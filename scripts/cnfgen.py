#!/usr/bin/env python3
"""Deterministic random CNF generators (DIMACS on stdout).

Usage:
  python3 -I cnfgen.py FAMILY [--seed S] [--size Z] [family params ...]
  python3 -I cnfgen.py --list

Every family is a function  gen_<family>(rng, size, **params) -> Formula.
The same (family, seed, size, params) always yields the same bytes
(independent of PYTHONHASHSEED and platform).

'size' is a coarse knob (default 3, typical range 1..10); the defaults of
all families are tuned so that size <= 5 is solved by kissat in well under
a second.  Explicit parameters (e.g. --vars) override what size implies.

Also usable as a module:  import cnfgen; f = cnfgen.generate(family, seed,
size); text = f.dimacs().
"""

import argparse
import itertools
import random
import sys


class Formula:
    def __init__(self, nvars=0):
        self.nvars = nvars
        self.clauses = []
        self.comments = []

    def new_var(self):
        self.nvars += 1
        return self.nvars

    def new_vars(self, n):
        return [self.new_var() for _ in range(n)]

    def add(self, clause):
        clause = list(clause)
        for lit in clause:
            assert lit != 0
            if abs(lit) > self.nvars:
                self.nvars = abs(lit)
        self.clauses.append(clause)

    def extend(self, clauses):
        for c in clauses:
            self.add(c)

    def dimacs(self, extra_vars=0):
        out = []
        for c in self.comments:
            out.append("c " + c)
        out.append("p cnf %d %d" % (self.nvars + extra_vars, len(self.clauses)))
        for c in self.clauses:
            out.append(" ".join(map(str, c)) + (" 0" if c else "0"))
        return "\n".join(out) + "\n"


# ---------------------------------------------------------------- helpers

def sign(rng, v):
    return v if rng.random() < 0.5 else -v


def rand_clause(rng, vars_, k):
    k = min(k, len(vars_))
    return [sign(rng, v) for v in rng.sample(vars_, k)]


def tseitin_and(f, out, ins):
    # out <-> AND(ins)
    for i in ins:
        f.add([-out, i])
    f.add([out] + [-i for i in ins])


def tseitin_or(f, out, ins):
    tseitin_and(f, -out, [-i for i in ins])


def tseitin_xor2(f, out, a, b):
    f.add([-out, a, b])
    f.add([-out, -a, -b])
    f.add([out, -a, b])
    f.add([out, a, -b])


def tseitin_ite(f, out, c, t, e):
    f.add([-out, -c, t])
    f.add([-out, c, e])
    f.add([out, -c, -t])
    f.add([out, c, -e])


def xor_direct(f, lits, parity):
    """Direct encoding of XOR(lits) = parity (2^(n-1) clauses)."""
    n = len(lits)
    for bits in itertools.product((0, 1), repeat=n):
        # forbid assignments with wrong parity: assignment bits[i]=1 means lit true
        if sum(bits) % 2 != parity:
            f.add([-l if b else l for l, b in zip(lits, bits)])


def xor_chain(f, rng, lits, parity, cut=3):
    """Encode XOR(lits) = parity by cutting into pieces of size 'cut' with
    fresh auxiliary variables."""
    lits = list(lits)
    while len(lits) > cut:
        piece = lits[:cut - 1]
        rest = lits[cut - 1:]
        aux = f.new_var()
        # aux = XOR(piece)  <=>  XOR(piece + [aux]) = 0
        xor_direct(f, piece + [aux], 0)
        lits = rest + [aux]
    if not lits:
        if parity:
            f.add([])
        return
    xor_direct(f, lits, parity)


def shuffle_formula(rng, f, rename=True, flip=True):
    """Randomly permute clauses/literals and optionally rename/flip vars."""
    perm = list(range(1, f.nvars + 1))
    if rename:
        rng.shuffle(perm)
    flips = [False] + [flip and rng.random() < 0.5 for _ in range(f.nvars)]
    m = {}
    for v in range(1, f.nvars + 1):
        nv = perm[v - 1]
        m[v] = -nv if flips[v] else nv
    newc = []
    for c in f.clauses:
        nc = [m[abs(l)] if l > 0 else -m[abs(l)] for l in c]
        rng.shuffle(nc)
        newc.append(nc)
    rng.shuffle(newc)
    f.clauses = newc
    return f


# ---------------------------------------------------------------- families

def gen_ksat(rng, size, vars=None, clauses=None, ratio=None, k=3,
             kmin=None, kmax=None):
    """Uniform random k-SAT.  'kmin'/'kmax' give mixed clause lengths."""
    n = vars or 20 + 15 * size
    k = int(k)
    if clauses is None:
        if ratio is None:
            # roughly near threshold for given k
            ratio = {2: 1.0, 3: 4.26, 4: 9.93, 5: 21.1, 6: 43.4, 7: 87.8}.get(k, 4.26)
            ratio *= rng.uniform(0.85, 1.15)
        clauses = int(round(float(ratio) * n))
    f = Formula(n)
    lo = int(kmin) if kmin is not None else k
    hi = int(kmax) if kmax is not None else k
    vs = list(range(1, n + 1))
    for _ in range(int(clauses)):
        f.add(rand_clause(rng, vs, rng.randint(lo, hi)))
    f.comments.append("ksat n=%d m=%d k=%d..%d" % (n, int(clauses), lo, hi))
    return f


def gen_threshold3(rng, size, vars=None):
    """Random 3-SAT at ratio 4.26 +- small jitter (hard-ish, ~50% SAT)."""
    n = vars or 30 + 20 * size
    return gen_ksat(rng, size, vars=n, ratio=4.26 + rng.uniform(-0.1, 0.1), k=3)


def gen_mixedsat(rng, size, vars=None):
    """Random formula with clause lengths 2..7 at a ratio near threshold."""
    n = vars or 30 + 20 * size
    f = Formula(n)
    vs = list(range(1, n + 1))
    # thresholds weights: each length contributes 2^-k per clause approx
    budget = rng.uniform(0.65, 0.95) * n  # sum of 2^-k * m_k * ~ln2 scale
    m = 0
    while budget > 0:
        k = rng.choice((2, 3, 3, 3, 4, 4, 5, 6, 7))
        f.add(rand_clause(rng, vs, k))
        budget -= 2.0 ** -k * 1.5
        m += 1
    f.comments.append("mixedsat n=%d m=%d" % (n, m))
    return f


def gen_php(rng, size, holes=None, sat=None):
    """Pigeonhole: holes+1 pigeons into holes (UNSAT) or holes pigeons (SAT)."""
    h = holes or min(2 + size // 2, 7)
    if sat is None:
        sat = rng.random() < 0.3
    p = h if sat else h + 1
    f = Formula()
    x = [[f.new_var() for _ in range(h)] for _ in range(p)]
    for i in range(p):
        f.add(x[i])
    for j in range(h):
        for a in range(p):
            for b in range(a + 1, p):
                f.add([-x[a][j], -x[b][j]])
    f.comments.append("php pigeons=%d holes=%d" % (p, h))
    return shuffle_formula(rng, f) if rng.random() < 0.5 else f


def gen_parity(rng, size, vars=None, constraints=None, width=None):
    """Random XOR constraints (Tseitin-chained), SAT or UNSAT by parity."""
    n = vars or 6 + 4 * size
    m = constraints or max(2, int(n * rng.uniform(0.85, 1.1)))
    w = width or 3
    f = Formula(n)
    vs = list(range(1, n + 1))
    for _ in range(m):
        ww = max(2, min(n, w + rng.randint(0, 3)))
        lits = [sign(rng, v) for v in rng.sample(vs, ww)]
        xor_chain(f, rng, lits, rng.randint(0, 1), cut=rng.choice((3, 4)))
    f.comments.append("parity n=%d m=%d" % (n, m))
    return f


def gen_xorchain(rng, size, length=None):
    """Two different chained encodings of the XOR of the same variables with
    (usually) contradicting parity: classic UNSAT for equivalence reasoning."""
    n = length or min(6 + 3 * size, 27)
    f = Formula(n)
    vs = list(range(1, n + 1))
    p1 = rng.randint(0, 1)
    p2 = p1 ^ (1 if rng.random() < 0.8 else 0)
    a = vs[:]
    b = vs[:]
    rng.shuffle(b)
    xor_chain(f, rng, a, p1, cut=3)
    xor_chain(f, rng, b, p2, cut=rng.choice((3, 4)))
    f.comments.append("xorchain n=%d parities=%d,%d" % (n, p1, p2))
    return f


def alt_and(f, out, ins):
    # out <-> AND(ins) as a chain of binary ANDs (structurally different)
    acc = ins[0]
    for i in ins[1:-1]:
        t = f.new_var()
        tseitin_and(f, t, [acc, i])
        acc = t
    tseitin_and(f, out, [acc, ins[-1]])


def alt_xor2(f, out, a, b):
    # out <-> (a & -b) | (-a & b)
    t1, t2 = f.new_var(), f.new_var()
    tseitin_and(f, t1, [a, -b])
    tseitin_and(f, t2, [-a, b])
    tseitin_or(f, out, [t1, t2])


def alt_ite(f, out, c, t, e):
    # out <-> (c & t) | (-c & e)
    t1, t2 = f.new_var(), f.new_var()
    tseitin_and(f, t1, [c, t])
    tseitin_and(f, t2, [-c, e])
    tseitin_or(f, out, [t1, t2])


def build_circuit(f, rng, inputs, ngates, kinds, alt=False):
    nodes = list(inputs)
    gates = []
    for _ in range(ngates):
        kind = rng.choice(kinds)
        out = f.new_var()
        recent = nodes[-max(4, len(nodes) // 2):]
        pool = recent if rng.random() < 0.6 else nodes

        def pick():
            return sign(rng, rng.choice(pool))
        if kind == "and":
            ar = rng.randint(2, 3)
            ins = [pick() for _ in range(ar)]
            if len({abs(i) for i in ins}) < ar:
                ins = [sign(rng, v) for v in rng.sample(nodes, min(ar, len(nodes)))]
            (alt_and if alt else tseitin_and)(f, out, ins)
        elif kind == "or":
            ins = [sign(rng, v) for v in rng.sample(nodes, min(2, len(nodes)))]
            tseitin_or(f, out, ins)
        elif kind == "xor":
            a, b = rng.sample(nodes, 2)
            (alt_xor2 if alt else tseitin_xor2)(f, out, sign(rng, a), sign(rng, b))
        else:  # ite
            c, t, e = rng.sample(nodes, 3)
            (alt_ite if alt else tseitin_ite)(f, out, sign(rng, c), sign(rng, t), sign(rng, e))
        nodes.append(out)
        gates.append((kind, out))
    return nodes


def gen_circuit(rng, size, inputs=None, gates=None, outputs=None):
    """Random AND/OR/XOR/ITE circuit (Tseitin) with random output constraints."""
    ni = inputs or 6 + 2 * size
    ng = gates or 15 + 12 * size
    f = Formula()
    ins = f.new_vars(ni)
    kinds = rng.choice([("and",), ("and", "xor"), ("and", "ite"),
                        ("and", "or", "xor", "ite"), ("xor", "ite")])
    nodes = build_circuit(f, rng, ins, ng, kinds)
    no = outputs or rng.randint(2, 4 + 2 * size)
    for v in rng.sample(nodes[ni:], min(no, ng)):
        f.add([sign(rng, v)])
    # occasionally add a few random clauses over inputs
    for _ in range(rng.randint(0, 2 * ni)):
        f.add(rand_clause(rng, nodes, 3))
    f.comments.append("circuit inputs=%d gates=%d kinds=%s" % (ni, ng, ",".join(kinds)))
    return shuffle_formula(rng, f) if rng.random() < 0.3 else f


def gen_miter(rng, size, inputs=None, gates=None):
    """Miter of a circuit with a structurally modified copy (congruence /
    sweeping target).  Usually equivalent (UNSAT), sometimes mutated."""
    ni = inputs or 5 + size
    ng = gates or 10 + 8 * size
    f = Formula()
    ins = f.new_vars(ni)
    state = rng.getstate()
    kinds = ("and", "xor", "ite")
    n1 = build_circuit(f, rng, ins, ng, kinds)
    alt = rng.random() < 0.5  # structurally different but equivalent copy
    after = rng.getstate()
    rng.setstate(state)
    n2 = build_circuit(f, rng, ins, ng, kinds, alt=alt)  # same function, new vars
    rng.setstate(after)
    o1, o2 = n1[-1], n2[-1]
    if rng.random() < 0.25:
        # mutate: flip one random gate input in the copy by adding a fresh xor
        o2x = f.new_var()
        tseitin_xor2(f, o2x, o2, rng.choice(ins))
        o2 = o2x
    d = f.new_var()
    tseitin_xor2(f, d, o1, o2)
    f.add([d])
    f.comments.append("miter inputs=%d gates=%d alt=%d" % (ni, ng, alt))
    return shuffle_formula(rng, f) if rng.random() < 0.5 else f


def gen_coloring(rng, size, nodes=None, colors=None, density=None):
    """Random graph k-coloring (direct encoding, at-least/at-most-one)."""
    k = colors or rng.choice((3, 3, 4))
    n = nodes or 8 + 4 * size
    # average degree around threshold (~4.69 for k=3, ~8.4 for k=4)
    deg = density or {3: 4.6, 4: 8.4}.get(k, 4.6) * rng.uniform(0.8, 1.2)
    m = int(deg * n / 2)
    f = Formula()
    x = [[f.new_var() for _ in range(k)] for _ in range(n)]
    for i in range(n):
        f.add(x[i])
        if rng.random() < 0.7:
            for a in range(k):
                for b in range(a + 1, k):
                    f.add([-x[i][a], -x[i][b]])
    edges = set()
    tries = 0
    while len(edges) < m and tries < 50 * m:
        tries += 1
        a, b = rng.sample(range(n), 2)
        edges.add((min(a, b), max(a, b)))
    for a, b in sorted(edges):
        for c in range(k):
            f.add([-x[a][c], -x[b][c]])
    f.comments.append("coloring nodes=%d colors=%d edges=%d" % (n, k, len(edges)))
    return shuffle_formula(rng, f) if rng.random() < 0.5 else f


def gen_equiv(rng, size, vars=None):
    """Equivalence chains/cycles plus random 3-clauses (substitution target)."""
    n = vars or 30 + 15 * size
    f = Formula(n)
    vs = list(range(1, n + 1))
    nchains = rng.randint(1, 3 + size)
    for _ in range(nchains):
        ln = rng.randint(2, max(3, n // 4))
        ch = [sign(rng, v) for v in rng.sample(vs, ln)]
        for a, b in zip(ch, ch[1:]):
            f.add([-a, b])
            f.add([a, -b])
        if rng.random() < 0.3:  # close as cycle (redundant)
            f.add([-ch[-1], ch[0]])
        if rng.random() < 0.05:  # contradiction a = -a via chain
            f.add([ch[0], ch[-1]])
            f.add([-ch[0], -ch[-1]])
    # binary implications (one direction only)
    for _ in range(rng.randint(0, n // 6)):
        f.add(rand_clause(rng, vs, 2))
    m3 = int(n * rng.uniform(1.4, 3.0))
    for _ in range(m3):
        f.add(rand_clause(rng, vs, 3))
    f.comments.append("equiv n=%d chains=%d" % (n, nchains))
    return f


def gen_bin(rng, size, vars=None):
    """Mostly binary clauses (2-SAT near threshold) plus some ternary ones;
    exercises failed literals, transitive reduction, SCC substitution."""
    n = vars or 30 + 20 * size
    f = Formula(n)
    vs = list(range(1, n + 1))
    m2 = int(n * rng.uniform(0.4, 0.9))
    for _ in range(m2):
        f.add(rand_clause(rng, vs, 2))
    for _ in range(int(n * rng.uniform(1.8, 3.2))):
        f.add(rand_clause(rng, vs, 3))
    f.comments.append("bin n=%d" % n)
    return f


def gen_amo(rng, size, groups=None):
    """Random exactly-one groups (pairwise AMO, factorization target) plus
    random cross constraints."""
    g = groups or 4 + 2 * size
    f = Formula()
    grp = []
    for _ in range(g):
        w = rng.randint(3, 6 + size)
        vs = f.new_vars(w)
        grp.append(vs)
        f.add(vs)
        for a in range(w):
            for b in range(a + 1, w):
                f.add([-vs[a], -vs[b]])
    allv = list(range(1, f.nvars + 1))
    for _ in range(int(f.nvars * rng.uniform(0.7, 1.5))):
        a, b, c = rng.sample(grp, 3)
        f.add([sign(rng, rng.choice(a)), sign(rng, rng.choice(b)),
               sign(rng, rng.choice(c))])
    f.comments.append("amo groups=%d" % g)
    return f


def gen_weird(rng, size, vars=None):
    """Random formula with DIMACS oddities: duplicate literals, tautologies,
    duplicate clauses, units, (rare) empty clause, unused variables."""
    n = vars or 25 + 15 * size
    base = gen_ksat(rng, size, vars=n, ratio=rng.uniform(4.5, 8.5),
                    kmin=3, kmax=5)
    f = Formula(n)
    vs = list(range(1, n + 1))
    for c in base.clauses:
        r = rng.random()
        c = list(c)
        if r < 0.08:
            c.append(rng.choice(c))  # duplicate literal
        elif r < 0.13:
            c.append(-rng.choice(c))  # tautology
        f.add(c)
        if rng.random() < 0.04:
            f.add(list(reversed(c)))  # duplicate clause
    for _ in range(rng.randint(0, 3)):
        f.add([sign(rng, rng.choice(vs))])  # units (possibly contradicting)
    if rng.random() < 0.05:
        f.add([])  # empty clause
    if rng.random() < 0.1:
        v = rng.choice(vs)
        f.add([v, v, v])  # unit via duplicates
    rng.shuffle(f.clauses)
    extra = rng.randint(0, 2 * size + 3)  # variables that never occur
    f.nvars = n + extra
    f.comments.append("weird n=%d extra_unused=%d" % (n, extra))
    return f


def gen_cnfuzz(rng, size, layers=None):
    """Layered random instances in the spirit of Biere's 'cnfuzz'."""
    nl = layers or rng.randint(1, 4 + size)
    maxw = rng.randint(6, 12 + 6 * size)
    widths = [rng.randint(4, maxw) for _ in range(nl)]
    lows, highs = [], []
    nv = 0
    for w in widths:
        lows.append(nv + 1)
        nv += w
        highs.append(nv)
    f = Formula(nv)
    # cnfuzz ratio 300..450 percent per layer
    for i in range(nl):
        m = widths[i] * rng.randint(380, 560) // 100
        for _ in range(m):
            k = rng.choice((3, 3, 3, 4, 5))
            used = set()
            cl = []
            for _ in range(k):
                j = i
                if i + 1 < nl and rng.random() < 0.3:
                    j = i + 1
                elif i > 0 and rng.random() < 0.15:
                    j = i - 1
                for _t in range(10):
                    v = rng.randint(lows[j], highs[j])
                    if v not in used:
                        break
                if v in used:
                    continue
                used.add(v)
                cl.append(sign(rng, v))
            f.add(cl)
    rng.shuffle(f.clauses)
    f.comments.append("cnfuzz layers=%d widths=%s" % (nl, widths))
    return f


def gen_planted(rng, size, vars=None, k=3):
    """Random k-SAT with a planted solution (always SAT, above threshold)."""
    n = vars or 30 + 20 * size
    sol = [None] + [rng.random() < 0.5 for _ in range(n)]
    f = Formula(n)
    vs = list(range(1, n + 1))
    m = int(n * rng.uniform(4.0, 6.0))
    while len(f.clauses) < m:
        c = rand_clause(rng, vs, int(k))
        if any((l > 0) == sol[abs(l)] for l in c):
            f.add(c)
    f.comments.append("planted n=%d m=%d" % (n, m))
    return f


FAMILIES = {
    "ksat": gen_ksat,
    "threshold3": gen_threshold3,
    "mixedsat": gen_mixedsat,
    "php": gen_php,
    "parity": gen_parity,
    "xorchain": gen_xorchain,
    "circuit": gen_circuit,
    "miter": gen_miter,
    "coloring": gen_coloring,
    "equiv": gen_equiv,
    "bin": gen_bin,
    "amo": gen_amo,
    "weird": gen_weird,
    "cnfuzz": gen_cnfuzz,
    "planted": gen_planted,
}

# families drawn by 'mix' (weights)
MIX = [("ksat", 2), ("threshold3", 2), ("mixedsat", 1), ("php", 1),
       ("parity", 1), ("xorchain", 1), ("circuit", 2), ("miter", 1),
       ("coloring", 1), ("equiv", 1), ("bin", 1), ("amo", 1),
       ("weird", 2), ("cnfuzz", 2), ("planted", 1)]


def resolve_family(family, seed):
    """'mix' picks a family deterministically from the seed."""
    if family != "mix":
        return family
    rng = random.Random("mix:%s" % seed)
    names = [n for n, w in MIX for _ in range(w)]
    return rng.choice(names)


def generate(family, seed=0, size=3, **params):
    family = resolve_family(family, seed)
    if family not in FAMILIES:
        raise ValueError("unknown family '%s' (try --list)" % family)
    rng = random.Random("%s:%s:%s" % (family, seed, size))
    params = {k: v for k, v in params.items() if v is not None}
    f = FAMILIES[family](rng, int(size), **params)
    f.comments.insert(0, "cnfgen family=%s seed=%s size=%s%s" % (
        family, seed, size,
        "".join(" %s=%s" % kv for kv in sorted(params.items()))))
    f.family = family
    return f


def _num(s):
    try:
        return int(s)
    except ValueError:
        return float(s)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("family", nargs="?", help="family name or 'mix'")
    ap.add_argument("--list", action="store_true", help="list families")
    ap.add_argument("--seed", default="0")
    ap.add_argument("--size", type=int, default=3)
    ap.add_argument("-o", "--output", help="write to file instead of stdout")
    ap.add_argument("params", nargs="*", metavar="key=value",
                    help="family parameters, e.g. vars=50 ratio=4.0 k=4 "
                         "kmin=2 kmax=6 holes=5 colors=3 ...")
    a = ap.parse_args(argv)
    if a.list or not a.family:
        for name, fn in FAMILIES.items():
            print("%-11s %s" % (name, (fn.__doc__ or "").strip().splitlines()[0]))
        print("%-11s %s" % ("mix", "pick one of the above from the seed"))
        return 0
    params = {}
    for p in a.params:
        if "=" not in p:
            ap.error("parameter '%s' must be key=value" % p)
        k, v = p.split("=", 1)
        params[k.lstrip("-")] = _num(v)
    f = generate(a.family, a.seed, a.size, **params)
    text = f.dimacs()
    if a.output:
        with open(a.output, "w") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
