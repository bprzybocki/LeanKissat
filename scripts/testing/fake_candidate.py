#!/usr/bin/env python3
"""Fake 'candidate' solver for testing difftest.py / the minimizer.

Runs the reference kissat with the given arguments and then corrupts the
result when the input CNF has a certain property (so that delta debugging
has something to preserve).  Mode is selected with FAKE_MODE (env) or the
first argument '--fake=MODE':

  flip     if the CNF contains both literals 3 and -3 in clauses of length
           >= 3 and the answer is UNSAT, claim SAT (bogus witness), and
           if SAT claim UNSAT -> status-mismatch
  model    on SAT answers, flip the value of variable 1 in the witness when
           some clause contains literal 1 -> bad-witness (usually)
  stats    add 1 to the 'conflicts' counter when there are >= 20 clauses
           -> stats-mismatch
  crash    exit with code 134 (like an abort) when some clause has >= 5
           literals -> crash
  hang     sleep forever when the CNF has an odd number of clauses
           -> timeout
  none     pass through unchanged
"""
import os
import subprocess
import sys
import time

REF = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "..", "..", "..", "kissat", "build", "kissat"))


def read_clauses(path):
    cls, cur = [], []
    with open(path) as fh:
        for line in fh:
            if line[:1] in ("c", "p"):
                continue
            for t in line.split():
                v = int(t)
                if v == 0:
                    cls.append(cur)
                    cur = []
                else:
                    cur.append(v)
    return cls


def main():
    args = sys.argv[1:]
    mode = os.environ.get("FAKE_MODE", "none")
    if args and args[0].startswith("--fake="):
        mode = args.pop(0).split("=", 1)[1]
    cnf = next((a for a in reversed(args) if not a.startswith("-")), None)
    cls = read_clauses(cnf) if cnf else []
    p = subprocess.run([REF] + args, stdout=subprocess.PIPE)
    out = p.stdout.decode()
    rc = p.returncode
    if mode == "flip":
        long_lits = {l for c in cls if len(c) >= 3 for l in c}
        if 3 in long_lits and -3 in long_lits:
            if rc == 20:
                out = out.replace("s UNSATISFIABLE", "s SATISFIABLE\nv 1 0")
                rc = 10
            elif rc == 10:
                lines = [l for l in out.splitlines() if not l.startswith("v")]
                out = "\n".join(lines).replace("s SATISFIABLE", "s UNSATISFIABLE") + "\n"
                rc = 20
    elif mode == "model":
        if rc == 10 and any(1 in c for c in cls):
            res = []
            for line in out.splitlines():
                if line.startswith("v "):
                    toks = ["-1" if t == "1" else ("1" if t == "-1" else t)
                            for t in line.split()[1:]]
                    line = "v " + " ".join(toks)
                res.append(line)
            out = "\n".join(res) + "\n"
    elif mode == "stats":
        if len(cls) >= 20:
            res = []
            for line in out.splitlines():
                if line.startswith("c conflicts:"):
                    parts = line.split()
                    line = line.replace(parts[2], str(int(parts[2]) + 1), 1)
                res.append(line)
            out = "\n".join(res) + "\n"
    elif mode == "crash":
        if any(len(c) >= 5 for c in cls):
            sys.stdout.write(out[: len(out) // 3])
            sys.stdout.flush()
            os._exit(134)
    elif mode == "hang":
        if len(cls) % 2 == 1:
            time.sleep(10 ** 6)
    sys.stdout.write(out)
    return rc


if __name__ == "__main__":
    sys.exit(main())
