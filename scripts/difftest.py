#!/usr/bin/env python3
"""Differential tester: reference kissat vs. a candidate solver.

For each (CNF, option set) pair both solvers are run with the same options
(plus '--statistics'), and the following are checked:

  * no crash / timeout (exit code must be 0, 10 or 20),
  * exit codes and 's' lines agree (and are consistent with each other),
  * SAT witnesses ('v' lines) satisfy the CNF (own checker),
  * statistics counters agree (the trajectory must be identical).

Failures are saved (CNF + both outputs + info.json) to the failures
directory and can optionally be delta-debugged ('--minimize').

Examples:
  python3 -I difftest.py --count 200 --family mix --jobs 8
  python3 -I difftest.py --candidate ../.lake/build/bin/leankissat \\
          --opts '' --opts '--plain' --count 100
  python3 -I difftest.py --files ../../kissat/test/cnf/*.cnf --opts '--sat'
"""

import argparse
import concurrent.futures as cf
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cnfgen  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_REFERENCE = os.path.normpath(os.path.join(
    HERE, "..", "..", "kissat", "build", "kissat"))
DEFAULT_FAILURES = os.path.normpath(os.path.join(HERE, "..", "test", "failures"))
DEFAULT_COUNTERS = ["conflicts", "decisions", "propagations", "restarts",
                    "reductions"]
# never compared (time / memory dependent)
EXCLUDE_RE = re.compile(r"time|second|resident|memory|MB|bytes", re.I)

# ------------------------------------------------------------------ parsing

STAT_RE = re.compile(r"^c ([A-Za-z_][A-Za-z0-9_\-]*):\s+(-?\d+(?:\.\d+)?)")
GLUE_RE = re.compile(r"^c (focused|stable) glue (\d+) used (\d+) clauses")
SECTION_RE = re.compile(r"^c -+ \[ (.*) \] -+")
# report line: 'c <char> seconds MB level reductions restarts ...'
REPORT_RE = re.compile(r"^c (.) +\d+\.\d+ +\d+ ((?:-?\d+(?:\.\d+)?%? *)+)$")


def read_cnf(path):
    """Return (nvars, nclauses_header, clauses).  Handles .gz/.xz/.bz2."""
    data = open_maybe_compressed(path).read()
    if isinstance(data, bytes):
        data = data.decode("ascii", "replace")
    nvars = ncls = None
    clauses = []
    cur = []
    for line in data.splitlines():
        s = line.strip()
        if not s or s[0] == "c" or s[0] == "%":
            continue
        if s[0] == "p":
            parts = s.split()
            nvars, ncls = int(parts[2]), int(parts[3])
            continue
        for tok in s.split():
            lit = int(tok)
            if lit == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(lit)
    if cur:
        clauses.append(cur)
    if nvars is None:
        nvars = max((abs(l) for c in clauses for l in c), default=0)
        ncls = len(clauses)
    return nvars, ncls, clauses


def open_maybe_compressed(path):
    if path.endswith(".gz"):
        import gzip
        return gzip.open(path, "rb")
    if path.endswith(".xz") or path.endswith(".lzma"):
        import lzma
        return lzma.open(path, "rb")
    if path.endswith(".bz2"):
        import bz2
        return bz2.open(path, "rb")
    return open(path, "r")


def write_cnf(path, nvars, clauses, comments=()):
    with open(path, "w") as fh:
        for c in comments:
            fh.write("c %s\n" % c)
        fh.write("p cnf %d %d\n" % (nvars, len(clauses)))
        for c in clauses:
            fh.write(" ".join(map(str, c)) + (" 0\n" if c else "0\n"))


def parse_output(text):
    """Parse solver stdout.  Returns dict with status, witness (list or None),
    witness_ok_format, stats (name -> number), report (list of tuples)."""
    status = None
    status_lines = 0
    vlits = []
    saw_v = False
    v_terminated = False
    stats = {}
    report = []
    section = None
    for line in text.splitlines():
        if line.startswith("s "):
            status_lines += 1
            status = line[2:].strip()
            continue
        if line.startswith("v"):
            saw_v = True
            for tok in line[1:].split():
                try:
                    lit = int(tok)
                except ValueError:
                    v_terminated = False
                    vlits.append(None)
                    continue
                if lit == 0:
                    v_terminated = True
                else:
                    if v_terminated:
                        v_terminated = False  # literals after the 0
                    vlits.append(lit)
            continue
        if not line.startswith("c"):
            continue
        m = SECTION_RE.match(line)
        if m:
            section = m.group(1)
            continue
        if section == "statistics":
            m = STAT_RE.match(line)
            if m:
                name, val = m.group(1), m.group(2)
                stats[name] = float(val) if "." in val else int(val)
        elif section == "glue usage":
            m = GLUE_RE.match(line)
            if m:
                stats["glue_%s_%s" % (m.group(1), m.group(2))] = int(m.group(3))
        elif section == "solving":
            m = REPORT_RE.match(line)
            if m:
                report.append((m.group(1),) + tuple(m.group(2).split()))
    return {
        "status": status,
        "status_lines": status_lines,
        "witness": vlits if saw_v else None,
        "witness_terminated": v_terminated,
        "stats": stats,
        "report": report,
    }


def check_witness(nvars, clauses, lits):
    """Return None if 'lits' satisfies all clauses, else an error message."""
    if lits is None:
        return "no witness ('v' lines) printed"
    val = {}
    for l in lits:
        if l is None:
            return "non-numeric token in 'v' line"
        v = abs(l)
        if v > nvars:
            return "witness literal %d exceeds header variables %d" % (l, nvars)
        if val.get(v, l > 0) != (l > 0):
            return "witness assigns both %d and %d" % (v, -v)
        val[v] = l > 0
    for i, c in enumerate(clauses):
        if not any(val.get(abs(l)) == (l > 0) for l in c):
            return "clause %d (%s) not satisfied" % (i + 1, " ".join(map(str, c)) or "empty")
    return None


# ------------------------------------------------------------------ running

STATUS_EXIT = {"SATISFIABLE": 10, "UNSATISFIABLE": 20, "UNKNOWN": 0}


def run_solver(cmd, opts, cnf, timeout):
    argv = list(cmd) + list(opts) + [cnf]
    t0 = time.time()
    try:
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             start_new_session=True)
    except OSError as e:
        return {"argv": argv, "rc": None, "stdout": "", "stderr": str(e),
                "timeout": False, "time": 0.0, "error": str(e)}
    try:
        out, err = p.communicate(timeout=timeout)
        to = False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except OSError:
            p.kill()
        out, err = p.communicate()
        to = True
    return {"argv": argv, "rc": p.returncode, "stdout": out.decode("utf-8", "replace"),
            "stderr": err.decode("utf-8", "replace"), "timeout": to,
            "time": time.time() - t0, "error": None}


def side_problem(res, parsed, cnfdata, check_model):
    """Classify a single solver run.  Returns (kind, message) or None."""
    if res["error"]:
        return ("crash", "could not execute: %s" % res["error"])
    if res["timeout"]:
        return ("timeout", "timeout after %.1fs" % res["time"])
    rc = res["rc"]
    if rc not in (0, 10, 20):
        return ("crash", "exit code %s%s" % (rc, " (signal %d)" % -rc if rc < 0 else ""))
    st = parsed["status"]
    if parsed["status_lines"] > 1:
        return ("bad-output", "%d 's' lines" % parsed["status_lines"])
    if st is not None and st not in STATUS_EXIT:
        return ("bad-output", "unknown status line 's %s'" % st)
    if st is None and rc != 0:
        return ("bad-output", "exit code %d but no 's' line" % rc)
    if st is not None and STATUS_EXIT[st] != rc:
        return ("bad-output", "exit code %d inconsistent with 's %s'" % (rc, st))
    if st == "SATISFIABLE" and check_model:
        if parsed["witness"] is not None and not parsed["witness_terminated"]:
            return ("bad-witness", "witness not terminated by 'v 0'")
        msg = check_witness(cnfdata[0], cnfdata[2], parsed["witness"])
        if msg:
            return ("bad-witness", msg)
    return None


def compare_stats(rs, cs, counters, all_counters, ignore):
    """Return list of (name, ref, cand) mismatches (sorted: requested
    counters first in given order, then alphabetical)."""
    mism = []
    seen = set()
    for name in counters:
        seen.add(name)
        if name in ignore:
            continue
        a, b = rs.get(name), cs.get(name)
        if a != b:
            mism.append((name, a, b))
    if all_counters:
        for name in sorted(set(rs) & set(cs)):
            if name in seen or name in ignore or EXCLUDE_RE.search(name):
                continue
            if rs[name] != cs[name]:
                mism.append((name, rs[name], cs[name]))
    return mism


class Config:
    pass


def check_pair(cfg, cnf_path, opts, cnfdata=None, parallel=False):
    """Run both solvers.  Returns result dict with 'kind' (None if OK)."""
    if cnfdata is None:
        cnfdata = read_cnf(cnf_path)
    full = list(opts) + (["--statistics"] if cfg.stats else [])
    if parallel:
        with cf.ThreadPoolExecutor(2) as ex:
            fr = ex.submit(run_solver, cfg.reference, full, cnf_path, cfg.timeout)
            fc = ex.submit(run_solver, cfg.candidate, full, cnf_path, cfg.timeout)
            rr, cr = fr.result(), fc.result()
    else:
        rr = run_solver(cfg.reference, full, cnf_path, cfg.timeout)
        cr = run_solver(cfg.candidate, full, cnf_path, cfg.timeout)
    rp, cp = parse_output(rr["stdout"]), parse_output(cr["stdout"])
    res = {"ref": rr, "cand": cr, "ref_parsed": rp, "cand_parsed": cp,
           "kind": None, "msg": "", "mismatches": []}
    rprob = side_problem(rr, rp, cnfdata, cfg.check_model)
    cprob = side_problem(cr, cp, cnfdata, cfg.check_model)
    if rprob and rprob[0] == "timeout" and (not cprob or cprob[0] == "timeout"):
        res["kind"] = "skip"
        res["msg"] = "reference timed out"
        return res
    if (cprob and cprob[0] == "timeout" and not rprob
            and rr["time"] > cfg.timeout_slack * cfg.timeout):
        res["kind"] = "skip"
        res["msg"] = "candidate timed out, reference close to the limit (%.1fs)" % rr["time"]
        return res
    if cprob:
        res["kind"], res["msg"] = cprob
        if res["kind"] == "timeout":
            res["msg"] += " (reference %.2fs)" % rr["time"]
        return res
    if rprob:
        res["kind"], res["msg"] = "ref-" + rprob[0], rprob[1]
        return res
    if rr["rc"] != cr["rc"] or rp["status"] != cp["status"]:
        res["kind"] = "status-mismatch"
        res["msg"] = "reference %s (%s) vs candidate %s (%s)" % (
            rp["status"], rr["rc"], cp["status"], cr["rc"])
        return res
    if cfg.stats:
        rs, cs = rp["stats"], cp["stats"]
        if not rs and not cs:
            pass  # e.g. '-q' in options: nothing to compare
        else:
            mism = compare_stats(rs, cs, cfg.counters, cfg.all_counters, cfg.ignore)
            if mism:
                res["kind"] = "stats-mismatch"
                res["mismatches"] = mism
                res["msg"] = ", ".join("%s: %s vs %s" % m for m in mism[:cfg.show])
                if len(mism) > cfg.show:
                    res["msg"] += " (+%d more)" % (len(mism) - cfg.show)
                return res
    if cfg.compare_report and rp["report"] != cp["report"]:
        n = next((i for i, (a, b) in enumerate(zip(rp["report"], cp["report"]))
                  if a != b), min(len(rp["report"]), len(cp["report"])))
        res["kind"] = "report-mismatch"
        res["msg"] = "report line %d differs: %s vs %s" % (
            n + 1,
            " ".join(rp["report"][n]) if n < len(rp["report"]) else "<none>",
            " ".join(cp["report"][n]) if n < len(cp["report"]) else "<none>")
    return res


# ------------------------------------------------------------------ minimizer

def minimize(cfg, cnfdata, opts, kind, workdir, log):
    """Delta-debug: remove clauses (ddmin-style chunks), then literals,
    then compact variable indices, preserving the failure kind."""
    nvars, _, clauses = cnfdata
    clauses = [list(c) for c in clauses]
    path = os.path.join(workdir, "probe.cnf")
    runs = [0]
    deadline = time.time() + cfg.minimize_time

    def fails(nv, cls):
        if runs[0] >= cfg.minimize_runs or time.time() > deadline:
            return False
        runs[0] += 1
        write_cnf(path, nv, cls)
        r = check_pair(cfg, path, opts, (nv, len(cls), cls), parallel=True)
        return r["kind"] == kind

    # 1. clause removal
    n = 2
    while len(clauses) >= 1:
        chunk = max(1, len(clauses) // n)
        removed = False
        i = 0
        while i < len(clauses):
            cand = clauses[:i] + clauses[i + chunk:]
            if fails(nvars, cand):
                clauses = cand
                removed = True
            else:
                i += chunk
        if chunk == 1 and not removed:
            break
        if not removed:
            n = min(n * 2, len(clauses))
        if runs[0] >= cfg.minimize_runs or time.time() > deadline:
            break
    log("  clauses after removal: %d (%d runs)" % (len(clauses), runs[0]))
    # 2. literal removal
    changed = True
    while changed and runs[0] < cfg.minimize_runs and time.time() < deadline:
        changed = False
        for ci in range(len(clauses)):
            j = 0
            while j < len(clauses[ci]):
                c = clauses[ci]
                cand = clauses[:ci] + [c[:j] + c[j + 1:]] + clauses[ci + 1:]
                if fails(nvars, cand):
                    clauses = cand
                    changed = True
                else:
                    j += 1
    # 3. compact variable indices (changes the instance, so check again)
    used = sorted({abs(l) for c in clauses for l in c})
    if used and (len(used) < nvars):
        m = {v: i + 1 for i, v in enumerate(used)}
        cand = [[m[abs(l)] * (1 if l > 0 else -1) for l in c] for c in clauses]
        if fails(len(used), cand):
            nvars, clauses = len(used), cand
    log("  minimized to %d vars, %d clauses, %d literals (%d runs)" % (
        nvars, len(clauses), sum(map(len, clauses)), runs[0]))
    return nvars, clauses


# ------------------------------------------------------------------ driver

def save_failure(cfg, job, res, cnf_text_path):
    tag = "%s-%s" % (job["name"], res["kind"])
    tag = re.sub(r"[^A-Za-z0-9_.=+-]", "_", tag)
    d = os.path.join(cfg.failures, tag)
    os.makedirs(d, exist_ok=True)
    shutil.copyfile(cnf_text_path, os.path.join(d, "input.cnf"))
    for side in ("ref", "cand"):
        with open(os.path.join(d, side + ".out"), "w") as fh:
            fh.write(res[side]["stdout"])
            if res[side]["stderr"]:
                fh.write("\n### stderr\n" + res[side]["stderr"])
    info = {
        "kind": res["kind"], "message": res["msg"],
        "mismatches": res["mismatches"],
        "options": job["opts"], "source": job["source"],
        "reference_argv": res["ref"]["argv"], "candidate_argv": res["cand"]["argv"],
        "ref_rc": res["ref"]["rc"], "cand_rc": res["cand"]["rc"],
        "ref_time": round(res["ref"]["time"], 3),
        "cand_time": round(res["cand"]["time"], 3),
    }
    with open(os.path.join(d, "info.json"), "w") as fh:
        json.dump(info, fh, indent=2)
    return d


def build_jobs(a, optsets):
    jobs = []
    if a.files:
        files = []
        for f in a.files:
            if os.path.isdir(f):
                files += sorted(os.path.join(f, x) for x in os.listdir(f)
                                if re.search(r"\.(cnf|dimacs)(\.(gz|xz|bz2))?$", x))
            else:
                files.append(f)
        for f in files:
            for oi, o in enumerate(optsets):
                jobs.append({"source": os.path.abspath(f), "file": os.path.abspath(f),
                             "name": "%s-o%d" % (os.path.basename(f), oi), "opts": o})
        return jobs
    fams = a.family.split(",")
    lo, hi = parse_range(a.size)
    for i in range(a.count):
        seed = a.seed + i
        fam = fams[i % len(fams)]
        rfam = cnfgen.resolve_family(fam, seed)
        size = lo + (seed * 7919) % (hi - lo + 1)
        for oi, o in enumerate(optsets):
            jobs.append({"source": "cnfgen %s --seed %d --size %d" % (rfam, seed, size),
                         "gen": (rfam, seed, size), "file": None,
                         "name": "%s-s%d-z%d-o%d" % (rfam, seed, size, oi), "opts": o})
    return jobs


def parse_range(s):
    if "-" in str(s):
        a, b = str(s).split("-", 1)
        return int(a), int(b)
    return int(s), int(s)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--reference", default=DEFAULT_REFERENCE,
                    help="reference solver command (shell-split) [%(default)s]")
    ap.add_argument("--candidate", default=None,
                    help="candidate solver command (shell-split; default: reference)")
    ap.add_argument("--opts", action="append", default=None,
                    help="option set applied to both solvers (repeatable; each "
                         "instance is run once per option set), e.g. --opts='--plain'")
    ap.add_argument("--files", nargs="+", help="CNF files or directories to test")
    ap.add_argument("--count", type=int, default=50, help="number of random instances")
    ap.add_argument("--seed", type=int, default=1, help="first seed")
    ap.add_argument("--family", default="mix",
                    help="cnfgen family, comma list (round-robin) or 'mix' [mix]")
    ap.add_argument("--size", default="1-6", help="size or range lo-hi [1-6]")
    ap.add_argument("--jobs", "-j", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--timeout", type=float, default=20.0, help="per run [20s]")
    ap.add_argument("--timeout-slack", type=float, default=0.5,
                    help="a candidate timeout is only a failure if the reference "
                         "needed less than this fraction of --timeout [0.5]")
    ap.add_argument("--counters", default=",".join(DEFAULT_COUNTERS),
                    help="always compared counters (must exist in both) [%(default)s]")
    ap.add_argument("--only-listed", action="store_true",
                    help="compare only --counters, not every common counter")
    ap.add_argument("--ignore", default="", help="comma list of counters to ignore")
    ap.add_argument("--no-stats", action="store_true",
                    help="do not add --statistics / compare counters")
    ap.add_argument("--compare-report", action="store_true",
                    help="also compare the progress report lines (minus time/MB)")
    ap.add_argument("--no-model-check", action="store_true")
    ap.add_argument("--failures", default=DEFAULT_FAILURES, help="[%(default)s]")
    ap.add_argument("--no-save", action="store_true", help="do not save failures")
    ap.add_argument("--minimize", action="store_true", help="delta-debug failures")
    ap.add_argument("--minimize-runs", type=int, default=3000)
    ap.add_argument("--minimize-time", type=float, default=300.0, help="seconds per failure")
    ap.add_argument("--max-failures", type=int, default=0,
                    help="stop scheduling after this many failures (0 = never)")
    ap.add_argument("--show", type=int, default=5, help="mismatching counters to print")
    ap.add_argument("-v", "--verbose", action="store_true", help="print every result")
    a = ap.parse_args(argv)

    cfg = Config()
    cfg.reference = shlex.split(a.reference)
    cfg.candidate = shlex.split(a.candidate) if a.candidate else list(cfg.reference)
    cfg.timeout = a.timeout
    cfg.timeout_slack = a.timeout_slack
    cfg.stats = not a.no_stats
    cfg.counters = [c for c in a.counters.split(",") if c]
    cfg.all_counters = not a.only_listed
    cfg.ignore = set(c for c in a.ignore.split(",") if c)
    cfg.compare_report = a.compare_report
    cfg.check_model = not a.no_model_check
    cfg.failures = a.failures
    cfg.minimize_runs = a.minimize_runs
    cfg.minimize_time = a.minimize_time
    cfg.show = a.show
    optsets = [shlex.split(o) for o in (a.opts if a.opts else [""])]

    for c in (cfg.reference, cfg.candidate):
        if not shutil.which(c[0]) and not os.access(c[0], os.X_OK):
            ap.error("solver '%s' not found / not executable" % c[0])

    jobs = build_jobs(a, optsets)
    tmp = tempfile.mkdtemp(prefix="difftest-")
    lock = threading.Lock()
    counts = {}
    failures = []
    stop = threading.Event()
    t0 = time.time()
    done = [0]

    def log(msg):
        with lock:
            print(msg, flush=True)

    def work(job, idx):
        if stop.is_set():
            return None
        if job["file"]:
            path = job["file"]
        else:
            fam, seed, size = job["gen"]
            path = os.path.join(tmp, "%d.cnf" % idx)
            with open(path, "w") as fh:
                fh.write(cnfgen.generate(fam, seed, size).dimacs())
        cnfdata = read_cnf(path)
        res = check_pair(cfg, path, job["opts"], cnfdata)
        kind = res["kind"] or "ok"
        with lock:
            counts[kind] = counts.get(kind, 0) + 1
            done[0] += 1
            n = done[0]
        optstr = " ".join(job["opts"]) or "<default>"
        if res["kind"] and res["kind"] != "skip":
            log("FAIL [%d/%d] %s opts=%s: %s: %s" % (n, len(jobs), job["source"],
                                                    optstr, res["kind"], res["msg"]))
            d = None
            if not a.no_save:
                d = save_failure(cfg, job, res, path)
                log("     saved to %s" % d)
            with lock:
                failures.append((job, res, d))
                if a.max_failures and len(failures) >= a.max_failures:
                    stop.set()
            if a.minimize:
                wd = tempfile.mkdtemp(prefix="ddmin-", dir=tmp)
                nv, cls = minimize(cfg, cnfdata, job["opts"], res["kind"], wd, log)
                if d:
                    write_cnf(os.path.join(d, "minimized.cnf"), nv, cls,
                              ["minimized from %s opts: %s kind: %s" % (
                                  job["source"], optstr, res["kind"])])
                    log("     minimized CNF: %s" % os.path.join(d, "minimized.cnf"))
        elif a.verbose:
            log("%s [%d/%d] %s opts=%s %s %.2fs/%.2fs %s" % (
                "SKIP" if res["kind"] else "ok  ", n, len(jobs), job["source"], optstr,
                res["ref_parsed"]["status"], res["ref"]["time"], res["cand"]["time"],
                "conflicts=%s" % res["ref_parsed"]["stats"].get("conflicts", "?")))
        if not job["file"]:
            try:
                os.unlink(path)
            except OSError:
                pass
        return res

    try:
        with cf.ThreadPoolExecutor(max(1, a.jobs)) as ex:
            futs = [ex.submit(work, j, i) for i, j in enumerate(jobs)]
            for f in cf.as_completed(futs):
                f.result()
    except KeyboardInterrupt:
        stop.set()
        print("interrupted", file=sys.stderr)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print("=" * 72)
    print("difftest: %d runs (%d instances x %d option sets) in %.1fs" % (
        done[0], len(jobs) // max(1, len(optsets)), len(optsets), time.time() - t0))
    print("reference: %s" % " ".join(cfg.reference))
    print("candidate: %s" % " ".join(cfg.candidate))
    print("results:   " + ", ".join("%s=%d" % kv for kv in sorted(counts.items())))
    nfail = len(failures)
    print("FAILURES:  %d" % nfail)
    for job, res, d in failures[:20]:
        print("  %-16s %s [%s]%s" % (res["kind"], job["source"],
                                     " ".join(job["opts"]) or "<default>",
                                     ("  -> " + d) if d else ""))
    if nfail > 20:
        print("  ... %d more" % (nfail - 20))
    return 1 if nfail else 0


if __name__ == "__main__":
    sys.exit(main())
