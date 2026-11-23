#!/usr/bin/env python3
"""Benchmark runner and CSV comparison.

Run a solver over a directory of CNF files (optionally compressed):
  python3 -I bench.py run --solver ../../kissat/build/kissat \\
        --dir ../../benchmarks/anni --timeout 300 --jobs 4 --out ref.csv

Compare two result files:
  python3 -I bench.py compare ref.csv lean.csv

CSV columns: file, status (SAT/UNSAT/UNKNOWN/TIMEOUT/CRASH/ERROR/WRONG),
exit, time (wall seconds), conflicts, decisions, propagations, timeout,
options.  'run --resume' skips files already present in the output CSV.
"""

import argparse
import concurrent.futures as cf
import csv
import math
import os
import re
import shlex
import signal
import subprocess
import sys
import threading
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest  # noqa: E402  (output parsing, witness checking)

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SOLVER = difftest.DEFAULT_REFERENCE
CNF_RE = re.compile(r"\.(cnf|dimacs)(\.(gz|xz|lzma|bz2))?$")
FIELDS = ["file", "status", "exit", "time", "conflicts", "decisions",
          "propagations", "timeout", "options"]
SOLVED = ("SAT", "UNSAT")


def list_files(dirs, files, pattern):
    out = []
    for d in dirs or []:
        for root, _, names in os.walk(d):
            for n in sorted(names):
                if CNF_RE.search(n) and (not pattern or re.search(pattern, n)):
                    out.append(os.path.join(root, n))
    out += files or []
    return sorted(set(os.path.abspath(f) for f in out))


def run_one(cmd, opts, path, timeout, check):
    argv = list(cmd) + list(opts) + ["--statistics"] + ([] if check else ["-n"]) + [path]
    t0 = time.time()
    try:
        p = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             start_new_session=True)
    except OSError as e:
        return {"status": "ERROR", "exit": "", "time": 0.0, "msg": str(e)}
    to = False
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        to = True
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except OSError:
            p.kill()
        out, err = p.communicate()
    wall = time.time() - t0
    text = out.decode("utf-8", "replace")
    parsed = difftest.parse_output(text)
    st = {"SATISFIABLE": "SAT", "UNSATISFIABLE": "UNSAT",
          "UNKNOWN": "UNKNOWN"}.get(parsed["status"], None)
    rc = p.returncode
    msg = ""
    if to:
        status = "TIMEOUT"
    elif rc not in (0, 10, 20):
        status = "CRASH"
        msg = (err.decode("utf-8", "replace").strip().splitlines() or [""])[-1]
    elif st is None:
        status = "UNKNOWN" if rc == 0 else "ERROR"
    elif {"SAT": 10, "UNSAT": 20, "UNKNOWN": 0}[st] != rc:
        status = "ERROR"
        msg = "exit code %d vs 's' line" % rc
    else:
        status = st
    if status == "SAT" and check:
        nv, _, cls = difftest.read_cnf(path)
        m = difftest.check_witness(nv, cls, parsed["witness"])
        if m:
            status, msg = "WRONG", m
    s = parsed["stats"]
    return {"status": status, "exit": rc, "time": wall, "msg": msg,
            "conflicts": s.get("conflicts", ""), "decisions": s.get("decisions", ""),
            "propagations": s.get("propagations", "")}


def cmd_run(a):
    cmd = shlex.split(a.solver)
    opts = shlex.split(a.options)
    files = list_files(a.dir, a.files, a.pattern)
    if not files:
        print("no CNF files found", file=sys.stderr)
        return 1
    done = set()
    if a.resume and os.path.exists(a.out):
        with open(a.out) as fh:
            done = {r["file"] for r in csv.DictReader(fh)}
    todo = [f for f in files if rel(f, a) not in done]
    mode = "a" if (a.resume and os.path.exists(a.out)) else "w"
    fh = open(a.out, mode, newline="")
    w = csv.DictWriter(fh, fieldnames=FIELDS)
    if mode == "w":
        w.writeheader()
    lock = threading.Lock()
    counter = [0]
    t0 = time.time()

    def work(f):
        r = run_one(cmd, opts, f, a.timeout, a.check)
        with lock:
            counter[0] += 1
            w.writerow({"file": rel(f, a), "status": r["status"], "exit": r["exit"],
                        "time": "%.3f" % r["time"], "conflicts": r.get("conflicts", ""),
                        "decisions": r.get("decisions", ""),
                        "propagations": r.get("propagations", ""),
                        "timeout": a.timeout, "options": a.options})
            fh.flush()
            print("[%d/%d] %-8s %8.2fs %s%s" % (counter[0], len(todo), r["status"],
                                              r["time"], rel(f, a),
                                              ("  " + r["msg"]) if r["msg"] else ""),
                  flush=True)
        return r

    stats = {}
    try:
        with cf.ThreadPoolExecutor(max(1, a.jobs)) as ex:
            for r in ex.map(work, todo):
                stats[r["status"]] = stats.get(r["status"], 0) + 1
    finally:
        fh.close()
    print("done: %d files in %.1fs: %s -> %s" % (
        len(todo), time.time() - t0,
        ", ".join("%s=%d" % kv for kv in sorted(stats.items())), a.out))
    return 1 if stats.get("WRONG") or stats.get("CRASH") or stats.get("ERROR") else 0


def rel(f, a):
    if a.dir and len(a.dir) == 1:
        return os.path.relpath(f, os.path.abspath(a.dir[0]))
    return f


def load(path):
    with open(path) as fh:
        rows = list(csv.DictReader(fh))
    out = {}
    for r in rows:
        r["time"] = float(r["time"]) if r["time"] else 0.0
        out[r["file"]] = r
    return out


def par2(rows, timeout):
    total = 0.0
    for r in rows.values():
        if r["status"] in SOLVED and r["time"] <= timeout:
            total += r["time"]
        else:
            total += 2 * timeout
    return total


def cmd_compare(a):
    A, B = load(a.a), load(a.b)
    common = sorted(set(A) & set(B))
    only_a, only_b = sorted(set(A) - set(B)), sorted(set(B) - set(A))
    tos = [float(r["timeout"]) for r in list(A.values()) + list(B.values())
           if r.get("timeout")]
    timeout = a.timeout or (max(tos) if tos else 0.0)
    if not timeout:
        print("error: no timeout in CSVs; pass --timeout", file=sys.stderr)
        return 2
    Ac = {f: A[f] for f in common}
    Bc = {f: B[f] for f in common}
    na, nb = os.path.basename(a.a), os.path.basename(a.b)
    k = a.top

    # disagreements first, loudly
    bad = []
    for f in common:
        sa, sb = A[f]["status"], B[f]["status"]
        if {sa, sb} == {"SAT", "UNSAT"}:
            bad.append((f, sa, sb))
    wrong = [(f, n) for n, rows in ((na, Ac), (nb, Bc)) for f, r in rows.items()
             if r["status"] in ("WRONG", "ERROR", "CRASH")]
    if bad:
        print("!" * 72)
        print("!!! %d DISAGREEING ANSWERS (SAT vs UNSAT) !!!" % len(bad))
        for f, sa, sb in bad:
            print("!!!   %s: %s=%s %s=%s" % (f, na, sa, nb, sb))
        print("!" * 72)
    if wrong:
        print("*** %d WRONG/ERROR/CRASH results:" % len(wrong))
        for f, n in wrong:
            print("***   %s: %s %s" % (n, f, (Ac if n == na else Bc)[f]["status"]))

    def cnt(rows, s):
        return sum(1 for r in rows.values() if r["status"] == s and r["time"] <= timeout)

    print("instances: %d common%s%s, timeout %.0fs" % (
        len(common), (", %d only in %s" % (len(only_a), na)) if only_a else "",
        (", %d only in %s" % (len(only_b), nb)) if only_b else "", timeout))
    print("%-28s %10s %10s" % ("", na[:10], nb[:10]))
    for s in SOLVED:
        print("%-28s %10d %10d" % ("solved " + s, cnt(Ac, s), cnt(Bc, s)))
    print("%-28s %10d %10d" % ("solved total", cnt(Ac, "SAT") + cnt(Ac, "UNSAT"),
                               cnt(Bc, "SAT") + cnt(Bc, "UNSAT")))
    print("%-28s %10.1f %10.1f" % ("PAR-2", par2(Ac, timeout), par2(Bc, timeout)))
    both = [f for f in common if A[f]["status"] in SOLVED and B[f]["status"] in SOLVED
            and A[f]["time"] <= timeout and B[f]["time"] <= timeout]
    only_sa = [f for f in common if A[f]["status"] in SOLVED and f not in both]
    only_sb = [f for f in common if B[f]["status"] in SOLVED and f not in both]
    print("solved by both: %d, only %s: %d, only %s: %d" % (
        len(both), na, len(only_sa), nb, len(only_sb)))
    if both:
        eps = 0.01
        ratios = [((B[f]["time"] + eps) / (A[f]["time"] + eps), f) for f in both]
        g = math.exp(sum(math.log(r) for r, _ in ratios) / len(ratios))
        print("time ratio %s/%s on commonly solved: geo-mean %.3f, "
              "min %.3f, max %.3f" % (nb, na, g, min(ratios)[0], max(ratios)[0]))
        same_conf = sum(1 for f in both if A[f]["conflicts"] == B[f]["conflicts"])
        print("identical conflict counts: %d/%d" % (same_conf, len(both)))
        ratios.sort(reverse=True)
        print("largest slowdowns (%s/%s):" % (nb, na))
        for r, f in ratios[:k]:
            print("  %8.2fx  %8.2fs %8.2fs  %s" % (r, A[f]["time"], B[f]["time"], f))
        if a.all:
            print("per-instance:")
            for f in common:
                ra, rb = A[f], B[f]
                rt = (rb["time"] + 0.01) / (ra["time"] + 0.01)
                print("  %-8s %8.2fs  %-8s %8.2fs  %7.2fx  %s %s  %s" % (
                    ra["status"], ra["time"], rb["status"], rb["time"], rt,
                    ra["conflicts"], rb["conflicts"], f))
    for f in only_sa[:k]:
        print("  only %s: %s (%s %.1fs)" % (na, f, A[f]["status"], A[f]["time"]))
    for f in only_sb[:k]:
        print("  only %s: %s (%s %.1fs)" % (nb, f, B[f]["status"], B[f]["time"]))
    if bad or wrong:
        print("!!! %d SAT/UNSAT disagreements, %d wrong/error/crash results "
              "(listed at the top) !!!" % (len(bad), len(wrong)))
    return 3 if bad or wrong else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="run a solver over CNF files")
    r.add_argument("--solver", default=DEFAULT_SOLVER, help="command (shell-split)")
    r.add_argument("--options", default="", help="extra solver options, e.g. '--sat'")
    r.add_argument("--dir", action="append", help="directory (recursive, repeatable)")
    r.add_argument("--files", nargs="+")
    r.add_argument("--pattern", help="regex filter on file names")
    r.add_argument("--timeout", type=float, default=300.0)
    r.add_argument("--jobs", "-j", type=int, default=1,
                   help="parallel runs (wall times get noisier) [1]")
    r.add_argument("--out", required=True, help="output CSV")
    r.add_argument("--resume", action="store_true", help="skip files already in --out")
    r.add_argument("--check", action="store_true",
                   help="validate SAT witnesses (otherwise '-n' is passed)")
    c = sub.add_parser("compare", help="compare two CSVs")
    c.add_argument("a")
    c.add_argument("b")
    c.add_argument("--timeout", type=float, help="PAR-2 timeout (default: from CSV)")
    c.add_argument("--top", type=int, default=10)
    c.add_argument("--all", action="store_true", help="per-instance table")
    a = ap.parse_args(argv)
    return cmd_run(a) if a.cmd == "run" else cmd_compare(a)


if __name__ == "__main__":
    sys.exit(main())
