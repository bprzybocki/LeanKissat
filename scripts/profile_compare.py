#!/usr/bin/env python3
"""Sequential repeated timings with exact status and search-counter checks.

Example:
  python3 -B -I scripts/profile_compare.py \
    --solver c="$KISSAT" \
    --solver baseline=/tmp/baseline-lkissat \
    --solver candidate=.lake/build/bin/lkissat \
    --out /tmp/comparison.json formula.cnf

Build the binaries before running this script. Solver order rotates between
repetitions. Statistics and model suppression are added to the supplied options.
"""

import argparse
import hashlib
import json
import math
import platform
import shlex
import statistics
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import difftest


def run(command, options, path, timeout):
    argv = command + options + ["--statistics", "-n", str(path)]
    start = time.perf_counter()
    p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout)
    elapsed = time.perf_counter() - start
    parsed = difftest.parse_output(p.stdout)
    codes = {"UNKNOWN": 0, "SATISFIABLE": 10, "UNSATISFIABLE": 20}
    if parsed["status_lines"] != 1 or codes.get(parsed["status"]) != p.returncode:
        raise RuntimeError(f"invalid solver result: {argv!r}\n{p.stdout}\n{p.stderr}")
    if not parsed["stats"] or "conflicts" not in parsed["stats"]:
        raise RuntimeError(f"missing statistics: {argv!r}")
    return {
        "seconds": elapsed,
        "status": parsed["status"],
        "exit": p.returncode,
        "stats": parsed["stats"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", action="append", required=True, metavar="NAME=COMMAND")
    parser.add_argument("--opts", default="--plain --conflicts=10000")
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    if args.repeats < 1 or args.warmups < 0:
        parser.error("repeats must be positive and warmups nonnegative")
    solvers = {}
    for spec in args.solver:
        name, separator, command = spec.partition("=")
        if not separator or not name or not shlex.split(command) or name in solvers:
            parser.error(f"invalid or duplicate solver: {spec}")
        solvers[name] = shlex.split(command)
    options = shlex.split(args.opts)
    names = list(solvers)
    binaries = {}
    for name, command in solvers.items():
        binary = Path(command[0])
        binaries[name] = {
            "command": command,
            "sha256": hashlib.sha256(binary.read_bytes()).hexdigest() if binary.is_file() else None,
        }
    result = {
        "platform": platform.platform(),
        "architecture": platform.machine(),
        "options": options + ["--statistics", "-n"],
        "repeats": args.repeats,
        "warmups": args.warmups,
        "binaries": binaries,
        "instances": [],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    print("instance\t" + "\t".join(names), flush=True)
    for path in args.files:
        path = path.resolve(strict=True)
        expected = None
        samples = {name: [] for name in names}
        for repeat in range(-args.warmups, args.repeats):
            offset = (repeat + args.warmups) % len(names)
            order = names[offset:] + names[:offset]
            for name in order:
                sample = run(solvers[name], options, path, args.timeout)
                identity = (sample["status"], sample["exit"], sample["stats"])
                if expected is None:
                    expected = identity
                elif identity != expected:
                    raise RuntimeError(f"status or counters differ for {path}, solver {name}")
                if repeat >= 0:
                    samples[name].append(sample["seconds"])
        medians = {name: statistics.median(times) for name, times in samples.items()}
        result["instances"].append({
            "path": str(path),
            "status": expected[0],
            "stats": expected[2],
            "samples": samples,
            "medians": medians,
        })
        args.out.write_text(json.dumps(result, indent=2) + "\n")
        print(path.name + "\t" + "\t".join(f"{medians[name]:.6f}" for name in names), flush=True)
    for name in names[1:]:
        ratio = math.exp(statistics.mean(
            math.log(row["medians"][name] / row["medians"][names[0]])
            for row in result["instances"]
        ))
        print(f"geometric mean {name}/{names[0]}: {ratio:.3f}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
