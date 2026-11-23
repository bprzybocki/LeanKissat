#!/bin/sh
# Differential test of the sorting routines: C Kissat (sort.h, rank.h, sort.c)
# vs. the Lean port (Util/Sort.lean, Util/Radix.lean, Core/SortLits.lean).
# Builds test/unit/sort_driver.c against verbatim copies of the Kissat sources
# (plus the stubs in test/unit/sortstub) and the Lean `sorttest` executable,
# runs both and diffs their outputs. With `--bench`, additionally times
# sorting 10^6 random UInt32 in C (-O3 -DNDEBUG) and in Lean.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
KSRC=${KISSAT_SRC:?set KISSAT_SRC to the src/ directory of a Kissat 4.0.4 checkout}
BUILD="$ROOT/.lake/build/sorttest-c"
rm -rf "$BUILD"
mkdir -p "$BUILD"
for f in allocate.h rank.h sort.c sort.h stack.h utilities.h; do
  cp "$KSRC/$f" "$BUILD/"
done
cp "$HERE"/sortstub/*.h "$BUILD/"
cp "$HERE/sort_driver.c" "$BUILD/"
# Asserts are enabled on purpose (no -DNDEBUG) to catch invalid operations.
${CC:-cc} -O1 -std=c99 -D_POSIX_C_SOURCE=199309L -Wall -o "$BUILD/sort_driver" \
  "$BUILD/sort_driver.c" "$BUILD/sort.c"
"$BUILD/sort_driver" > "$BUILD/c.out"
(cd "$ROOT" && lake build sorttest >/dev/null && .lake/build/bin/sorttest) > "$BUILD/lean.out"
if cmp -s "$BUILD/c.out" "$BUILD/lean.out"; then
  echo "sort test PASSED ($(wc -l < "$BUILD/c.out" | tr -d ' ') lines identical)"
else
  diff "$BUILD/c.out" "$BUILD/lean.out" | head -40
  echo "sort test FAILED"
  exit 1
fi
if [ "$1" = "--bench" ]; then
  ${CC:-cc} -O3 -DNDEBUG -std=c99 -D_POSIX_C_SOURCE=199309L -Wall \
    -o "$BUILD/sort_bench" "$BUILD/sort_driver.c" "$BUILD/sort.c"
  "$BUILD/sort_bench" bench > "$BUILD/c.bench"
  (cd "$ROOT" && .lake/build/bin/sorttest bench) > "$BUILD/lean.bench"
  if cmp -s "$BUILD/c.bench" "$BUILD/lean.bench"; then
    echo "bench outputs identical"
  else
    echo "bench outputs DIFFER"; exit 1
  fi
fi
