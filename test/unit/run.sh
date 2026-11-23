#!/bin/sh
# Differential unit test: C Kissat data structures vs. the Lean port.
# Builds test/unit/driver.c against verbatim copies of the Kissat sources
# (plus the stubs in test/unit/stub) and the Lean `unittest` executable,
# runs both and diffs their outputs.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
KSRC=${KISSAT_SRC:?set KISSAT_SRC to the src/ directory of a Kissat 4.0.4 checkout}
BUILD="$ROOT/.lake/build/unittest-c"
rm -rf "$BUILD"
mkdir -p "$BUILD"
for f in allocate.h averages.c averages.h heap.c heap.h inlineheap.h \
         inlinequeue.h queue.c queue.h random.h reluctant.c reluctant.h \
         smooth.c smooth.h stack.h utilities.h; do
  cp "$KSRC/$f" "$BUILD/"
done
cp "$HERE"/stub/*.h "$BUILD/"
cp "$HERE/driver.c" "$BUILD/"
# Asserts are enabled on purpose (no -DNDEBUG) to catch invalid operations.
${CC:-cc} -O1 -std=c99 -Wall -o "$BUILD/driver" \
  "$BUILD/driver.c" "$BUILD/heap.c" "$BUILD/queue.c" "$BUILD/smooth.c" \
  "$BUILD/reluctant.c" "$BUILD/averages.c"
"$BUILD/driver" > "$BUILD/c.out"
(cd "$ROOT" && lake build unittest >/dev/null && .lake/build/bin/unittest) > "$BUILD/lean.out"
if cmp -s "$BUILD/c.out" "$BUILD/lean.out"; then
  echo "unit test PASSED ($(wc -l < "$BUILD/c.out" | tr -d ' ') lines identical)"
else
  diff "$BUILD/c.out" "$BUILD/lean.out" | head -40
  echo "unit test FAILED"
  exit 1
fi
