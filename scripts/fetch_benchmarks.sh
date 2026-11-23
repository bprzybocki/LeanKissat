#!/bin/sh
# Download and decompress sampled SAT Anniversary Track instances.
# usage: fetch_benchmarks.sh <url-list> <outdir>
set -u
list=$1; out=$2
mkdir -p "$out"
while read -r u; do
  [ -z "$u" ] && continue
  h=$(basename "$u")
  if ls "$out"/"$h"-*.cnf >/dev/null 2>&1; then continue; fi
  tmp="$out/.dl-$h"
  name=$(curl -sSIL -m 60 "$u" | grep -i '^content-disposition' | tail -1 | sed 's/.*filename=//' | tr -d '\r')
  curl -sSL -m 1800 "$u" -o "$tmp" || { echo "FAIL $u"; rm -f "$tmp"; continue; }
  case "$name" in
    *.xz) xz -dc "$tmp" > "$out/${name%.xz}" && rm -f "$tmp" ;;
    *) mv "$tmp" "$out/$name" ;;
  esac
  echo "OK $name"
done < "$list"
