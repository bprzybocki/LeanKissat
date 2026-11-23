#!/bin/sh
# usage: prof.sh <cnf> [opts]; prints top self-time functions and alloc parents
cd /Users/benprz/Documents/kissat_lean/LeanKissat
f=$1; shift
./.lake/build/bin/lkissat "$@" -q -n $f > /dev/null & PID=$!
sleep 2; sample $PID 5 1 -f /tmp/prof.sample > /dev/null 2>&1; kill $PID
grep -A25 "Sort by top of stack" /tmp/prof.sample | tail -24 | sed 's/(in lkissat)//; s/lp_LeanKissat_LeanKissat_//; s/___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00LeanKissat_/forIn:/'
awk '/Call graph:/,/Total number in stack/' /tmp/prof.sample > /tmp/cg.txt
python3 - <<'PY'
import re
lines=open('/tmp/cg.txt').read().split('\n')
stack=[]; agg={}
for l in lines:
    m=re.match(r'^([\s!:|+]*)(\d+)\s+(\S+)',l)
    if not m: continue
    ind,cnt,name=len(m.group(1)),int(m.group(2)),m.group(3)
    while stack and stack[-1][0]>=ind: stack.pop()
    if name in('lean_dec_ref_cold','lean_alloc_small_object_core','mi_free','_platform_memmove'):
        par=stack[-1][1] if stack else '?'
        agg[(name,par)]=agg.get((name,par),0)+cnt
    stack.append((ind,name))
for k,v in sorted(agg.items(),key=lambda x:-x[1])[:8]: print(v,k[0],k[1].replace('lp_LeanKissat_LeanKissat_',''))
PY
