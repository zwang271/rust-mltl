#!/bin/sh
# Targeted search for traces that beat a candidate rule (see README.md).
for rule in half_floor half; do for d in 3 4 5; do for mb in 10 25 40; do
  ./bin/v4 stress $rule $((d*1000+mb)) 1200 $d $mb 4000 12 distinct > out/s_${rule}_d${d}_b${mb}.jsonl
  python3 -c "
import json,sys; L=[json.loads(l) for l in open('out/s_${rule}_d${d}_b${mb}.jsonl')]
print('$rule d=$d mb=$mb', len(L), 'beaten', sum(x['gap']>0 for x in L), 'tight', sum(x['gap']==0 for x in L))"
done; done; done
