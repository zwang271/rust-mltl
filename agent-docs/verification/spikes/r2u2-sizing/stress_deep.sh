#!/bin/sh
# 10x deeper targeted search against "half".
for c in "3 10" "3 25" "4 10" "4 40"; do set -- $c
  ./bin/v4 stress half $((90000+$1*100+$2)) 500 $1 $2 40000 12 distinct > out/sd_half_d$1_b$2.jsonl
  python3 -c "
import json; L=[json.loads(l) for l in open('out/sd_half_d$1_b$2.jsonl')]; print('deep half d=$1 mb=$2', len(L), 'beaten', sum(x['gap']>0 for x in L), 'tight', sum(x['gap']==0 for x in L))"
done
