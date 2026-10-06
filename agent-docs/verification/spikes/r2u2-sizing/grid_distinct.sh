#!/bin/sh
# Main experiment, one atom per leaf (every trace the shape allows).
B=./bin/v2
for d in 3 4 5; do for mb in 4 10 25 40; do
  $B run $((d*100+mb+7)) 2000 $d $mb 30 2000 40 1500 12 distinct > out/gd_d${d}_b${mb}.jsonl
  echo "d=$d maxb=$mb done $(wc -l < out/gd_d${d}_b${mb}.jsonl)"
done; done
