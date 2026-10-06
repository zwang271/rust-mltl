#!/bin/sh
# Main experiment: depth x interval-bound grid.
B=./target/release/r2u2-sizing
for d in 3 4 5; do for mb in 4 10 25 40; do
  $B run $((d*100+mb)) 3000 $d $mb 30 1500 40 1500 12 > out/g_d${d}_b${mb}.jsonl
  echo "d=$d maxb=$mb done $(wc -l < out/g_d${d}_b${mb}.jsonl)"
done; done
