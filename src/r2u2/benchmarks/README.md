# Benchmarks: verified monitor vs R2U2's `r2u2_core`

[`run.py`](run.py) runs the verified monitor ([`driver.rs`](driver.rs)) and
R2U2's Rust monitor ([`r2u2_core_driver/main.rs`](r2u2_core_driver/main.rs),
formulas compiled by C2PO with default options) on the same random trace,
times only the monitoring loop, and compares the verdicts step by step.

    R2U2_ROOT=<path to the r2u2 repo> python3 run.py 200000

Results: [`results/results.tsv`](results/results.tsv). On 200,000 steps the
verified monitor is 2–12× slower (median ~6.5×). Verdicts agree, except one
random formula where `r2u2_core` is wrong at 189 steps (checked against MLTL
semantics directly). Smallest known case: `p0 U[0,0] ((p1 U[1,1] p0) U[0,2] p1)`
on `{}, {p0}, {p1}`: `r2u2_core` says true at step 1, the correct value is
false.
