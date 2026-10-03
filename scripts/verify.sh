#!/usr/bin/env bash
# Verify every crate in the workspace with Verus. Exits non-zero on any failure.
# Extra arguments are passed to `cargo verus verify` (e.g. `-p mltl-core`).
set -euo pipefail
cd "$(dirname "$0")/.."
if [ $# -eq 0 ]; then
  exec cargo verus verify --workspace
else
  exec cargo verus verify "$@"
fi
