#!/bin/bash
# Only the entry point of local setup (lean/RegulaProvision.lean): run once in a fresh
# copy before the first `lake build`, so Lake finds the shared, read-only Mathlib instead
# of cloning and building its own.
set -euo pipefail
cd "$(dirname "$0")/.."
exec lean --run lean/RegulaProvision.lean
