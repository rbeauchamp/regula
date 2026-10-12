#!/bin/bash
# Dependency setup entry point; acquisition routes and prerequisites are documented in
# docs/guides/contributing.md.
set -euo pipefail
cd "$(dirname "$0")/.."
lean_command="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.34.1/bin/lean"
exec "$lean_command" --run lean/RegulaProvision.lean
