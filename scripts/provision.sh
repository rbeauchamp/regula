#!/bin/bash
# Dependency setup entry point; acquisition routes and prerequisites are documented in
# docs/guides/contributing.md.
set -euo pipefail
cd "$(dirname "$0")/.."
exec lean --run lean/RegulaProvision.lean
