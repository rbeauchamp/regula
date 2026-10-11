#!/bin/bash
# Dependency setup entry point; acquisition routes and prerequisites are documented in
# docs/guides/contributing.md.
set -euo pipefail
cd "$(dirname "$0")/.."
# Elan's `lean` proxy, by its path, never a `lean` that PATH resolves: Lake puts a workspace's
# binary directories first on the PATH of the programs it starts.
exec "${ELAN_HOME:-$HOME/.elan}/bin/lean" --run lean/RegulaProvision.lean "$@"
