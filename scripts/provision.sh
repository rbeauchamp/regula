#!/bin/bash
# Dependency setup entry point; acquisition routes and prerequisites are documented in
# docs/guides/contributing.md.
set -euo pipefail
cd "$(dirname "$0")/.."
# Elan's `lean` proxy, by its path beside the `elan` that PATH resolves (elan-init's
# `~/.elan/bin`, Homebrew's `bin`), never a `lean` that PATH resolves: Lake puts a workspace's
# binary directories first on the PATH of the programs it starts.
elan=$(command -v elan) || { echo "dependency setup requires Elan on PATH" >&2; exit 127; }
exec "${elan%/*}/lean" --run lean/RegulaProvision.lean "$@"
