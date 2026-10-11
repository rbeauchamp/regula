#!/bin/bash
# Dependency setup entry point; acquisition routes and prerequisites are documented in
# docs/guides/contributing.md.
set -euo pipefail
cd "$(dirname "$0")/.."
# The `lean` of the toolchain that lean-toolchain names, by its path in Elan's toolchain
# directory (Lake.toolchain2Dir), never a `lean` that PATH resolves: Lake puts a workspace's
# binary directories first on the PATH of the programs it starts. The driver it runs first refuses
# any compiler but the pinned version and commit.
toolchain=$(<lean-toolchain)
# Without its surrounding blanks, CR included, as Lake reads it (ToolchainVer.ofFile?).
toolchain=${toolchain#"${toolchain%%[![:space:]]*}"}
toolchain=${toolchain%"${toolchain##*[![:space:]]}"}
toolchain=${toolchain//\//--}
elan_home=${ELAN_HOME:-$HOME/.elan}
[[ $elan_home == /* ]] || { echo "provisioning requires an absolute ELAN_HOME, not $elan_home" >&2; exit 127; }
lean=$elan_home/toolchains/${toolchain//:/---}/bin/lean
[[ -x $lean ]] || { echo "provisioning requires the Elan toolchain $(<lean-toolchain) at $lean" >&2; exit 127; }
exec "$lean" --run lean/RegulaProvision.lean
