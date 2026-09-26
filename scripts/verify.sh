#!/bin/bash
# Only bootstrap/root selection, failure-safe stale-verdict invalidation, local
# dependency provisioning before the deadline, and the external, no-grace
# process-group deadline.
set -euo pipefail
cd "$(dirname "$0")/.."
# Invalidate the rule-examples verdict unconditionally once at wrapper entry,
# after the project cd and before any prerequisite check or exec, mirroring the
# driver's begin-attempt. This constant INCOMPLETE cannot create a PASS and
# decides no policy; a write failure fails closed under `set -e`. Scope: this
# receipt only; other verdict artifacts are owned by their own drivers.
mkdir -p tmp
printf '{"outcome":"INCOMPLETE","phase":"setup"}\n' > tmp/rule-examples.json
if command -v gtimeout >/dev/null 2>&1; then
  timeout_command=gtimeout
elif command -v timeout >/dev/null 2>&1; then
  timeout_command=timeout
else
  echo "verification requires GNU coreutils timeout" >&2
  exit 127
fi
if [[ $("$timeout_command" --version) != *"GNU coreutils"* ]]; then
  echo "verification requires GNU coreutils timeout" >&2
  exit 127
fi
# Setup, not verification: point this copy at the shared, read-only Mathlib
# (lean/RegulaProvision.lean; a no-op on GitHub Actions) before the deadline starts.
lean --run lean/RegulaProvision.lean
exec "$timeout_command" --signal=KILL 420s \
  lean --run lean/RegulaVerification.lean "$@"
