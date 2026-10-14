#!/bin/bash
# Only bootstrap/root selection, failure-safe stale-verdict invalidation, local
# dependency provisioning before the deadline, and the external, no-grace
# process-group deadline.
set -euo pipefail
cd "$(dirname "$0")/.."
# The toolchain-only driver invalidates the selected mode's earlier verdicts before setup,
# so a failed or timed-out provisioning cannot leave an accepted one in place.
lean --run lean/RegulaVerification.lean --begin-attempt "$@"
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
# Dependency setup runs under its own limit before the acceptance deadline starts.
# Acquisition routes and prerequisites belong to docs/guides/contributing.md.
"$timeout_command" --signal=KILL 1800s scripts/provision.sh || {
  echo "verification did not start: scripts/provision.sh failed or exceeded its 1800-second limit (exit $?)" >&2
  exit 1
}
exec "$timeout_command" --signal=KILL 420s \
  lean --run lean/RegulaVerification.lean "$@"
