import Regula.DiagnosticsGate
import Regula.Campaigns

/-! # The inventory of campaigns and the diagnostics workflow

The `campaign` job of the diagnostics workflow reads its matrix from the output `campaigns` of the
step `applies`, which writes `Regula.DiagnosticsGate.campaigns`; that program imports only the
toolchain, because the step runs it with `lean --run` before anything is built. This module proves
the list the invocations of `Regula.Campaigns.Job.diagnosticsCampaign`, each spelled as its
arguments after `./scripts/verify.sh`, so the jobs the gate needs are those the inventory counts.
The kernel checks it when this module builds. -/
namespace Regula.Campaigns.Diagnostics

/-- The `campaign` jobs run the invocations of `Job.diagnosticsCampaign`, in order. -/
theorem campaigns_eq :
    Regula.DiagnosticsGate.campaigns =
      (Job.invocations .diagnosticsCampaign).map (" ".intercalate) := by
  decide +kernel

end Regula.Campaigns.Diagnostics
