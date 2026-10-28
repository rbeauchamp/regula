import Regula.DiagnosticsGate
import Regula.Campaigns

/-! # The inventory of campaigns, the diagnostics workflow and the local gate

The `campaign` job of the diagnostics workflow reads its matrix from the output `campaigns` of the
step `applies`, which writes `Regula.DiagnosticsGate.campaigns`; that program imports only the
toolchain, because the step runs it with `lean --run` before anything is built. This module proves
the list the invocations of `Regula.Campaigns.Job.diagnosticsCampaign`, each spelled as its
arguments after `./scripts/verify.sh`, so the jobs the gate needs are those the inventory counts.

The same program runs the local gate (`Regula.DiagnosticsGate.localSteps`). This module proves its
invocations of `./scripts/verify.sh` exactly those of the jobs that check a change
(`Job.checksChange`), in the order of `Job.all` and of each job's invocations, so the local gate
runs every campaign of those jobs and no other. The kernel checks both when this module builds. -/
namespace Regula.Campaigns.Diagnostics

/-- The `campaign` jobs run the invocations of `Job.diagnosticsCampaign`, in order. -/
theorem campaigns_eq :
    Regula.DiagnosticsGate.campaigns =
      (Job.invocations .diagnosticsCampaign).map (" ".intercalate) := by
  decide +kernel

/-- The local gate runs, in order, the `verify.sh` invocations of each job that checks a change. -/
theorem localVerifications_eq :
    Regula.DiagnosticsGate.localSteps.filterMap Regula.DiagnosticsGate.Step.verifyArguments =
      (Job.all.filter Job.checksChange).flatMap Job.invocations := by
  decide +kernel

end Regula.Campaigns.Diagnostics
