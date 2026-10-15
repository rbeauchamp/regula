import RegulaVerification
import Regula.Campaigns

/-! # The inventory of campaigns and the verification driver

`Regula.Campaigns` states the invocations of `./scripts/verify.sh` and the `qualify` and
`checkerSelftest` campaigns each runs (`runsOf`). The driver, `RegulaVerification`, imports only the
toolchain, and the inventory does not import it, so that `Regula.RegistryChecks`, which defines a
`main` of its own as the driver does, can import the inventory. This module relates the two: the
inventory's invocations are exactly the driver's (`verifyInvocations_eq`), and for each of them
the `qualify` and `checkerSelftest` commands the driver runs are those `runsOf` gives, a `qualify`
selection by its form (`runsOf_commands`). The kernel checks both when this module builds. -/
namespace Regula.Campaigns.Verification

open Regula.Qualification

/-- A `qualify` or `checkerSelftest` command: the form of the `qualify` selection, none when its
arguments are not a selection, or the self-test's command line. -/
inductive Run where
  /-- A run of `lake exe qualify`. -/
  | qualify (command : Option Command)
  /-- A run of `lake exe checkerSelftest` with these arguments. -/
  | selftest (arguments : List String)
  /-- An invocation of `./scripts/verify.sh`, which no driver command is. -/
  | verify (arguments : List String)
  deriving DecidableEq

/-- What a command of the driver runs of `qualify` or `checkerSelftest`, if anything. -/
def runOf (command : RegulaVerification.Command) : Option Run :=
  match command.program with
  | .stated .. => none
  | .toolchain .lake => match command.args.toList with
    | "exe" :: "qualify" :: "--under-deadline" :: selection =>
        some (.qualify ((Command.parse selection).map form))
    | "exe" :: "qualify" :: selection => some (.qualify ((Command.parse selection).map form))
    | "exe" :: "checkerSelftest" :: selection => some (.selftest selection)
    | _ => none
  | .toolchain _ => none

/-- The command a campaign of the inventory stands for. -/
def Campaign.run : Campaign → Run
  | .verify arguments => .verify arguments
  | .qualify command => .qualify (some command)
  | .selftest campaign => .selftest campaign.arguments

/-- The inventory's invocations of `./scripts/verify.sh` are the driver's, in the order of its
modes. -/
theorem verifyInvocations_eq :
    verifyInvocations = RegulaVerification.modes.map RegulaVerification.arguments := by
  decide +kernel

/-- Only the first acceptance step's commands depend on the directories of its copy and of its
pending record. -/
private theorem commands_of_ne_ordinary (copy pending : String) (mode : RegulaVerification.Mode)
    (h : mode ≠ .ordinary) :
    RegulaVerification.commands copy pending mode = RegulaVerification.commands "" "" mode := by
  cases mode <;> first | rfl | exact absurd rfl h

/-- The first acceptance step runs `qualify combined` alone of these programs, wherever its copy
and pending record are. -/
private theorem ordinary_runs (copy pending : String) :
    (RegulaVerification.commands copy pending .ordinary).filterMap runOf =
      [.qualify (some .combined)] :=
  rfl

/-- The statement of `runsOf_commands` for the empty directories. -/
private theorem runsOf_commands_empty :
    ∀ mode ∈ RegulaVerification.modes,
      (RegulaVerification.commands "" "" mode).filterMap runOf =
        (runsOf (RegulaVerification.arguments mode)).map Campaign.run := by
  decide +kernel

/-- For every mode of the driver, the `qualify` and `checkerSelftest` commands it runs, in order,
are the campaigns `runsOf` gives for its arguments; each `qualify` command is a selection
(`Command.parse` accepts it) of that form. -/
theorem runsOf_commands (copy pending : String) :
    ∀ mode ∈ RegulaVerification.modes,
      (RegulaVerification.commands copy pending mode).filterMap runOf =
        (runsOf (RegulaVerification.arguments mode)).map Campaign.run := by
  intro mode member
  by_cases ordinary : mode = .ordinary
  · subst ordinary
    rw [ordinary_runs, ← runsOf_commands_empty _ member, ordinary_runs]
  · rw [commands_of_ne_ordinary copy pending mode ordinary]
    exact runsOf_commands_empty mode member

end Regula.Campaigns.Verification
