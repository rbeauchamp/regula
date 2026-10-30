import Regula.Load
import Regula.Rules
import RegulaPolicy.Community

/-!
# The shell of the checker

The checker of a finished build, which the `lint` executable runs (`Regula.LintMain`), Lake's lint
driver for a project that sets `lintDriver := "regula/lint"`. It has three effects: it loads the
finished build (`Regula.Load.loadBundle`), it prints its report, and it sets its exit code. It
writes no file and removes no file. Lake's load of the workspace runs Git, which the guard of the
`lint` executable isolates (`Regula.TaskManager.guard`). It builds nothing: the project's gate
builds the claimed targets with `lake build --wfail` before it runs the checker, and a module
without its `.olean` makes the run `incomplete`.

The verdict is that of `Regula.Closed.run` (the specification's `gateRecord`): `pass` (exit 0)
when the input has the closed form and no rule reports a subject, `fail` (exit 1) when a rule
reports one, and `incomplete` (exit 2) when the build cannot be loaded or the input does not have
the closed form (RG2001).

The option allowlist of RG2006 is, until #484 fixes its members, the options the present rule
accepts: the required options and Mathlib's standard linter set at their values
(`RegulaPolicy.Community.baseline`, `mathlibBaseline`) and every option of
`RegulaPolicy.Community.accepts`.
-/

namespace Regula.Shell

open Lean Regula.Closed RegulaPolicy.Community

/-- The value a Lake option's text gives: `true` or `false`, a numeral, or else the text. -/
def valueOf (text : String) : OptionValue :=
  if text == "true" then .bool true
  else if text == "false" then .bool false
  else match text.toNat? with
    | some n => .nat n
    | none => .string text

/-- RG2006's allowlist until #484: a required option at its value, or an accepted one. An option
set under a leading `weak.` component is the option without it, as Lean reads it (`optionOf`). -/
def allowed (o : Name × String) : Bool :=
  let name := optionOf o.1
  let v := valueOf o.2
  (baseline ++ mathlibBaseline).any (fun r => r.1 == name && v.readsAs r.2) || accepts name v

/-- The address of a rule's page on the rule-reference site. -/
def page (rule : RuleId) : String :=
  s!"https://rbeauchamp.github.io/regula/dev/rules/{rule.spelling}/"

/-- The line of one finding, of the form `Regula.Closed.findingForm`. -/
def line (f : Finding) : String :=
  let place := match f.module with
    | some m => if m == f.subject then "" else s!" (module {m})"
    | none => ""
  s!"{f.rule.spelling} {f.subject}{place}: {f.detail} {page f.rule}"

/-- Print the findings and the verdict, and give the verdict's exit code (`Verdict.exitCode`). -/
def report (verdict : Verdict) (findings : List Finding) (why : Option String) : IO UInt32 := do
  for f in findings do
    IO.println (line f)
  match verdict, why with
  | .pass, _ => IO.println s!"regula: {verdict.label}"
  | .fail, _ => IO.println s!"regula: {verdict.label}, {findings.length} findings"
  | .incomplete, why =>
    IO.println s!"regula: {verdict.label} ({(page .environment)}): {why.getD "no reason"}"
  return verdict.exitCode

/-- What a run read: its environments, the modules of the root package, and the constants of
claimed modules in each environment. -/
def coverage (b : Bundle) : String :=
  let modules := (b.envs.head?.map (·.modules.length)).getD 0
  let claimed := b.envs.map fun i =>
    let table := i.claimTable
    (i.decls.filter fun d => !((table.find? d.module).getD []).isEmpty).length
  s!"regula: read {b.envs.length} environments, {modules} modules of the root package, and \
    {claimed} constants of claimed modules in each environment"

/-- Run the checker on the explicitly named workspace, or on the current directory only when
it is the workspace Lake dispatched. A different implicit workspace is incomplete. -/
unsafe def run (args : List String) : IO UInt32 := do
  let selection ← match args with
    | [] => pure Regula.Load.WorkspaceSelection.dispatched
    | [dir] => pure (Regula.Load.WorkspaceSelection.named dir)
    | _ => do
      IO.eprintln "usage: lint [WORKSPACE]"
      return 2
  match ← (Regula.Load.loadBundle selection).toBaseIO with
  | .error e => report .incomplete [] (some (toString e))
  | .ok bundle =>
    let (verdict, findings, why) := Regula.Closed.run allowed bundle
    IO.println (coverage bundle)
    report verdict findings why

end Regula.Shell
