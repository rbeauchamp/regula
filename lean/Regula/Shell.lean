import Regula.Rules

/-!
# The shell of the checker

The checker of a finished build, which the `lint` executable runs (`Regula.LintMain`), Lake's lint
driver for a project that sets `lintDriver := "regula/lint"`. It reads the finished build through
`load`, prints its report and sets its exit code. It writes no file. Lake's own load of the
workspace runs Git in the environment of the caller. It builds nothing: the project's gate builds
with `lake build --wfail` before it runs the checker, and a module without its `.olean` makes the
run `incomplete`.

The verdict is that of `Regula.Closed.run`: `pass` (exit 0) when the input has the closed form and
no rule reports a subject, `fail` (exit 1) when a rule reports one, and `incomplete` (exit 2) when
the build cannot be loaded or the input does not have the closed form (RG2001).
-/

namespace Regula.Shell

open Regula.Closed

/-- The one Lean release that this revision of Regula reads, by its version and commit. The rules
read a name form and a recursion helper's form that this release gives, so the shell refuses any
other. -/
def supportsLean (version commit : String) : Bool :=
  version == "4.35.0" && commit == "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"

/-- The profile that a project states in `lintDriverArgs`; any other text is none. -/
def profileOf? : String → Option Profile
  | "kernel-only" => some .kernelOnly
  | "choice-free" => some .choiceFree
  | "standard-logical" => some .standardLogical
  | _ => none

/-- The line of one finding. -/
def line (f : Finding) : String :=
  let place := if f.module == f.subject then "" else s!" (module {f.module})"
  s!"{f.rule.spelling} {f.subject}{place}: {f.detail}"

/-- Print the findings and the verdict, and give the verdict's exit code. -/
def report (verdict : Verdict) (findings : List Finding) (why : Option String) : IO UInt32 := do
  for f in findings do
    IO.println (line f)
  match verdict, why with
  | .pass, _ => IO.println s!"regula: {verdict.label}"
  | .fail, _ => IO.println s!"regula: {verdict.label}, {findings.length} findings"
  | .incomplete, why =>
    IO.println s!"regula: {verdict.label} (RG2001): {why.getD "no reason"}"
  return verdict.exitCode

/-- What a run read. -/
def coverage (i : Input) : String :=
  s!"regula: read {i.modules.length} claimed modules and {i.tables.claimed.length} of their \
    constants"

/-- Run the checker with the arguments of `lake lint`: exactly one profile. Any other argument list,
any other Lean release and a build that `load` cannot read are `incomplete`. -/
def run (load : Profile → IO Input) (args : List String) : IO UInt32 := do
  unless supportsLean Lean.versionString Lean.githash do
    return ← report .incomplete [] (some s!"this revision of Regula reads only Lean 4.35.0, and \
      this is Lean {Lean.versionString} ({Lean.githash})")
  let [text] := args
    | report .incomplete [] (some "state one profile in `lintDriverArgs`: kernel-only, choice-free \
        or standard-logical")
  let some profile := profileOf? text
    | report .incomplete [] (some s!"{text} is no profile: kernel-only, choice-free or \
        standard-logical")
  match ← (load profile).toBaseIO with
  | .error e => report .incomplete [] (some (toString e))
  | .ok input =>
    let (verdict, findings, why) := Regula.Closed.run input
    IO.println (coverage input)
    report verdict findings why

end Regula.Shell
