/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Rules

/-!
# The shell of the checker

The checker of a finished build, which the `lint` executable runs (`Regula.LintMain`), Lake's lint
driver for a project that sets `lintDriver := "regula/lint"`. It reads the finished build through
`load`, prints its report and sets its exit code. It writes no file. Lake's own load of the
workspace runs Git in the environment of the caller. It builds nothing: the project's gate builds
with `lake build --wfail` before it runs the checker, and a module without its `.olean` makes the
run `incomplete`.

The verdict is that of `Regula.Closed.decision`: `pass` (exit 0) when the input has the closed form
and no rule reports a subject, `fail` (exit 1) when a rule reports one, and `incomplete` (exit 2)
when the build cannot be loaded or the input does not have the closed form (RG2001). `profileOfRun`
and `decision` are pure, and `specification/RegulaSpecification/Proofs/Load.lean` states what they
give.
-/

public section

namespace Regula.Shell

open Regula.Closed

/-- The one Lean release that this revision of Regula reads, by its version and commit. The rules
read a name form and a recursion helper's form that this release gives, so the shell refuses any
other. -/
def supportsLean (version commit : String) : Bool :=
  version == "4.35.0" && commit == "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"

/-- The line of one finding. -/
def line (f : Finding) : String :=
  let place := if f.module == f.subject then "" else s!" (module {f.module})"
  s!"{f.rule.spelling} {f.subject}{place}: {f.detail}"

/-- Print the findings and the verdict, and give the verdict's exit code. -/
def report (r : Report) : IO UInt32 := do
  for f in r.findings do
    IO.println (line f)
  match r with
  | .pass => IO.println s!"regula: {r.verdict.label}"
  | .fail _ rest => IO.println s!"regula: {r.verdict.label}, {rest.length + 1} findings"
  | .incomplete why => IO.println s!"regula: {r.verdict.label} (RG2001): {why}"
  return r.verdict.exitCode

/-- What a run read. -/
def coverage (i : Input) : String :=
  s!"regula: read {i.modules.length} claimed modules and {i.claimedDecls.length} of their \
    constants"

/-- The spellings of the profiles, for a refusal. -/
def profileSpellings : String :=
  ", ".intercalate (Profile.all.map (·.spelling))

/-- The profile of a run of the Lean release `version` at `commit` with the arguments `args`, or why
the run is `incomplete`: any other release, and any argument list other than one profile. -/
def profileOfRun (version commit : String) (args : List String) : Except String Profile :=
  if !supportsLean version commit then
    .error s!"this revision of Regula reads only Lean 4.35.0, and this is Lean {version} ({commit})"
  else
    match args with
    | [text] =>
      match Profile.ofSpelling? text with
      | some profile => .ok profile
      | none => .error s!"{text} is no profile: {profileSpellings}"
    | _ => .error s!"state one profile in `lintDriverArgs`: {profileSpellings}"

/-- Run the checker with the arguments of `lake lint` (`profileOfRun`), read the build through
`load` and report the verdict of `decision`. -/
def run (load : Profile → IO Input) (args : List String) : IO UInt32 := do
  match profileOfRun Lean.versionString Lean.githash args with
  | .error why => report (.incomplete why)
  | .ok profile =>
    let loaded := (← (load profile).toBaseIO).mapError toString
    if let .ok input := loaded then IO.println (coverage input)
    report (decision loaded)

end Regula.Shell
