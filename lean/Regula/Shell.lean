/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Language
public import Regula.Rules

/-!
# The shell of the checker

The checker, which the `lint` executable runs (`Regula.LintMain`), Lake's lint driver for a project
that sets `lintDriver := "regula/lint"`. It reads the finished build through `load`, prints its report
and sets its exit code. It writes no file itself, and Lake's own load of the workspace runs Git in the
environment of the caller. Only the full gate builds, through `build`. Otherwise the project's gate
builds with `lake build --wfail` before it runs the checker, and a module without its `.olean` makes
the run `incomplete`.

A run with one profile gives the proof verdict, that of `Regula.Closed.decision`: `pass` (exit 0) when
the input has the closed form and no rule reports a subject, `fail` (exit 1) when a rule reports one, and
`incomplete` (exit 2) when the build cannot be loaded or the input does not have the closed form (RG2001).
`profileOfRun` and `decision` are pure, and `specification/RegulaSpecification/Proofs/Load.lean` states
what they give. It promises nothing about what ran during the build.

A run with the profile, `full` and a directory is the full gate (`Regula.Language.gate`) on the project
there: the language check, then the build and its replay, then the same rules. Only that run can print a
full verdict, because only there the check came first, and only from a checker that the project's Lake did
not start (`Regula.Reader.startedOutside`).
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
  | .pass =>
    IO.println s!"regula: proof verdict: {r.verdict.label}, which says nothing about what ran during \
      the build"
  | .fail _ rest =>
    IO.println s!"regula: proof verdict: {r.verdict.label}, {rest.length + 1} findings"
  | .incomplete why => IO.println s!"regula: proof verdict: {r.verdict.label} (RG2001): {why}"
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
    | _ =>
      .error s!"state one profile in `lintDriverArgs`: {profileSpellings}, or, from a checkout of \
        Regula, a profile, `full` and the project's directory"

/-- The rules on the finished build: prints what they found, and gives their verdict. -/
def rules (load : Profile → IO Input) (profile : Profile) : IO Verdict := do
  let loaded := (← (load profile).toBaseIO).mapError toString
  if let .ok input := loaded then IO.println (coverage input)
  let r := decision loaded
  for f in r.findings do
    IO.println (line f)
  if let .incomplete why := r then
    IO.println s!"RG2001: {why}"
  return r.verdict

/-- What the language check says of a reading, printed. -/
def check (read : IO (Language.Reading × List String)) : IO Language.Outcome := do
  match ← read.toBaseIO with
  | .error e =>
    IO.println s!"RG2001: {e}"
    return .incomplete
  | .ok (reading, lines) =>
    for l in lines do
      IO.println l
    IO.println s!"regula: the language check read {reading.files.length} files"
    return Language.decision reading

/-- The full gate. -/
def runFull (load : Profile → IO Input) (read : IO (Language.Reading × List String))
    (build : IO Bool) (profile : Profile) : IO UInt32 := do
  let report ← Language.gate (check read) build (rules load profile)
  IO.println report.label
  return report.exitCode

/-- Run the checker with the arguments of `lake lint` (`profileOfRun`) and read the build through
`load`, giving the verdict of `decision`. Or, with a profile, `full` and a directory, run the full gate on
the project there. -/
def run (load : Profile → IO Input) (loadAt : String → Profile → IO Input)
    (read : String → IO (Language.Reading × List String)) (build : String → IO Bool)
    (args : List String) : IO UInt32 := do
  let (profileArgs, project) := match args with
    | [text, "full", dir] => ([text], some dir)
    | _ => (args, none)
  match profileOfRun Lean.versionString Lean.githash profileArgs, project with
  | .error why, _ => report (.incomplete why)
  | .ok profile, some dir => runFull (loadAt dir) (read dir) (build dir) profile
  | .ok profile, none =>
    let loaded := (← (load profile).toBaseIO).mapError toString
    if let .ok input := loaded then IO.println (coverage input)
    report (decision loaded)

end Regula.Shell
