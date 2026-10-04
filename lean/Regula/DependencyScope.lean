import Regula.Checker.Workspace

/-! # Mathlib source dependency roots

Setup reads the libraries of the Mathlib integration package (`integration/mathlib/`) through
Lake; no other package of this repository imports Mathlib. Lean parses each header. The emitted
module imports every observed Mathlib root; Lake builds its transitive exported native closure.
This is a setup plan for the Mathlib integration check, not declaration acceptance. Lake,
parsing and filesystem reads remain trusted; the later check still reads its own complete inputs.
-/

namespace Regula.DependencyScope
open Lean System Regula.Checker

private def imports (text origin : String) : IO (Array Name) := do
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext text origin)
  if messages.hasErrors then
    throw <| IO.userError s!"dependency scope: malformed import header in {origin}"
  return (Elab.headerToImports header (includeInit := false)).map (·.module)

private partial def localNeeds (ws : _root_.Lake.Workspace) (key : _root_.Lake.BuildKey) :
    IO (Array _root_.Lake.Module) := do
  match key with
  | .facet target _ => localNeeds ws target
  | .packageTarget package target =>
    if !package.isAnonymous && package != ws.root.keyName then return #[]
    if let some lib := ws.root.leanLibs.find? (·.name == target) then return ← lib.getModuleArray
    if let some exe := ws.root.leanExes.find? (·.name == target) then return #[exe.root]
    throw <| IO.userError s!"dependency scope: unsupported local need {target}"
  | .module name =>
    let some m := ws.findModule? name
      | throw <| IO.userError s!"dependency scope: unknown local module {name}"
    return #[m]
  | .packageModule package name =>
    if package != ws.root.keyName then return #[]
    let some m := ws.findModule? name
      | throw <| IO.userError s!"dependency scope: unknown local module {name}"
    return #[m]
  | .package _ => throw <| IO.userError "dependency scope: unsupported package need"

private def libraryImports (repo : FilePath) : IO (Array Name) :=
  Workspace.withRootWorkspace repo (fun ws => do
    let mut pending := #[]
    if ws.root.leanLibs.isEmpty then
      throw <| IO.userError s!"dependency scope: no library at {repo}"
    for lib in ws.root.leanLibs do
      pending := pending ++ (← lib.getModuleArray)
      for need in lib.config.needs do pending := pending ++ (← localNeeds ws need)
    let mut seen : NameSet := {}
    let mut imported := #[]
    let mut todo := pending.toList
    repeat
      let m :: rest := todo | break
      todo := rest
      if seen.contains m.name then continue
      seen := seen.insert m.name
      let names ← imports (← IO.FS.readFile m.leanFile) m.leanFile.toString
      imported := imported ++ names
      for name in names do
        if let some dependency := ws.findModule? name then todo := dependency :: todo
    return imported) (scrubSearchPath := true) (resolveDependencies := false)

/-- Discover the Mathlib integration package's import roots and emit a parser-checked module.
All required Mathlib roots are kept once in a stable order; Lean validates their printed names. -/
def source (repo : FilePath) : IO String := do
  let roots ← libraryImports (repo / "integration" / "mathlib")
  let ordered := ((roots.filter ((`Mathlib).isPrefixOf ·)).toList.eraseDups.toArray).qsort
    (fun left right => left.toString < right.toString)
  if ordered.isEmpty then throw <| IO.userError "dependency scope: no Mathlib imports discovered"
  let header := String.join (ordered.toList.map fun name => s!"import {name}\n")
  let roundtrip ← imports header "generated Mathlib dependency module"
  unless roundtrip == ordered do
    throw <| IO.userError "dependency scope: import names did not roundtrip through Lean"
  return header ++ "\ndef main : IO Unit := pure ()\n"

end Regula.DependencyScope

/-- Emit only JSON so the toolchain-only provisioner can decode the exact generated source. -/
def main : IO Unit := do
  IO.println (Lean.toJson (← Regula.DependencyScope.source (← IO.currentDir))).compress
