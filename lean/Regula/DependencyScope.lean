import Regula.Checker.Documentation

/-! # Mathlib source dependency roots

Setup reads the Audit and website libraries through Lake and the same Markdown/Verso fence
scanners as documentation acceptance. Lean parses each header. The emitted module imports
every observed Mathlib root; Lake builds its transitive exported native closure. This is a
setup plan, not declaration or documentation acceptance. Lake, parsing and filesystem reads
remain trusted; later acceptance still reads and checks its own complete inputs.
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

private def librarySources (repo : FilePath) (library : Option Name := none)
    (render : Option String := none) : IO (Array RegulaPolicy.SourceSnapshot × Array Name) :=
  Workspace.withRootWorkspace repo (fun ws => do
    let mut sources := #[]
    let mut pending := #[]
    let libraries := ws.root.leanLibs.filter fun lib => library.all (· == lib.name)
    if libraries.isEmpty then throw <| IO.userError s!"dependency scope: no library at {repo}"
    for lib in libraries do
      for m in ← lib.getModuleArray do
        sources := sources.push ⟨m.leanFile.toString, ← IO.FS.readFile m.leanFile⟩
        pending := pending.push m
      for need in lib.config.needs do pending := pending ++ (← localNeeds ws need)
    if let some render := render then
      let some exe := ws.root.leanExes.find?
          (·.name == _root_.Lake.stringToLegalOrSimpleName render)
        | throw <| IO.userError s!"dependency scope: unknown renderer {render}"
      pending := pending.push exe.root
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
    return (sources, imported)) (scrubSearchPath := true) (resolveDependencies := false)

private def fenceImports (scan : Documentation.ScanResult) : IO (Array Name) := do
  unless scan.problems.isEmpty do
    throw <| IO.userError s!"dependency scope: {String.intercalate "; " scan.problems.toList}"
  scan.fences.flatMapM fun fence => imports fence.body s!"{fence.document.uri}:{fence.line}"

/-- Discover package and documentation import roots and emit a parser-checked module.
All required Mathlib roots are kept once in a stable order; Lean validates their printed names. -/
def source (repo : FilePath) : IO String := do
  let mut roots := #[]
  let verso ← IO.ofExcept (Documentation.parseVersoOption "website:RegulaStandard:regula-standard")
  for (package, library, render) in #[(repo / "audit", none, none),
      (repo / verso.dir, some verso.library, some verso.render)] do
    let (documents, imported) ← librarySources package library render
    roots := roots ++ imported
    for document in documents do
      if library.isSome then
        roots := roots ++ (← fenceImports (Documentation.scanVerso document.source document.uri))
  for document in ← Documentation.captureMarkdown (repo / "docs") do
    roots := roots ++ (← fenceImports (Documentation.scan document.source document.uri))
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
