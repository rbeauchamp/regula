import Regula.Report
import Regula.Collect
import Regula.Diagnostic
import RegulaCore.Coordinates
import RegulaCore.EditorPolicy
import Regula.Checker.Common
import Lean

/-!
# Fresh elaboration transcripts

Fresh source-elaboration transcripts for the two narrowly allowed generated
roles. The source is compared byte-for-byte before and after elaboration;
isolated callers release frontend imports before consuming the typed result.
-/

universe u

namespace Regula.Checker.Frontend
open scoped Regula.Report

open Lean Lean.Elab
open RegulaPolicy (EvaluatorRole)
open Regula.Checker.PolicyCodec (exactFields)

/-- One import of the elaborated module (`RegulaPolicy.Frontend.ImportRecord`), with the
exact-field JSON codec the frontend workers exchange. -/
abbrev ImportRecord := RegulaPolicy.Frontend.ImportRecord
deriving instance ToJson for RegulaPolicy.Frontend.ImportRecord
instance : FromJson RegulaPolicy.Frontend.ImportRecord := ⟨fun j => do
  exactFields j ["module", "importAll", "isExported", "isMeta"]
  return {
    «module» := ← j.getObjValAs? _ "module"
    importAll := ← j.getObjValAs? _ "importAll"
    isExported := ← j.getObjValAs? _ "isExported"
    isMeta := ← j.getObjValAs? _ "isMeta"
  }⟩

/-- A source range as line/column start and end positions (`RegulaPolicy.Frontend.SyntaxRange`),
with its exact-field JSON codec. -/
abbrev SyntaxRange := RegulaPolicy.Frontend.SyntaxRange
deriving instance ToJson for RegulaPolicy.Frontend.SyntaxRange
instance : FromJson RegulaPolicy.Frontend.SyntaxRange := ⟨fun j => do
  exactFields j ["start", "end"]
  return {
    start := ← j.getObjValAs? _ "start"
    «end» := ← j.getObjValAs? _ "end"
  }⟩

/-- One elaborator invocation read from a command's info tree: its role, elaborator, syntax
kind, source range and whether it is pinned (`RegulaPolicy.Frontend.Evaluator`), with its
exact-field JSON codec. -/
abbrev Evaluator := RegulaPolicy.Frontend.Evaluator
deriving instance ToJson for RegulaPolicy.Frontend.Evaluator
instance : FromJson RegulaPolicy.Frontend.Evaluator := ⟨fun j => do
  exactFields j ["role", "elaborator", "kind", "range", "pinned"]
  return {
    role := ← j.getObjValAs? _ "role"
    elaborator := ← j.getObjValAs? _ "elaborator"
    kind := ← j.getObjValAs? _ "kind"
    range := ← j.getObjValAs? _ "range"
    pinned := ← j.getObjValAs? _ "pinned"
  }⟩

/-- One constant a command added: its name, kind, printed type and native statement
(`RegulaPolicy.Frontend.AddedDeclaration`), with its exact-field JSON codec. -/
abbrev AddedDeclaration := RegulaPolicy.Frontend.AddedDeclaration
deriving instance ToJson for RegulaPolicy.Frontend.AddedDeclaration
instance : FromJson RegulaPolicy.Frontend.AddedDeclaration := ⟨fun j => do
  exactFields j ["name", "kind", "type", "nativeStatement"]
  return {
    name := ← j.getObjValAs? _ "name"
    kind := ← j.getObjValAs? _ "kind"
    «type» := ← j.getObjValAs? _ "type"
    nativeStatement := ← j.getObjValAs? _ "nativeStatement"
  }⟩

/-- The binder site of a declared constant at its declaration identifier
(`RegulaPolicy.Frontend.DeclarationBinding`), with its exact-field JSON codec. -/
abbrev DeclarationBinding := RegulaPolicy.Frontend.DeclarationBinding
deriving instance ToJson for RegulaPolicy.Frontend.DeclarationBinding
instance : FromJson RegulaPolicy.Frontend.DeclarationBinding := ⟨fun j => do
  exactFields j ["name", "range"]
  return {
    name := ← j.getObjValAs? _ "name"
    range := ← j.getObjValAs? _ "range"
  }⟩

/-- One elaborated command that added constants, with its evaluators, binders and whether it
declares an axiom, and the source-local overrides its environment holds
(`RegulaPolicy.Frontend.Command`), with its exact-field JSON codec. -/
abbrev Command := RegulaPolicy.Frontend.Command
deriving instance ToJson for RegulaPolicy.Frontend.Command
instance : FromJson RegulaPolicy.Frontend.Command := ⟨fun j => do
  exactFields j ["commandElaborator", "commandKind", "commandRange", "added", "addedDeclarations",
      "evaluators", "bindings", "declaresAxiom", "sourceLocalOverrides"]
  return {
    commandElaborator := ← j.getObjValAs? _ "commandElaborator"
    commandKind := ← j.getObjValAs? _ "commandKind"
    commandRange := ← j.getObjValAs? _ "commandRange"
    added := ← j.getObjValAs? _ "added"
    addedDeclarations := ← j.getObjValAs? _ "addedDeclarations"
    evaluators := ← j.getObjValAs? _ "evaluators"
    bindings := ← j.getObjValAs? _ "bindings"
    declaresAxiom := ← j.getObjValAs? _ "declaresAxiom"
    sourceLocalOverrides := ← j.getObjValAs? _ "sourceLocalOverrides"
  }⟩

/-- The fresh-elaboration transcript of one module (`RegulaPolicy.Frontend.Transcript`),
with its exact-field JSON codec. -/
abbrev Transcript := RegulaPolicy.Frontend.Transcript
deriving instance ToJson for RegulaPolicy.Frontend.Transcript
instance : FromJson RegulaPolicy.Frontend.Transcript := ⟨fun j => do
  exactFields j ["module", "source", "sourceBytes", "sourceContent", "leanVersion", "leanGitHash",
      "imports", "commands", "runtimeReplacements", "replacementHistoryUnsupported"]
  return {
    «module» := ← j.getObjValAs? _ "module"
    source := ← j.getObjValAs? _ "source"
    sourceBytes := ← j.getObjValAs? _ "sourceBytes"
    sourceContent := ← j.getObjValAs? _ "sourceContent"
    leanVersion := ← j.getObjValAs? _ "leanVersion"
    leanGitHash := ← j.getObjValAs? _ "leanGitHash"
    imports := ← j.getObjValAs? _ "imports"
    commands := ← j.getObjValAs? _ "commands"
    runtimeReplacements := ← j.getObjValAs? _ "runtimeReplacements"
    replacementHistoryUnsupported := ← j.getObjValAs? _ "replacementHistoryUnsupported"
  }⟩



/-- Recheck source coordinates against exact transcript bytes using Lean's FileMap and LSP
UTF-16 columns, through `checked_coordinates`. This is a data-boundary check; it does not
authenticate how a worker acquired the bytes. -/
def validateCoordinates (declarations : Array Regula.Report.Declaration)
    (transcript : Transcript) : Except String Unit :=
  checked_coordinates.run Regula.lspUtf16Column declarations transcript

mutual
/-- The elements under a persistent-array node, left to right. -/
private def nodeElems {α : Type u} : PersistentArrayNode α → List α
  | .node ⟨children⟩ => nodesElems children
  | .leaf values => values.toList

private def nodesElems {α : Type u} : List (PersistentArrayNode α) → List α
  | [] => []
  | child :: children => nodeElems child ++ nodesElems children
end

/-- The elements of a persistent array in `toArray` order: the root's leaves left to right,
then the tail. Core computes `toArray` with the `partial` `foldlMAux`, which the kernel cannot
unfold, so the `InfoTree` traversals below recurse through this structural enumeration,
which follows `foldlMAux` case for case, and `sizeOf_lt_elems` bounds its members. -/
private def elems {α : Type u} (t : PersistentArray α) : List α := nodeElems t.root ++ t.tail.toList

mutual
private theorem sizeOf_lt_nodeElems {α : Type u} [SizeOf α] {x : α} :
    (n : PersistentArrayNode α) → x ∈ nodeElems n → sizeOf x < sizeOf n
  | .node ⟨children⟩, h => by
    have := sizeOf_lt_nodesElems children (by simpa [nodeElems] using h)
    simp; omega
  | .leaf values, h => by
    have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr (by simpa [nodeElems] using h))
    simp; omega

private theorem sizeOf_lt_nodesElems {α : Type u} [SizeOf α] {x : α} :
    (ns : List (PersistentArrayNode α)) → x ∈ nodesElems ns → sizeOf x < sizeOf ns
  | [], h => by simp [nodesElems] at h
  | n :: ns, h => by
    simp only [nodesElems, List.mem_append] at h
    rcases h with h | h
    · have := sizeOf_lt_nodeElems n h; simp; omega
    · have := sizeOf_lt_nodesElems ns h; simp; omega
end

private theorem sizeOf_lt_elems {α : Type u} [SizeOf α] {x : α} {t : PersistentArray α}
    (h : x ∈ elems t) : sizeOf x < sizeOf t := by
  rcases t with ⟨root, tail, _, _, _⟩
  simp only [elems, List.mem_append] at h
  rcases h with h | h
  · have := sizeOf_lt_nodeElems root h; simp; omega
  · have := Array.sizeOf_lt_of_mem (Array.mem_def.mpr h); simp; omega

/-- A child of an `InfoTree` node is smaller than the node: the termination measure of the
traversals below. -/
private theorem sizeOf_child_lt {i : Info} {children : PersistentArray InfoTree} {child : InfoTree}
    (h : child ∈ elems children) : sizeOf child < sizeOf (InfoTree.node i children) := by
  have := sizeOf_lt_elems h; simp; omega

/-- Keep every implementation selected in a command context, before later
attribute assignments can overwrite it. Nested command contexts matter: a
namespace's final environment is not its complete compilation history. -/
private def replacementRecords (tree : InfoTree)
    (seen : Array (Name × Name)) : Array (Name × Name) := Id.run do
  let mut seen := seen
  match tree with
  | .context (.commandCtx ctx) child =>
      for env in #[ctx.env] ++ ctx.cmdEnv?.toArray do
        for (reference, target) in
            (Lean.Compiler.implementedByAttr.ext.getState env).2.toArray do
          let edge := (reference, target)
          if !seen.contains edge then seen := seen.push edge
      return replacementRecords child seen
  | .context _ child => return replacementRecords child seen
  | .node _ children =>
      return (elems children).attach.foldl
        (fun seen ⟨child, _⟩ => replacementRecords child seen) seen
  | .hole _ => return seen
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

private def commandRecord? (tree : InfoTree) :
    Option (CommandContextInfo × CommandInfo) :=
  match tree with
  | .context (.commandCtx ctx) child =>
      match child with
      | .node (.ofCommandInfo info) _ => some (ctx, info)
      | other => commandRecord? other
  | .context _ child => commandRecord? child
  | .node _ children => (elems children).attach.findSome? fun ⟨child, _⟩ => commandRecord? child
  | .hole _ => none
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

private def position (p : Lean.Position) : Regula.Report.Position :=
  { line := p.line, column := p.column }

private def syntaxRange (fileMap : FileMap) (stx : Syntax) : Option SyntaxRange :=
  stx.getRange? (canonicalOnly := true) |>.map fun range =>
    { start := position <| fileMap.toPosition range.start
      «end» := position <| fileMap.toPosition range.stop }

/-- An evaluator is pinned when its elaborator is Lean's anonymous built-in
scaffolding, a syntax macro registered in the command's own environment
(macros are pure syntax transformations; their expansions produce their own
evaluator records and are audited in turn), or an elaborator registered for
that exact syntax kind in the module's post-import environment, i.e. by the
pinned toolchain or an explicitly imported library rather than by the audited
module itself. An attribute application is recorded as a command node whose
elaborator is the attribute implementation's `ref` (`Term.applyAttributesCore`);
it is pinned when `baselineAttribute` holds of that reference
(`baselineAttributeRefs`). -/
private def pinnedElaborator (baselineEnv commandEnv : Environment)
    (role : EvaluatorRole) (elaborator : Name) (kind : Name) (specializeSame := false)
    (baselineAttribute : Name → Bool := fun _ => false) : Bool :=
  if elaborator.isAnonymous then true
  else if role == .command && elaborator == `Lean.Compiler.specializeAttr &&
      #[`Lean.Parser.Attr.specialize, `specialize].contains kind then
    let registered := fun env =>
      (getAttributeImpl env `specialize).toOption.any (·.ref == elaborator)
    specializeSame && registered baselineEnv && registered commandEnv &&
      !(commandEnv.contains elaborator && (commandEnv.getModuleIdxFor? elaborator).isNone)
  else if role == .command && baselineAttribute elaborator then true
  else if (macroAttribute.getEntries commandEnv kind).any (·.declName == elaborator) then true
  else if role == .tactic then
    (Tactic.tacticElabAttribute.getEntries baselineEnv kind).any (·.declName == elaborator)
  else if role == .term then
    (Term.termElabAttribute.getEntries baselineEnv kind).any (·.declName == elaborator) ||
      -- `do` elements produce TermInfo too, but use their own keyed registry.
      (Do.doElemElabAttribute.getEntries baselineEnv kind).any (·.declName == elaborator)
  else
    (Command.commandElabAttribute.getEntries baselineEnv kind).any (·.declName == elaborator)

/-- Every information node carrying elaborator attribution participates, including
unfinished terms and alternative elaboration choices. -/
private def evaluatorInfo? : Info → Option (EvaluatorRole × ElabInfo)
  | .ofCommandInfo i => some (.command, i.toElabInfo)
  | .ofTacticInfo i => some (.tactic, i.toElabInfo)
  | .ofTermInfo i => some (.term, i.toElabInfo)
  | .ofPartialTermInfo i => some (.term, i.toElabInfo)
  | .ofChoiceInfo i => some (.term, i.toElabInfo)
  | _ => none

/-- The evaluator records of an information tree. A node is also pinned when an enclosing node
of the same role names the same elaborator and is pinned (`dispatched`): Lean's tactic framework
runs an elaborator with that name as the context's elaborator (`Tactic.Context.elaborator`, set
where `evalTactic` dispatches it for its own syntax kind), and every tactic information node the
elaborator records while it runs, such as one for the separators and sequence nodes of a tactic
block or the arguments `intro` introduces, carries that name with the node's own syntax
(`Tactic.mkTacticInfo`). -/
private def evaluatorRecords (baselineEnv commandEnv : Environment)
    (fileMap : FileMap) (tree : InfoTree) (specializeSame : Bool)
    (baselineAttribute : Name → Bool) (dispatched : Array (EvaluatorRole × Name) := #[]) :
    Array Evaluator :=
  match tree with
  | .context _ child =>
      evaluatorRecords baselineEnv commandEnv fileMap child specializeSame baselineAttribute
        dispatched
  | .node info children =>
      let (own, dispatched) : Array Evaluator × Array (EvaluatorRole × Name) :=
        match evaluatorInfo? info with
        | some (role, i) =>
            let inherited := dispatched.contains (role, i.elaborator)
            let pinned := inherited || pinnedElaborator baselineEnv commandEnv role
              i.elaborator i.stx.getKind specializeSame baselineAttribute
            (#[{
              role
              elaborator := i.elaborator
              kind := i.stx.getKind
              range := syntaxRange fileMap i.stx
              pinned
            }], if pinned && !inherited then dispatched.push (role, i.elaborator) else dispatched)
        | none => (#[], dispatched)
      (elems children).attach.foldl
        (fun acc ⟨child, _⟩ =>
          acc ++ evaluatorRecords baselineEnv commandEnv fileMap child specializeSame
            baselineAttribute dispatched) own
  | .hole _ => #[]
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

/-- Pinned predefinition elaboration records the exact constant binder at its
declaration identifier, including nested `where` definitions. -/
private def declarationBindings (fileMap : FileMap) (tree : InfoTree) :
    Array DeclarationBinding :=
  match tree with
  | .context _ child => declarationBindings fileMap child
  | .node info children =>
      let own := match info with
        | .ofTermInfo i => match i.expr with
          | .const name _ =>
            if i.isBinder then #[{ name := name, range := syntaxRange fileMap i.stx }]
            else #[]
          | _ => #[]
        | _ => #[]
      (elems children).attach.foldl
        (fun result ⟨child, _⟩ => result ++ declarationBindings fileMap child) own
  | .hole _ => #[]
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

/-- Whether a command's information tree records an `axiom` declaration: in the syntax of a
command it elaborates or in the output of a macro expansion. Lean records both nodes in a
`finally` step (`withInfoTreeContext`, `withInfoContext`), so the answer does not depend on
elaborating that declaration succeeding. -/
private def declaresAxiom (tree : InfoTree) : Bool :=
  match tree with
  | .context _ child => declaresAxiom child
  | .node info children =>
      let syntaxDeclaresAxiom := fun (stx : Syntax) =>
        (stx.find? (·.isOfKind ``Lean.Parser.Command.«axiom»)).isSome
      let own := match info with
        | .ofCommandInfo i => syntaxDeclaresAxiom i.stx
        | .ofMacroExpansionInfo i => syntaxDeclaresAxiom i.output
        | _ => false
      (elems children).attach.foldl (fun found ⟨child, _⟩ => found || declaresAxiom child) own
  | .hole _ => false
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

/-- Source metaprograms can compile with a temporary replacement and restore
the map within one command. Command snapshots cannot certify that history.
Imported trusted elaborators remain inside the documented process boundary. -/
private def unsupportedReplacementEvaluators (compilerEnv : Environment)
    (attributeRefs : Array Name)
    (baselineEnv commandEnv : Environment)
    (tree : InfoTree) : Array String :=
  match tree with
  | .context _ child =>
      unsupportedReplacementEvaluators compilerEnv attributeRefs baselineEnv commandEnv child
  | .node info children => Id.run do
      let evaluator? := (evaluatorInfo? info).map fun (role, i) =>
        (role, i.elaborator, i.stx.getKind)
      let own := match evaluator? with
        | some (role, elaborator, kind) =>
            let scaffold := elaborator == `header || elaborator == `import
            -- Helpers and attribute parameters can report synthetic syntax
            -- kinds. Resolve their declaration against the pinned compiler or
            -- the source's actual imports; a source-local override is not that
            -- trusted declaration. This does not relax generated-role policy.
            let sourceLocal := commandEnv.contains elaborator &&
              (commandEnv.getModuleIdxFor? elaborator).isNone
            let trustedCode := !sourceLocal &&
              (compilerEnv.contains elaborator || attributeRefs.contains elaborator ||
                (commandEnv.getModuleIdxFor? elaborator).isSome)
            if #[`Lean.Elab.Command.elabRunCmd, `Lean.Elab.Command.elabRunMeta,
                `Lean.Elab.Command.elabRunElab, `Lean.Elab.Term.elabRunElab,
                `Lean.Elab.Tactic.evalRunTac].contains elaborator
                || (!scaffold && !trustedCode &&
                  !pinnedElaborator baselineEnv commandEnv role elaborator kind) then
              #[s!"{role}: {elaborator} ({kind})"]
            else #[]
        | none => #[]
      return (elems children).attach.foldl (fun found ⟨child, _⟩ =>
        found ++ unsupportedReplacementEvaluators compilerEnv attributeRefs baselineEnv commandEnv
            child) own
  | .hole _ => #[]
termination_by tree
decreasing_by all_goals first | exact sizeOf_child_lt ‹_› | (simp_wf; omega)

private def constantKind : ConstantInfo → RegulaPolicy.DeclarationKind
  | .axiomInfo _  => .axiom
  | .defnInfo _   => .definition
  | .thmInfo _    => .theorem
  | .opaqueInfo _ => .opaque
  | .ctorInfo _   => .constructor
  | .inductInfo _ => .inductive
  | .recInfo _    => .recursor
  | .quotInfo _   => .quotient

private def constantRecord (env : Environment) (name : Name) : AddedDeclaration :=
  let info := env.constants.find! name
  { name := name
    kind := constantKind info
    «type» := toString (repr info.type)
    nativeStatement := Regula.Collect.nativeStatement? name info.type }

/-- Whether the attribute `name` of `commandEnv` is the implementation object the module's
post-import `baselineEnv` registers under that name. -/
private unsafe def baselineAttribute (baselineEnv commandEnv : Environment) (name : Name) :
    Bool :=
  match getAttributeImpl baselineEnv name, getAttributeImpl commandEnv name with
  | .ok baseline, .ok current => ptrEq baseline current
  | _, _ => false

/-- The references (`AttributeImpl.ref`) that only attributes `commandEnv` registers exactly
as `baselineEnv` does carry: an application recorded with such a reference ran an attribute of the
pinned toolchain or an imported library. A reference also carried by an attribute the module
added or replaced is excluded, since the recorded name then does not determine which
implementation ran. -/
private unsafe def baselineAttributeRefs (baselineEnv commandEnv : Environment) : NameSet :=
  let (pinned, spoiled) := (getAttributeNames commandEnv).foldl
    (fun ((pinned, spoiled) : NameSet × NameSet) name =>
      match getAttributeImpl commandEnv name with
      | .ok current =>
          if baselineAttribute baselineEnv commandEnv name then (pinned.insert current.ref, spoiled)
          else (pinned, spoiled.insert current.ref)
      | .error _ => (pinned, spoiled))
    ({}, {})
  spoiled.foldl (fun pinned ref => pinned.erase ref) pinned

/-- `Command.sourceLocalOverrides`: the declarations of the macros and term, tactic, command and
`do`-element elaborators the audited module declared and registered (`KeyedDeclsAttribute` entries
whose declaration belongs to the current module) for a syntax kind that is not one of its own
declarations, then the attributes of `commandEnv` that are not `baselineEnv`'s objects. A
notation or syntax the module declares together with its own macro is not an override:
Lean-generated syntax cannot have its kind. -/
private unsafe def sourceLocalOverrides (baselineEnv commandEnv : Environment) : Array Name :=
  let declaredHere := fun (name : Name) =>
    commandEnv.contains name && (commandEnv.getModuleIdxFor? name).isNone
  let overriding := fun (entries : List KeyedDeclsAttribute.OLeanEntry) =>
    entries.filterMap fun entry =>
      if declaredHere entry.declName && !declaredHere entry.key then some entry.declName else none
  let elaborators := overriding (macroAttribute.ext.getState commandEnv).newEntries ++
    overriding (Term.termElabAttribute.ext.getState commandEnv).newEntries ++
    overriding (Tactic.tacticElabAttribute.ext.getState commandEnv).newEntries ++
    overriding (Command.commandElabAttribute.ext.getState commandEnv).newEntries ++
    overriding (Do.doElemElabAttribute.ext.getState commandEnv).newEntries
  let attributes := (getAttributeNames commandEnv).filter
    (!baselineAttribute baselineEnv commandEnv ·)
  RegulaPolicy.canonicalNames (elaborators ++ attributes).toArray

/-- In ordinary command snapshots, only the local map can gain declarations.
When pointer identity confirms the same immutable imported map allocation, scan
only local declarations; otherwise preserve the complete environment difference. -/
private unsafe def newConstants (before after : Environment) : Array Name :=
  let previous := before.constants
  let current := after.constants
  let collect := fun (names : Array Name) name (_ : ConstantInfo) =>
    if previous.contains name then names else names.push name
  if !previous.stage₁ && !current.stage₁ && ptrEq previous.map₁ current.map₁ then
    current.foldStage2 collect #[]
  else
    current.fold collect #[]

/-- Elaborate one exact source from a fresh frontend state and return the
first-introduction transcript. Any diagnostic error or concurrent source
change fails the call. Regula's local feedback is always off here through the audit-build
marker, as in the `lint` driver's claimed build (`Lake.auditLeanOptions`), whatever the source
sets `linter.regula` to (`Regula.Linter.liveFeedback_auditBuild`); the marker is unregistered and
`weak.`, so every command scope elaborates exactly as without it. -/
private unsafe def buildCore (moduleName : Name) (sourcePath : System.FilePath)
    (history : Bool := false) : IO Transcript := do
  unsafe Lean.enableInitializersExecution
  let sourceBefore ← IO.FS.readFile sourcePath
  -- A separate metadata environment identifies pinned elaborator helpers;
  -- these imports are not added to the source being re-elaborated.
  let compilerEnv ← Lean.importModules #[{ module := `Lean, importAll := true }] {} 0
    (loadExts := true) (level := .private)
  let compilerEnv? := if history then some compilerEnv else none
  unsafe Lean.enableInitializersExecution
  let attributeRefs := (← Lean.attributeMapRef.get).toArray.map (·.2.ref)
  let inputCtx := Parser.mkInputContext sourceBefore sourcePath.toString
  let ctx := { inputCtx with }
  let opts := (Lean.Elab.async.set (warningAsError.set {} true) false).setBool
      Regula.Linter.auditBuildOption true
  let processor := Lean.Language.Lean.process
  let importsRef ← IO.mkRef (#[] : Array Import)
  let snap ← processor (fun stx => do
    importsRef.set stx.imports
    return Except.ok {
      imports := stx.imports
      isModule := stx.isModule
      mainModuleName := moduleName
      opts
      trustLevel := 0
      plugins := #[]
    }) none ctx
  let snapshots := Lean.Language.toSnapshotTree snap
  let hasErrors ← snapshots.runAndReport opts false
  if hasErrors then
    throw <| IO.userError s!"fresh frontend elaboration failed for {moduleName}"
  let imports ← importsRef.get
  let mut before? : Option Environment := none
  let mut baseline? : Option Environment := none
  let mut commands : Array Command := #[]
  let mut runtimeReplacements : Array (Name × Name) := #[]
  let mut replacementHistoryUnsupported : Array String := #[]
  for snapshot in snapshots.getAll do
    if let some tree := snapshot.infoTree? then
      if history then runtimeReplacements := replacementRecords tree runtimeReplacements
      if let some (commandCtx, info) := commandRecord? tree then
        if baseline?.isNone then
          baseline? := some commandCtx.env
        if let some compilerEnv := compilerEnv? then
          for evaluator in unsupportedReplacementEvaluators compilerEnv attributeRefs
              (baseline?.getD commandCtx.env)
              commandCtx.env tree do
            if !replacementHistoryUnsupported.contains evaluator then
              replacementHistoryUnsupported := replacementHistoryUnsupported.push evaluator
        if let some after := commandCtx.cmdEnv? then
          if let some before := before? then
            let added := newConstants before after
            if !added.isEmpty then
              -- Attribute refs are navigation metadata. Require the actual
              -- immutable registered handler object from the compiler baseline,
              -- not a source replacement retaining its name/ref.
              let specializeSame := match (getAttributeImpl compilerEnv `specialize),
                  (getAttributeImpl (baseline?.getD commandCtx.env) `specialize),
                  (getAttributeImpl commandCtx.env `specialize) with
                | .ok expected, .ok baseline, .ok current =>
                    ptrEq expected baseline && ptrEq expected current
                | _, _, _ => false
              let baseline := baseline?.getD commandCtx.env
              let attributeRefs := baselineAttributeRefs baseline commandCtx.env
              commands := commands.push {
                commandElaborator := info.elaborator
                commandKind := info.stx.getKind
                commandRange := syntaxRange commandCtx.fileMap info.stx
                added := added
                addedDeclarations := added.map (constantRecord after)
                evaluators := evaluatorRecords baseline commandCtx.env commandCtx.fileMap tree
                  specializeSame attributeRefs.contains
                bindings := declarationBindings commandCtx.fileMap tree
                declaresAxiom := declaresAxiom tree
                sourceLocalOverrides := sourceLocalOverrides baseline commandCtx.env
              }
          before? := some after
        else if before?.isNone then
          before? := some commandCtx.env
  let sourceAfter ← IO.FS.readFile sourcePath
  if sourceAfter != sourceBefore then
    throw <| IO.userError s!"source changed during frontend transcript: {sourcePath}"
  return {
    «module» := moduleName
    source := sourcePath.toString
    sourceBytes := sourceBefore.toUTF8.size
    sourceContent := sourceBefore
    leanVersion := Lean.versionString
    leanGitHash := Lean.githash
    imports := imports.map fun item => {
      «module» := item.module
      importAll := item.importAll
      isExported := item.isExported
      isMeta := item.isMeta
    }
    commands
    runtimeReplacements
    replacementHistoryUnsupported
  }

/-- Elaborate with the already configured module search path. A caller may use
this variant while it owns one read-only search-path scope for bounded workers. -/
unsafe def buildCurrentSearchPath (moduleName : Name)
    (sourcePath : System.FilePath) : IO Transcript :=
  buildCore moduleName sourcePath

/-- Source-history worker variant; it additionally resolves operational
elaborator attribution and records overwritten implementation targets. -/
unsafe def buildReplacementHistoryCurrentSearchPath (moduleName : Name)
    (sourcePath : System.FilePath) : IO Transcript :=
  buildCore moduleName sourcePath true

/-- Run `buildCore` with any freshly built package search roots taking
precedence, then restore the executable's original search path. -/
unsafe def build (moduleName : Name) (sourcePath : System.FilePath)
    (extraSearchRoots : Array System.FilePath := #[]) : IO Transcript := do
  let oldSearchPath ← Lean.searchPathRef.get
  Lean.searchPathRef.set (extraSearchRoots.toList ++ oldSearchPath)
  try buildCore moduleName sourcePath
  finally Lean.searchPathRef.set oldSearchPath

/-- The request a `--frontend-worker` process reads: which module to elaborate, from which
source file, with which extra search roots first. -/
structure WorkerRequest where
  /-- The module name the source is elaborated as. -/
  moduleName : Name
  /-- The path of the source file to elaborate. -/
  source : String
  /-- Search roots placed before the worker's own search path, such as freshly built
  package outputs. -/
  searchRoots : Array String
  deriving ToJson

instance : FromJson WorkerRequest := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["moduleName", "source", "searchRoots"]
  return {
    moduleName := ← j.getObjValAs? _ "moduleName"
    source := ← j.getObjValAs? _ "source"
    searchRoots := ← j.getObjValAs? _ "searchRoots"
  }⟩

/-- Release the frontend's persistent imported environments on worker exit. -/
def buildIsolated (moduleName : Name) (sourcePath : System.FilePath)
    (extraSearchRoots : Array System.FilePath := #[]) : IO Transcript := do
  let sourceBefore ← IO.FS.readFile sourcePath
  let transcript : Transcript ← runTypedWorker "--frontend-worker" ({
    moduleName, source := sourcePath.toString,
    searchRoots := extraSearchRoots.map (·.toString)
  } : WorkerRequest)
  unless transcript.module == moduleName && transcript.source == sourcePath.toString &&
      transcript.sourceContent == sourceBefore && transcript.sourceBytes ==
          sourceBefore.utf8ByteSize &&
      transcript.leanVersion == Lean.versionString && transcript.leanGitHash == Lean.githash &&
      (← IO.FS.readFile sourcePath) == sourceBefore do
    throw <| IO.userError "frontend worker snapshot or toolchain binding mismatch"
  return transcript

end Regula.Checker.Frontend
