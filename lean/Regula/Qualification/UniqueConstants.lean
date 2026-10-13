import Regula.Qualification.Support
import Regula.Checker.Acceptance
import Regula.Checker.Inspection
import Std.Data.HashMap.Lemmas

/-! # One declaring module for each constant of a claimed environment

A check of the first acceptance step (`qualify combined`) on this repository's own code, not a
rule of the standard. Lean realizes an equation lemma, or another constant it derives on demand,
in the first module that needs it, so two modules that do not import each other can each declare
a copy of one constant. The project audit reuses an admitted module in a later environment only
when the copies of its names agree (`Admission.copiesAgree`, `Admission.agrees`). The copies of a
name agree when each is `Identical` to the constant that environment keeps, whichever modules
declare it. They also agree when owned modules alone declare the name (`Admission.declaredOwned`)
and each copy is the copy of the module the name is attributed to up to exchanging names private
to the module that declares it, which only that copy and those names use
(`Admission.uniformUpToPrivate`). An environment offers a module holding a shared copy only when
those copies agree and owned modules alone declare the name (`Admission.ownedAgrees`).
An environment that loads two copies that do not agree, or a copy that a toolchain or
trusted-dependency module also declares, therefore replays a module again, and every module that
imports it.

The check refuses each constant that two modules of one claimed environment declare, where one of
them is a module of the root package. The environments are those the audit inspects
(`Acceptance.surfaceAssignments`, `Inspection.surfaceEnvironments`), each imported as the audit's
workers import it, with the probe and every import's private data. The check decides no claim of
the audit and changes no reuse decision; it keeps Regula's own claimed code from defeating that
reuse. `shared` is the executed decision, and `mem_shared` states what it gives. -/

namespace Regula.Qualification.UniqueConstants
open Lean System Regula.Checker

/-- The modules of `modules` that declare `constant`, in order, once for each time a module's
list of declared constants gives it. -/
def declarers (modules : List (Name × List Name)) (constant : Name) : List Name :=
  modules.flatMap fun (module, constants) =>
    (constants.filter (· == constant)).map fun _ => module

/-- The modules declaring each constant of `modules`, collected in one pass. -/
def declaredBy (modules : List (Name × List Name)) : Std.HashMap Name (List Name) :=
  modules.foldl (init := ∅) fun declared (module, constants) =>
    constants.foldl (init := declared) fun declared constant =>
      declared.alter constant fun found => some (found.getD [] ++ [module])

/-- Whether the declarers `found` of one constant are more than one module, one of them `own`. -/
def Shared (own : NameSet) (found : List Name) : Prop :=
  1 < found.length ∧ ∃ module ∈ found, own.contains module = true

instance (own : NameSet) (found : List Name) : Decidable (Shared own found) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Each constant that more than one of `modules` declares, one of them `own`, with its
declaring modules. `modules` holds each loaded module with the constants it declares. -/
def shared (own : NameSet) (modules : List (Name × List Name)) : List (Name × List Name) :=
  (declaredBy modules).toList.filter fun (_, found) => decide (Shared own found)

/-- The declarers `found` of one constant as `declaredBy` holds them: none when no module declares
it. -/
def listed (found : List Name) : Option (List Name) :=
  if found = [] then none else some found

private theorem lookup_inner (module constant : Name) (constants : List Name)
    (declared : Std.HashMap Name (List Name)) (before : List Name)
    (h : declared[constant]? = listed before) :
    (constants.foldl (init := declared) fun declared c =>
        declared.alter c fun found => some (found.getD [] ++ [module]))[constant]? =
      listed (before ++ (constants.filter (· == constant)).map fun _ => module) := by
  induction constants generalizing declared before with
  | nil => simpa using h
  | cons c rest ih =>
    simp only [List.foldl_cons]
    by_cases same : c = constant
    · subst same
      have := ih (declared.alter c fun found => some (found.getD [] ++ [module]))
        (before ++ [module])
        (by simp [h, listed]; split <;> simp_all)
      simpa [List.filter_cons] using this
    · have := ih (declared.alter c fun found => some (found.getD [] ++ [module])) before
        (by simp [Std.HashMap.getElem?_alter, same, h])
      simpa [List.filter_cons, same] using this

private theorem lookup_outer (modules : List (Name × List Name)) (constant : Name)
    (declared : Std.HashMap Name (List Name)) (before : List Name)
    (h : declared[constant]? = listed before) :
    (modules.foldl (init := declared) fun declared (module, constants) =>
        constants.foldl (init := declared) fun declared c =>
          declared.alter c fun found => some (found.getD [] ++ [module]))[constant]? =
      listed (before ++ declarers modules constant) := by
  induction modules generalizing declared before with
  | nil => simpa [declarers] using h
  | cons entry rest ih =>
    obtain ⟨module, constants⟩ := entry
    simp only [List.foldl_cons]
    have := ih _ _ (lookup_inner module constant constants declared before h)
    simpa [declarers, List.flatMap_cons, List.append_assoc] using this

/-- `declaredBy` finds a constant's declarers, and only for a constant some module declares. -/
theorem declaredBy_getElem? (modules : List (Name × List Name)) (constant : Name) :
    (declaredBy modules)[constant]? = listed (declarers modules constant) := by
  unfold declaredBy
  simpa using lookup_outer modules constant ∅ [] (by simp [listed])

/-- `shared` gives exactly each constant whose declarers in `modules` are shared, with those
declarers: so it is empty exactly when no constant of `modules` is declared by two of them where
one is `own`. -/
theorem mem_shared (own : NameSet) (modules : List (Name × List Name)) (constant : Name)
    (found : List Name) :
    (constant, found) ∈ shared own modules ↔
      found = declarers modules constant ∧ Shared own found := by
  simp only [shared, List.mem_filter, Std.HashMap.mem_toList_iff_getElem?_eq_some,
    declaredBy_getElem?, decide_eq_true_eq, listed]
  constructor
  · rintro ⟨h, s⟩
    split at h <;> simp_all
  · rintro ⟨rfl, s⟩
    refine ⟨?_, s⟩
    have : declarers modules constant ≠ [] := by
      intro e; simp [Shared, e] at s
    simp [this]

/-- `shared` is empty exactly when no constant has shared declarers. -/
theorem shared_eq_nil (own : NameSet) (modules : List (Name × List Name)) :
    shared own modules = [] ↔ ∀ constant, ¬ Shared own (declarers modules constant) := by
  constructor
  · intro h constant s
    have := (mem_shared own modules constant _).mpr ⟨rfl, s⟩
    simp [h] at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨constant, found⟩ m
    obtain ⟨rfl, s⟩ := (mem_shared own modules constant found).mp m
    exact h constant s

/-- One compiled module as its `.olean` parts give it: the modules it imports, whatever the marks
of each import, and each constant that any of its parts declares, once. -/
structure ModuleFacts where
  /-- The modules the module imports. -/
  imports : Array Name
  /-- The constants of the module's exported, server and private parts, each once. -/
  constants : List Name

/-- The facts of `module`, read from every `.olean` part Lean's import reads for it (the exported
part, and when its server part exists its server and private parts), each once; a module-system
file must have all three parts and any other only the exported one, as `importModules` reads them.
The parts stay loaded: the names point into them. -/
def readFacts (module : Name) : IO ModuleFacts := do
  let olean ← findOLean module
  unless ← olean.pathExists do
    throw <| IO.userError s!"unique-constants: {module} has no .olean at {olean}"
  let server := OLeanLevel.server.adjustFileName olean
  let files := if ← server.pathExists then
      #[olean, server, OLeanLevel.private.adjustFileName olean]
    else #[olean]
  let parts ← readModuleDataParts files
  let some (main, _) := parts[0]?
    | throw <| IO.userError s!"unique-constants: {olean} could not be read"
  unless (parts.size == 3) == main.isModule do
    throw <| IO.userError s!"unique-constants: {module} has {parts.size} .olean parts, but its \
      exported part says isModule := {main.isModule}"
  let names := parts.foldl (fun names (data, _) =>
    data.constNames.foldl NameSet.insert names) ({} : NameSet)
  return { imports := main.imports.map (·.module), constants := names.toList }

/-- The modules of the import closure of `roots` and the probe module, each with its constants,
reading each module once across calls through `cache`. An audit worker imports these roots and
the probe (`Checker.Environment`), and every module it loads is in this closure with constants
from one of the parts read here: so every constant two loaded modules of the audit's environment
declare is one that two of these modules declare. -/
def closureFacts (cache : IO.Ref (Std.HashMap Name ModuleFacts)) (roots : Array Name) :
    IO (List (Name × List Name)) := do
  let probe := Checker.Environment.probeModuleName.toName
  let mut pending := (if roots.contains probe then roots else roots.push probe).toList
  let mut seen : NameSet := {}
  let mut result : Array (Name × List Name) := #[]
  while true do
    match pending with
    | [] => break
    | module :: rest =>
      pending := rest
      if seen.contains module then continue
      seen := seen.insert module
      let facts ← match (← cache.get)[module]? with
        | some facts => pure facts
        | none => do
          let facts ← readFacts module
          cache.modify (·.insert module facts)
          pure facts
      result := result.push (module, facts.constants)
      pending := facts.imports.toList ++ pending
  return result.toList

/-- The check that `qualify unique-constants` and `qualify combined` run from the package root:
each environment the project audit inspects (`Inspection.surfaceEnvironments` over
`Acceptance.surfaceAssignments`, the coordinator's own functions), read with `closureFacts`, and
`shared` over it, with the root package's modules as `own`. It prints each shared constant with
its declaring modules and throws, or prints `PASS` with the counts. -/
def check : IO Unit := do
  let root ← Qualification.rootDirectory
  initializeLeanSearchPath
  let inventory ← Lake.surfaceInventory root
  let manifest ← Manifest.loadFor (Manifest.defaultPath root) inventory
  let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  let libraries ← Inspection.manifestedLibraries manifest inventory
  let environments ← Inspection.surfaceEnvironments manifest inventory assignments libraries
  let own := (inventory.targets.flatMap (·.modules)).foldl NameSet.insert {}
  let cache ← IO.mkRef ({} : Std.HashMap Name ModuleFacts)
  let mut constants := 0
  let mut refused := 0
  for environment in environments do
    let modules ← closureFacts cache environment.info.modules
    constants := modules.foldl (fun total (_, declared) => total + declared.length) constants
    for (constant, found) in shared own modules do
      refused := refused + 1
      IO.eprintln s!"unique-constants: {environment.label}: {constant} is declared by {found}"
  if refused != 0 then
    throw <| IO.userError s!"unique-constants: {refused} occurrences, counted once per \
      environment, of a constant declared by two modules of one environment where one is a \
      root-package module; realize each once, in a module that every user imports"
  IO.println s!"unique-constants: PASS (no constant declared by two modules of one environment \
    where one is a root-package module; {environments.size} environments, {constants} constant \
    declarations counted once per environment)"

end Regula.Qualification.UniqueConstants
