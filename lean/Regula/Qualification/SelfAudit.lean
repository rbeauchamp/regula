import Regula.Checker.Admission
import Regula.Checker.Lake
import Regula.Collect
import Regula.Linter.Documentation
import Regula.ToolchainProgram
import RegulaPolicy.Operational

/-! # Checker library self-audit

Operational self-audit of the checker's own excluded `Regula` library
(`./scripts/verify.sh diagnostics self-audit`; docs/guides/contributing.md).

The library is not a conforming proof surface, so the project audit excludes it. This
campaign applies the rules that do hold for operational code, per module of the library as
Lake discovers it: completed kernel admission of every owned safe declaration (RG2005), the
executed `RegulaPolicy.checked_operationalFailure` decision (RG1001–RG1005, RG1007, RG1009) on the
observations the live linter's shared collector (`Regula.Collect.declaration`) constructs, with the
axioms each declaration reaches in the kernel that admission replayed (`Admission.validate`), the
executed `RegulaPolicy.checked_decisionFailure` decision (RG1008) against the decision contracts
the same module registers (`RegulaPolicy.decidedImplementations` of the recorded contracts of its
declarations), and the live linter's module-header (RG5001: docstring present and first, no
repeated import) and material-documentation presence predicates
(`Regula.Linter.Documentation`, RG5001–RG5003). Authored `unsafe`/`partial` declarations, the
pinned toolchain's Lake axioms that in-process Lake APIs reach, and the axioms Lean's
`collectAxioms` omits for a declaration are reported, never failed.

Each module is imported alone, because several executable roots of the library each define
`main` and cannot share one environment. Warning-free elaboration (RG2003) is the preceding
`lake build Regula` step of the same campaign. Trusted, not verified: Lean's import, kernel
replay and pretty-printer, the collector's observations, and the olean paths that identify a
toolchain module. -/
namespace Regula.Qualification.SelfAudit

open Lean System RegulaPolicy

/-- The excluded operational library this campaign audits. -/
def library : String := "Regula"

/-- The report claim label: the operational decision, never a conforming profile. -/
def claim : String := "operational"

/-! ### Shards

`qualify self-audit --shard i/4` audits the modules of the `i`th of four shards, and the dogfood
workflow runs each shard as a job of its own, under the deadline of its own invocation. Each list
of modules the campaign inspects is sorted by name and dealt in turn: the module at position `i`,
counted from 0, is in shard `i % shards`. So the shard of a module depends on the set of modules
alone, not on the order Lake discovers them in, and each shard gets a quarter of each list. -/

/-- The number of shards of the campaign (`RegulaVerification.selfAuditShards` repeats it). -/
def shards : Nat := 4

/-- The items of `items`, each with its shard: the item at position `i`, counted from 0, is in
shard `i % shards`. -/
def dealt {α : Type} (items : List α) : List (Fin shards × α) :=
  items.mapIdx fun index item => (⟨index % shards, Nat.mod_lt _ (by decide)⟩, item)

/-- The items that `shard` audits: those `dealt` to it, or every item without a shard
(`Checker.inShard`). -/
def selected {α : Type} (shard : Option (Fin shards)) (items : List α) : List α :=
  (Checker.inShard shard (dealt items)).map (·.2)

/-- Without a shard the campaign audits every item, in its order. -/
theorem selected_none {α : Type} (items : List α) : selected none items = items := by
  apply List.ext_getElem <;> simp [selected, Checker.inShard, dealt]

/-- Every item is audited in exactly one shard: the selections of the four shards, in their order,
are together a rearrangement of the items, which an unsharded run audits (`Checker.inShard_cover`).
This is a statement about the selection; that the shards' jobs select from the same list rests on
their discovering the same modules from the same sources, which it does not state. -/
theorem selected_cover {α : Type} (items : List α) :
    ((List.finRange shards).flatMap fun shard => selected (some shard) items).Perm items := by
  have cover := (Checker.inShard_cover _ (List.nodup_finRange shards) List.mem_finRange
    (dealt items)).map Prod.snd
  have none_eq : (Checker.inShard none (dealt items)).map Prod.snd = items := selected_none items
  rw [List.map_flatMap, none_eq] at cover
  exact cover

/-- The spelling of a shard on the command line: `INDEX/4`, `INDEX` counted from 1. -/
def shardLabel (shard : Fin shards) : String := s!"{shard.val + 1}/{shards}"

/-- The shard that `--shard spec` selects: exactly one of the four labels, so `01/4` and `5/4` are
refused (`shardOf?_sound`, `shardOf?_label`). -/
def shardOf? (spec : String) : Option (Fin shards) :=
  (List.finRange shards).find? fun shard => spec == shardLabel shard

/-- A selected shard is the one whose label the argument is. -/
theorem shardOf?_sound (spec : String) (shard : Fin shards) (h : shardOf? spec = some shard) :
    spec = shardLabel shard := by
  simpa using List.find?_some h

/-- Every shard is selected by its label. -/
theorem shardOf?_label (shard : Fin shards) : shardOf? (shardLabel shard) = some shard := by
  revert shard; decide

/-- The names of `modules` in order of their text, which `dealt` deals. -/
def byName (modules : Array Name) : List Name :=
  (modules.qsort (·.toString < ·.toString)).toList

/-- Observations of one module in its own imported environment. -/
structure ModuleObservation where
  /-- The observed module. -/
  «module» : Name
  /-- The collected record of every constant the module owns, in `ownedConstants` order. -/
  declarations : Array RegulaPolicy.Declaration
  /-- The constants of this module's own data, neither `unsafe` nor `partial`, that kernel
  admission admitted; a realized copy that `ownedConstants` attributes to an imported module is
  counted here too. -/
  admitted : Nat
  /-- Axioms reached from this module that a toolchain `Lake` module declares. -/
  toolchain : Array Name
  /-- The module's RG5001 header observation, read from its Lake source file. -/
  header : RegulaPolicy.ModuleHeader.Observation
  /-- Each public `@[regula_material]` declaration the module owns, with its RG5002/RG5003
  documentation failure, or `none` when its docstring passes. -/
  material : Array (Name × Option MaterialDocumentationFailure)
  /-- The finding texts of the comparison rule and of the absence rule for the module
  (`ruleFindings`). -/
  ruleFindings : Array String

/-- Whether `owner`'s artifact is the pinned toolchain's own `Lake` module. -/
private def toolchainLakeModule (toolchainLib : FilePath) (owner : Name) : IO Bool := do
  unless owner.getRoot == `Lake do return false
  let expected := modToFilePath toolchainLib owner "olean"
  unless ← Regula.Filesystem.isPresent expected do return false
  return (← IO.FS.realPath (← findOLean owner)) == (← IO.FS.realPath expected)

/-! ### Comparisons of `Json` values

Lean's equality of `Json` is one-sided for two objects: it looks each member of the first up in
the second, so a first object tree that is not a search tree can repeat one name and lack another
(https://github.com/rbeauchamp/regula/issues/269). A received value is therefore compared with
`Regula.JsonAgreement.conforms`, or read as a string, number or Boolean first. The campaign
refuses each other declaration that compares `Json` values, unless both operands are values that
Regula builds and the allowlist names it with that reason.

What the check finds: each use of Lean's `BEq Json` instance, completely, since such a use names
the instance (`Lean.Json.instBEq`), the only public way to its private `Json.beq'`; and each
`BEq.beq`, `bne` or `Eq` whose compared operand contains `Json.compress`, directly or through
`let` bindings. It does not find a comparison of texts that a named helper or a function argument
renders, nor one through a `BEq` instance that Lean or a dependency declares for a type with a
`Json` field. The guarantee that received values are compared through `conforms` rests on the
conversions of #269 and the theorems about `conforms`; this check is the tripwire for a new use of
the `BEq` form. -/

/-- The declarations that keep Lean's equality of `Json`, each by its module and its name, with its
reason. The module is part of the key: each executable root declares its own `main`. -/
def jsonComparisonAllowlist : Array (Name × Name × String) := #[
  (`Regula.Checker.Snapshot, `Regula.Checker.Snapshot.legacyBeq,
    "compares the field state of two dependency observations; the field state_sound proves each \
      is stateOfCore of the observation's captures, a value Regula builds"),
  (`Regula.RegistryChecks, `main,
    "the registry self-check executable: each operand is a value it builds with the encoders, \
      Json.mkObj or Json.setObjVal!, or that its own decoders read back from such a value")]

/-- The entries of `jsonComparisonAllowlist` whose module is not one of `inspected`, the modules
the campaign inspects (`mem_uninspectedEntries`). `jsonFindings` reads an entry only for its own
module, so the finding of an entry whose declaration compares no `Json` values never reaches such
an entry; this finds it instead. -/
def uninspectedEntries (inspected : Array Name) : Array (Name × Name) :=
  (jsonComparisonAllowlist.filter fun (m, _, _) => !inspected.contains m).map
    fun (m, n, _) => (m, n)

/-- An entry is found exactly when the allowlist has it, with some reason, and its module is not
inspected. -/
theorem mem_uninspectedEntries {inspected : Array Name} {m n : Name} :
    (m, n) ∈ uninspectedEntries inspected ↔
      (∃ reason, (m, n, reason) ∈ jsonComparisonAllowlist) ∧ m ∉ inspected := by
  simp only [uninspectedEntries, Array.mem_map, Array.mem_filter, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.eq_false_iff, ne_eq, Array.contains_iff_mem, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨m', n', reason, ⟨present, absent⟩, rfl, rfl⟩
    exact ⟨⟨reason, present⟩, absent⟩
  · rintro ⟨⟨reason, present⟩, absent⟩
    exact ⟨m, n, reason, ⟨present, absent⟩, rfl, rfl⟩

/-- The finding text for an entry of `jsonComparisonAllowlist` whose module is not inspected. -/
def uninspectedEntryText (entry : Name × Name) : String :=
  s!"json-comparison: {entry.2} ({entry.1}) is in jsonComparisonAllowlist but the campaign \
    inspects no module {entry.1}; remove the entry"

/-- The answers `rendersIn` and `comparesJsonIn` have given, by question, term and the part of the
binder context that the term can read. Lean shares subterms, so a term without this table is a tree
far larger than the term itself. -/
abbrev ComparisonTable := Std.HashMap (Bool × Expr × List Nat) Bool

/-- The rendering indices under one more binder, which renders when `bound` holds. -/
def underBinder (bound : Bool) (carries : List Nat) : List Nat :=
  let shifted := carries.map (· + 1)
  if bound then 0 :: shifted else shifted

/-- Whether `e` contains `Json.compress`, directly or through a bound variable: `carries` lists the
de Bruijn indices of the loose bound variables that are `let`-bound to such a term, usually none. -/
def rendersIn (carries : List Nat) (e : Expr) : StateM ComparisonTable Bool := do
  let key := (false, e, carries.filter (· < e.looseBVarRange))
  if let some known := (← get)[key]? then return known
  let answer ← match e with
    | .const name _ => pure (name == ``Lean.Json.compress)
    | .bvar index => pure (carries.contains index)
    | .app f a => return (← rendersIn carries f) || (← rendersIn carries a)
    | .lam _ type body _ | .forallE _ type body _ =>
      return (← rendersIn carries type) || (← rendersIn (carries.map (· + 1)) body)
    | .letE _ type value body _ =>
      let bound ← rendersIn carries value
      return (← rendersIn carries type) || bound || (← rendersIn (underBinder bound carries) body)
    | .mdata _ e | .proj _ _ e => rendersIn carries e
    | _ => pure false
  modify (·.insert key answer)
  return answer

/-- Whether `e` compares `Json` values with Lean's equality: it names the `BEq Json` instance, or it
applies `BEq.beq`, `bne` or `Eq` to an operand that `rendersIn`; `carries` is as for `rendersIn`. -/
def comparesJsonIn (carries : List Nat) (e : Expr) : StateM ComparisonTable Bool := do
  let key := (true, e, carries.filter (· < e.looseBVarRange))
  if let some known := (← get)[key]? then return known
  let answer ← match e with
    | .const name _ => pure (name == ``Lean.Json.instBEq)
    | .app f a =>
      let comparison := e.isAppOfArity ``BEq.beq 4 || e.isAppOfArity ``bne 4 ||
        e.isAppOfArity ``Eq 3
      let left ← match f with
        | .app _ left => rendersIn carries left
        | _ => pure false
      let operands := left || (← rendersIn carries a)
      return comparison && operands || (← comparesJsonIn carries f) ||
        (← comparesJsonIn carries a)
    | .lam _ type body _ | .forallE _ type body _ =>
      return (← comparesJsonIn carries type) || (← comparesJsonIn (carries.map (· + 1)) body)
    | .letE _ type value body _ =>
      let bound ← rendersIn carries value
      return (← comparesJsonIn carries type) || (← comparesJsonIn carries value) ||
        (← comparesJsonIn (underBinder bound carries) body)
    | .mdata _ e | .proj _ _ e => comparesJsonIn carries e
    | _ => pure false
  modify (·.insert key answer)
  return answer

/-- Whether the closed term `e` compares `Json` values (`comparesJsonIn`). Lean's `Expr.find?`, which
visits each shared subterm one time, finds a use of the instance and decides if `e` mentions
`Json.compress` at all; only then does `comparesJsonIn` follow the `let` bindings. -/
def comparesJson (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``Lean.Json.instBEq)).isSome ||
    (e.find? (·.isConstOf ``Lean.Json.compress)).isSome && (comparesJsonIn [] e).run' {}

/-- The declarations of `owned`, of the module `moduleName`, whose type or value compares `Json`
values (`comparesJson`), outside `jsonComparisonAllowlist`. -/
def jsonComparisons (moduleName : Name) (owned : Array (Name × ConstantInfo)) : Array Name :=
  owned.filterMap fun (name, info) =>
    let user := privateToUserName name
    let allowed := jsonComparisonAllowlist.any fun (m, n, _) => m == moduleName && n == user
    if allowed then
      none
    else if comparesJson info.type || (info.value? (allowOpaque := true)).any comparesJson then
      some name
    else none

/-- Controls of the check, each with whether it gave the intended answer: a declaration that the
allowlist names for `Regula.RegistryChecks` alone is found in another module; texts of `compress`
compared through two `let` bindings are found; a `compress` that no comparison reads is not. -/
def jsonControls : List (String × Bool) :=
  let compress (j : Expr) : Expr := mkApp (mkConst ``Lean.Json.compress) j
  let beq (a b : Expr) : Expr :=
    let stringBEq := mkApp2 (mkConst ``instBEqOfDecidableEq [Level.zero]) (mkConst ``String)
      (mkConst ``String.decEq)
    mkApp4 (mkConst ``BEq.beq [Level.zero]) (mkConst ``String) stringBEq a b
  let null := mkConst ``Lean.Json.null
  let named := `main
  let declaration : ConstantInfo := .defnInfo {
    name := named, levelParams := [], type := mkConst ``Bool
    value :=
      mkApp2 (mkConst ``BEq.beq [Level.zero]) (mkConst ``Lean.Json) (mkConst ``Lean.Json.instBEq)
    hints := .opaque, safety := .safe, all := [named] }
  let bound := Expr.letE `x (mkConst ``String) (compress null)
    (.letE `y (mkConst ``String) (compress null) (beq (.bvar 1) (.bvar 0)) false) false
  [("main, allowlisted in Regula.RegistryChecks, is found in another module",
      jsonComparisons `Regula.Qualification.SelfAudit #[(named, declaration)] == #[named]),
    ("compress texts compared through let bindings are found", comparesJson bound),
    ("a compress text that no comparison reads is not found", !comparesJson (compress null))]

/-- The finding text for a declaration that compares `Json` values. -/
def jsonComparisonText (name moduleName : Name) : String :=
  s!"json-comparison: {privateToUserName name} ({moduleName}) compares Json values with Lean's \
    one-sided equality; compare a received value with Regula.JsonAgreement.conforms, or name the \
    declaration in jsonComparisonAllowlist when both operands are built by Regula"

/-- The findings of the comparison rule for the declarations `owned` of the module `moduleName`:
each declaration that compares `Json` values (`jsonComparisons`), and each entry of
`jsonComparisonAllowlist` for the module that names no declaration comparing them. The second
kind makes each entry a control: the rule must still find the comparison it allows. -/
def jsonFindings (moduleName : Name) (owned : Array (Name × ConstantInfo)) : Array String :=
  let compares (info : ConstantInfo) : Bool :=
    comparesJson info.type || (info.value? (allowOpaque := true)).any comparesJson
  let stale := (jsonComparisonAllowlist.filter (·.1 == moduleName)).filterMap fun (_, entry, _) =>
    if owned.any (fun (name, info) => privateToUserName name == entry && compares info) then none
    else some s!"json-comparison: {entry} ({moduleName}) is in jsonComparisonAllowlist but \
      compares no Json values there; remove the entry"
  (jsonComparisons moduleName owned).map (jsonComparisonText · moduleName) ++ stale

/-! ### Reads that take an unreadable path for an absent one

Lean 4.34.1's `System.FilePath.pathExists` and `System.FilePath.isDir` return `false` for every
error of `System.FilePath.metadata`, not only for `noFileOrDirectory`
(`Init/System/IO.lean:1162-1173`), so a path that cannot be read, such as one under a directory
without search permission, reads as absent (https://github.com/rbeauchamp/regula/issues/430).
Regula reads whether a path is present through `Regula.Filesystem.isPresent`, `isDirectory`,
`metadataIfPresent`, `readFileIfPresent`, `entryIfPresent` or `realPathIfPresent`, each of which
reads absence only for `noFileOrDirectory` and propagates every other error. Code that cannot
import them, a program that `lean --run` runs, the copy program and the collector, defines its own
copy, which a theorem proves equal to the shared one (`Regula.Filesystem.isPresent_eq_match`). The
campaign refuses each declaration whose type or value names one of Lean's two readers
(`absenceReaders`), unless the allowlist names it with its reason: a read whose `false` decides
nothing, because it only selects a cleanup or a report.

What the check finds: each declaration of an inspected module that names either reader, in its
elaborated type or value, completely, since a call, a partial application and a point-free use
each name it. It does not find a read inside a function of Lean's library or of another package
that a declaration calls, such as `System.SearchPath.findWithExt`, `System.FilePath.walkDir` or
`Lean.findOLean`, which read with these two themselves
(https://github.com/rbeauchamp/regula/issues/441), and it inspects no module of the `markdown` and
`website` packages (https://github.com/rbeauchamp/regula/issues/442). Its controls are the modules
of a committed fixture package outside every library, which the campaign compiles and gives to the
same worker as an audited module (`absenceFixtureControls`). -/

/-- Lean's readers that return `false` for every error of `System.FilePath.metadata`. -/
def absenceReaders : List Name :=
  [``System.FilePath.pathExists, ``System.FilePath.isDir]

/-- The declarations that keep one of `absenceReaders`, each by its module and its name, with the
reason that its `false` decides nothing. The module is part of the key: each executable root
declares its own `main`. Every read of the package goes through the shared observer, so there is
none. -/
def absenceReadAllowlist : Array (Name × Name × String) := #[]

/-- Whether the term `e` names one of `absenceReaders`. -/
def readsAbsence (e : Expr) : Bool :=
  (e.find? fun e => absenceReaders.any e.isConstOf).isSome

/-- Whether the type or the value of `info` names one of `absenceReaders` (`readsAbsence`). -/
def readsAbsenceIn (info : ConstantInfo) : Bool :=
  readsAbsence info.type || (info.value? (allowOpaque := true)).any readsAbsence

/-- Whether `allowlist` names the declaration `name` of the module `moduleName`. -/
def allowedIn (allowlist : Array (Name × Name × String)) (moduleName name : Name) : Bool :=
  allowlist.any fun entry => entry.1 == moduleName && entry.2.1 == privateToUserName name

/-- An allowlist with no entry for a module names none of its declarations. -/
theorem allowedIn_eq_false {allowlist : Array (Name × Name × String)} {moduleName : Name}
    (unlisted : ∀ entry ∈ allowlist, entry.1 ≠ moduleName) (name : Name) :
    allowedIn allowlist moduleName name = false := by
  simp only [allowedIn, Array.any_eq_false]
  intro index bound
  simp [unlisted _ (Array.getElem_mem bound)]

/-- The declarations of `owned`, of the module `moduleName`, that read absence with one of Lean's
readers (`readsAbsenceIn`), except those that `allowlist` names for the module (`allowedIn`). -/
def absenceReads (allowlist : Array (Name × Name × String)) (moduleName : Name)
    (owned : Array (Name × ConstantInfo)) : Array Name :=
  owned.filterMap fun entry =>
    if !allowedIn allowlist moduleName entry.1 && readsAbsenceIn entry.2 then some entry.1 else none

/-- With no allowlist entry for its module, the check finds exactly the declarations whose type or
value names one of Lean's readers. -/
theorem mem_absenceReads {allowlist : Array (Name × Name × String)} {moduleName name : Name}
    {owned : Array (Name × ConstantInfo)}
    (unlisted : ∀ entry ∈ allowlist, entry.1 ≠ moduleName) :
    name ∈ absenceReads allowlist moduleName owned ↔
      ∃ info, (name, info) ∈ owned ∧ readsAbsenceIn info = true := by
  simp only [absenceReads, Array.mem_filterMap, allowedIn_eq_false unlisted, Bool.not_false,
    Bool.true_and]
  constructor
  · rintro ⟨⟨found, info⟩, member, result⟩
    by_cases reads : readsAbsenceIn info = true
    · simp only [reads, ite_true, Option.some.injEq] at result
      exact ⟨info, result ▸ member, reads⟩
    · simp [reads] at result
  · rintro ⟨info, member, reads⟩
    exact ⟨(name, info), member, by simp [reads]⟩

/-- The finding text for a declaration that reads absence with one of Lean's readers. -/
def absenceReadText (name moduleName : Name) : String :=
  s!"absence-read: {privateToUserName name} ({moduleName}) reads whether a path is present with \
    System.FilePath.pathExists or isDir, which return false for every error of metadata; read with \
    Regula.Filesystem.isPresent, isDirectory, metadataIfPresent, readFileIfPresent or \
    entryIfPresent, or name the declaration in absenceReadAllowlist when its false decides nothing"

/-- The findings of the absence rule for the declarations `owned` of the module `moduleName`:
each declaration that reads absence with one of Lean's readers (`absenceReads`), and each entry of
`allowlist` for the module that names no such declaration. The second kind makes each entry a
control: the rule must still find the read it allows. -/
def absenceFindings (moduleName : Name) (owned : Array (Name × ConstantInfo))
    (allowlist : Array (Name × Name × String) := absenceReadAllowlist) : Array String :=
  let stale := (allowlist.filter (·.1 == moduleName)).filterMap fun (_, entry, _) =>
    if owned.any (fun (name, info) => privateToUserName name == entry && readsAbsenceIn info) then
      none
    else some s!"absence-read: {entry} ({moduleName}) is in absenceReadAllowlist but reads no \
      absence with pathExists or isDir there; remove the entry"
  (absenceReads allowlist moduleName owned).map (absenceReadText · moduleName) ++ stale

/-- The findings of both rules of the other libraries for the declarations `owned` of the module
`moduleName`: the comparison rule's (`jsonFindings`), then the absence rule's (`absenceFindings`).
Both workers of the campaign print these, so the absence rule's controls
(`absenceFixtureControls`) run the same check as the audit. -/
def ruleFindings (moduleName : Name) (owned : Array (Name × ConstantInfo)) : Array String :=
  jsonFindings moduleName owned ++ absenceFindings moduleName owned

/-- The committed fixture package of the absence rule's controls, relative to the repository. It
is outside every library of the package, so the campaign inspects it only as a control. -/
def absenceFixtureRoot : FilePath := "examples/fixtures/absence-reads"

/-- The controls of the absence rule, each a module of the fixture package (`absenceFixtureRoot`)
with the findings the worker must print for it and a label: `AbsenceReads.Refused` calls
`pathExists` and names `isDir` without an argument, and both are found; `AbsenceReads.Strict`
reads `metadata` and keeps each error but `noFileOrDirectory`, and nothing is found. -/
def absenceFixtures : List (Name × Array String × String) := [
  (`AbsenceReads.Refused,
    #[absenceReadText `AbsenceReads.legacyPresent `AbsenceReads.Refused,
      absenceReadText `AbsenceReads.legacyDirectory `AbsenceReads.Refused],
    "a call of pathExists and a point-free use of isDir are found"),
  (`AbsenceReads.Strict, #[], "a read of metadata that keeps every other error is not found")]

/-- Import one module, kernel-admit its owned declarations and collect its observations. -/
private unsafe def observe (toolchainLib : FilePath) (moduleName : Name) (source : FilePath) :
    IO (Except String ModuleObservation) := do
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := moduleName, importAll := true }] {} 0
    (loadExts := true) (level := .private)
  let admission ← match ← Checker.Admission.validate env #[moduleName] with
    | .ok admission => pure admission
    | .error failure => return .error failure.detail
  let admitted := (admission.receipt.admitted.filter (·.1 == moduleName)).size
  if let .error refusal := Regula.Collect.ownedDecisionRegistrations env [moduleName] then
    return .error refusal
  let own := Regula.Probe.ownedConstants env [moduleName]
  let ctx : Elab.Command.Context := {
    fileName := "<operational-self-audit>", fileMap := FileMap.ofString "",
    snap? := none, cancelTk? := none }
  let scope ← Regula.Collect.ContractScope.new env admission.replayed.axioms
  let collected ← EIO.toIO' <|
    (show Elab.Command.CommandElabM (Array RegulaPolicy.Declaration) from
      own.mapM fun (name, _) =>
        Regula.Collect.declaration name .snapshot scope (some admission.replayed)).run ctx
      |>.run (Elab.Command.mkState env)
  let declarations : Array RegulaPolicy.Declaration ← match collected with
    | .ok (declarations, _) => pure declarations
    | .error ex => return .error (← ex.toMessageData.toString)
  let mut toolchain : Array Name := #[]
  for d in declarations do
    for name in d.axioms do
      if standardLogicalAxiom name || toolchain.contains name then continue
      let some idx := env.getModuleIdxFor? name | continue
      let some owner := env.header.modules[idx.toNat]? | continue
      if ← toolchainLakeModule toolchainLib owner.module then
        toolchain := toolchain.push name
  let header ← Linter.Documentation.moduleObservation env moduleName
    (← IO.FS.readFile source) source.toString
  let mut material := #[]
  for (name, _) in own do
    if Linter.Documentation.selected env name then
      material := material.push (name, ← Linter.Documentation.declarationFailure env name)
  return .ok {
    «module» := moduleName, declarations, admitted, toolchain, header, material,
    ruleFindings := ruleFindings moduleName own }

/-- Text of one violation finding at the declaration's module. -/
private def declarationText (id : RuleId) (name : Name) (detail : String) (moduleName : Name) :
    Except String String := do
  let ⟨_, finding⟩ ← Findings.declarationFinding id name detail (.module moduleName)
    .incrementalProject (some claim)
  return finding.text

/-- One declaration for which Lean's `collectAxioms` omits axioms that it reaches in the replayed
kernel, by its module and name, with the two sets and the omitted axioms
(`RegulaPolicy.tableOmissionText`). -/
structure OmissionReport where
  /-- The module that owns the declaration. -/
  «module» : String
  /-- The declaration. -/
  declaration : String
  /-- The two axiom sets and the omitted axioms. -/
  detail : String
  deriving ToJson, FromJson

/-- The text of an omission report: the declaration, its module and the detail. -/
def OmissionReport.text (r : OmissionReport) : String :=
  s!"{r.declaration} ({r.module}): {r.detail}"

/-- One module's region-free verdict, transported from its worker process as JSON. -/
structure ModuleResult where
  /-- The audited module's name. -/
  «module» : String
  /-- How many constants the module owns. -/
  declarations : Nat
  /-- How many constants of its own data kernel admission admitted (`ModuleObservation`). -/
  admitted : Nat
  /-- How many of its declarations carry an executable-contract registration. -/
  contracts : Nat
  /-- The rendered text of every finding: module documentation, material documentation and
  declarations that `RegulaPolicy.operationalFailure` or, where that passes,
  `RegulaPolicy.decisionFailure` rejects. -/
  violations : Array String
  /-- Declarations that are `unsafe` or `partial` and have no unsafe-recursion base, each with its
  module, reported rather than failed. -/
  unsafeDeclarations : Array String
  /-- The opaque bases of the module's `partial def`s, each with its module, reported rather than
  failed. -/
  partialDefinitions : Array String
  /-- The admitted axioms, outside Standard-Logical, that a toolchain `Lake` module declares. -/
  toolchainAxioms : Array String
  /-- Non-proposition declarations whose axioms include one of those toolchain axioms, each with
  its module. -/
  toolchainDependents : Array String
  /-- Each declaration of the module for which Lean's `collectAxioms` omits axioms it reaches in
  the replayed kernel, reported rather than failed. -/
  tableOmissions : Array OmissionReport
  deriving ToJson, FromJson

/-- Decide one module's observations with the axioms its own environment attributes to the
toolchain; every retained value is a freshly rendered string. -/
private def decide (o : ModuleObservation) : Except String ModuleResult := do
  let toolchain ← admitToolchainAxioms o.toolchain
  let mut violations : Array String := #[]
  for ⟨_, finding⟩ in ← Linter.Documentation.moduleFindings o.module o.header
      .incrementalProject (some claim) do
    violations := violations.push finding.text
  for (name, failure?) in o.material do
    if let some failure := failure? then
      violations := violations.push (← declarationText
        (ruleForMaterialDocumentation failure) name (materialDocumentationDetail failure) o.module)
  violations := violations ++ o.ruleFindings
  -- A name is reported with its module: two modules, each audited alone, can declare one name.
  let inModule (name : Name) : String := s!"{name} ({o.module})"
  let mut unsafeDeclarations := #[]
  let mut partialDefinitions := #[]
  let mut dependents := #[]
  let mut contracts := 0
  -- A registered decision is decided by a contract of its own module: each module is audited in
  -- its own environment, so a contract in another module of the library does not count.
  let decided := decidedImplementations (recordedContracts o.declarations)
  for d in o.declarations do
    if d.executableContract.isSome then contracts := contracts + 1
    match d.unsafeRecBase with
    | none => if d.isUnsafe || d.isPartial then unsafeDeclarations :=
                                                 unsafeDeclarations.push (inModule d.name)
    | some base =>
      -- A `partial def` compiles to an opaque base implemented by this helper; safe
      -- structural or well-founded recursion keeps a definition base.
      if o.declarations.any (fun r => r.name == base && r.kind == .«opaque») then
        partialDefinitions := partialDefinitions.push (inModule base)
    if !d.isProp && d.axioms.any toolchain.names.contains then
      dependents := dependents.push (inModule d.name)
    if let some failure := (checked_operationalFailure.run toolchain d).or
        (checked_decisionFailure.run d decided) then
      let id := ruleForFailure failure
      let extra := d.axioms.filter fun n => !standardLogicalAxiom n
      let detail := Findings.ruleDetail id d ++
        (if extra.isEmpty then "" else s!" (axioms outside Standard-Logical: {extra.toList})")
      violations := violations.push (← declarationText id d.name detail o.module)
  let omissions := o.declarations.filterMap fun d =>
    if d.tableOmissions.isEmpty then none
    else some { «module» := o.module.toString, declaration := d.name.toString
                detail := tableOmissionText d.axioms d.tableOmissions }
  return ⟨o.module.toString, o.declarations.size, o.admitted, contracts, violations,
      unsafeDeclarations,
    partialDefinitions,
    toolchain.names.map toString, dependents, omissions⟩

/-- The omission reports of all module results, each kept: no report is merged with another,
so two modules that declare one name keep a report each. Each module has one result, and a
result reports only declarations of its own module. -/
def omissionReports (results : Array ModuleResult) : Array OmissionReport :=
  results.flatMap (·.tableOmissions)

/-- A report is kept exactly when some module result holds it. -/
theorem mem_omissionReports {results : Array ModuleResult} {r : OmissionReport} :
    r ∈ omissionReports results ↔ ∃ m ∈ results, r ∈ m.tableOmissions := by
  simp [omissionReports, Array.mem_flatMap]

/-- Worker: observe and decide exactly one module, printing only its JSON result. -/
unsafe def worker (moduleName source : String) : IO Unit := do
  Checker.initializeLeanSearchPath
  let observation ← IO.ofExcept (← observe (← getLibDir (← findSysroot)) moduleName.toName source)
  IO.println (toJson (← IO.ofExcept (decide observation))).compress

/-- Worker for a module of another library of the package: import it alone and print, as a JSON
array, the findings of the comparison rule and of the absence rule for it (`ruleFindings`). -/
unsafe def rulesWorker (moduleName : String) : IO Unit := do
  Checker.initializeLeanSearchPath
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := moduleName.toName, importAll := true }] {} 0
    (loadExts := true) (level := .private)
  IO.println (toJson (ruleFindings moduleName.toName
    (Regula.Probe.ownedConstants env [moduleName.toName]))).compress

/-- Run the controls of the absence rule through the worker of the campaign: compile each module
of `absenceFixtures` alone with the toolchain's `lean` into a new temporary directory, then run
`self`, the campaign's own program, as the worker of the other libraries (`rulesWorker`) on it,
with that directory first on the worker's `LEAN_PATH`. Gives each control's label with whether the
worker printed exactly the control's expected findings, in any order, and why not. -/
def absenceFixtureControls (repo : FilePath) (self : String) : IO (List (String × Bool)) :=
  Regula.Filesystem.withOwnTempDir fun lib => do
    let lean ← Regula.Toolchain.program "lean"
    let root := repo / absenceFixtureRoot
    let inherited := (← IO.getEnv "LEAN_PATH").map (s!"{System.SearchPath.separator}{·}")
    absenceFixtures.mapM fun (moduleName, expected, label) => do
      let olean := modToFilePath lib moduleName "olean"
      if let some directory := olean.parent then IO.FS.createDirAll directory
      let compiled ← Checker.runProcess repo lean.toString
        #["-R", root.toString, "-o", olean.toString,
          (modToFilePath root moduleName "lean").toString] Checker.scrubbedLeanPathEnv
      unless compiled.succeeded do
        return (s!"{label}: {moduleName} did not compile: {compiled.output.trimAscii}", false)
      let result ← Checker.runProcess repo self
        #["--under-deadline", "self-audit-rules-module", moduleName.toString]
        #[("LEAN_PATH", some s!"{lib}{inherited.getD ""}")]
      unless result.succeeded do
        return (s!"{label}: worker exit {result.exitCode}: {result.stderr.trimAscii}", false)
      match Json.parse result.stdout >>= fromJson? (α := Array String) with
      | .ok found =>
        if found.qsort (· < ·) == expected.qsort (· < ·) then return (label, true)
        return (s!"{label}: the worker printed {found}", false)
      | .error e => return (s!"{label}: unreadable worker result: {e}", false)

/-- Run the campaign, or the part of it that `shard` selects (`selected`, `selected_cover`): one
fresh worker process per Lake-discovered module of the library that the shard selects, and one per
selected module of the other libraries and executable roots. Each shard also reports each entry of
`jsonComparisonAllowlist` whose module no shard inspects (`uninspectedEntries`). Any violation or
incomplete module refuses after the full report. -/
def check (shard : Option (Fin shards) := none) (jobs : Nat := 4) : IO Unit := do
  let repo ← Checker.repoRoot
  let inventory ← Checker.Lake.surfaceInventory repo
  let some info := inventory.libraries.find? (·.library == library)
    | throw <| IO.userError s!"self-audit: Lake discovered no root library {library}"
  if info.modules.isEmpty then
    throw <| IO.userError s!"self-audit: Lake discovered no modules of {library}"
  let scope := match shard with
    | some shard => s!" (shard {shardLabel shard})"
    | none => ""
  let modules := selected shard (byName info.modules)
  if modules.isEmpty then
    throw <| IO.userError s!"self-audit{scope}: the shard selects no module of {library}"
  let self := (← IO.appPath).toString
  let outcomes ← Checker.loggedPhase s!"self-audit modules of {library}{scope}" <|
      Checker.mapWorkQueue jobs modules.toArray fun moduleName =>
    show IO (Except String ModuleResult) from do
    let result ← Checker.runProcess repo self
      #["--under-deadline", "self-audit-module", moduleName.toString,
        ((info.sources.find? (·.«module» == moduleName)).map (·.source.toString)).getD ""]
    if result.exitCode != 0 then
      return .error s!"{moduleName}: worker exit {result.exitCode}: {result.stderr.trimAscii}"
    match Json.parse result.stdout >>= fromJson? (α := ModuleResult) with
    | .ok r =>
      if r.module == moduleName.toString then return .ok r
      return .error s!"{moduleName}: worker answered for {r.module}"
    | .error e => return .error s!"{moduleName}: unreadable worker result: {e}"
  -- The other libraries of the package, other than the intended-failure controls, and the root
  -- modules of executables that no library contains are held to the comparison rule and the
  -- absence rule alone: each
  -- module in a worker of its own, after Lake builds them, since a worker imports built modules.
  -- A shard builds and inspects only the modules it selects.
  let others := inventory.libraries.filter fun l => l.library != library && l.library != "Fixtures"
  let inLibrary (m : Name) : Bool := inventory.libraries.any (·.modules.contains m)
  let roots := (inventory.executables.map (·.root)).filter (!inLibrary ·)
  let guarded := selected shard (byName (others.flatMap (·.modules) ++ roots))
  -- An entry of a module that no shard inspects, found from the whole inventory in each shard.
  let uninspected := (uninspectedEntries (info.modules ++ others.flatMap (·.modules) ++ roots)).map
    uninspectedEntryText
  unless guarded.isEmpty do
    let build ← Checker.loggedPhase s!"self-audit build of the guarded modules{scope}" <|
      Checker.runProcess repo "lake" (#["build"] ++ guarded.toArray.map (s!"+{·}"))
    if build.exitCode != 0 then
      throw <| IO.userError s!"self-audit: lake build of the guarded modules failed: \
        {build.stdout.trimAscii} {build.stderr.trimAscii}"
  let jsonOutcomes ← Checker.loggedPhase
      s!"self-audit Json comparisons and absence reads{scope}" <|
      Checker.mapWorkQueue jobs guarded.toArray fun moduleName =>
    show IO (Except String (Array String)) from do
    let result ← Checker.runProcess repo self
      #["--under-deadline", "self-audit-rules-module", moduleName.toString]
    if result.exitCode != 0 then
      return .error s!"{moduleName}: worker exit {result.exitCode}: {result.stderr.trimAscii}"
    match Json.parse result.stdout >>= fromJson? (α := Array String) with
    | .ok found => return .ok found
    | .error e => return .error s!"{moduleName}: unreadable worker result: {e}"
  let absenceControls ← Checker.loggedPhase s!"self-audit absence read controls{scope}" <|
    absenceFixtureControls repo self
  let results := outcomes.filterMap fun | .ok r => some r | .error _ => none
  let incomplete := outcomes.filterMap fun | .ok _ => none | .error e => some e
  let incomplete := incomplete ++ jsonOutcomes.filterMap fun | .ok _ => none | .error e => some e
  let incomplete := incomplete ++ jsonControls.filterMap fun (label, passed) =>
    if passed then none else some s!"Json comparison control failed: {label}"
  let incomplete := incomplete ++ absenceControls.filterMap fun (label, passed) =>
    if passed then none else some s!"absence read control failed: {label}"
  let union (field : ModuleResult → Array String) : Array String :=
    (results.foldl (fun acc r => (field r).foldl
      (fun acc n => if acc.contains n then acc else acc.push n) acc) #[]).qsort (· < ·)
  let violations := results.flatMap (·.violations) ++
    (jsonOutcomes.filterMap fun | .ok found => some found | .error _ => none).flatMap id ++
    uninspected
  for line in violations do IO.println line
  for line in incomplete do IO.println s!"INCOMPLETE {line}"
  let declarations := results.foldl (· + ·.declarations) 0
  let admitted := results.foldl (· + ·.admitted) 0
  let contracts := results.foldl (· + ·.contracts) 0
  let unsafeDeclarations := union (·.unsafeDeclarations)
  let partialDefinitions := union (·.partialDefinitions)
  let dependents := union (·.toolchainDependents)
  IO.println s!"operational self-audit of library {library}{scope}: \
    {results.size}/{modules.length} module(s) of the {info.modules.size} the library has, \
    {declarations} declaration(s) inspected, {admitted} constant(s) of the \
    modules' own data (every one neither unsafe nor partial) kernel-admitted, \
    {contracts} executable contract registration(s)"
  IO.println s!"Json comparisons{scope}: each of those modules of {library} and \
    {guarded.length} module(s) of the other libraries but Fixtures and of executable roots \
    {roots.toList} inspected, \
    {jsonComparisonAllowlist.size} allowlisted declaration(s), \
    {(jsonControls.filter (·.2)).length}/{jsonControls.length} control(s) as intended"
  IO.println s!"absence reads{scope}: the same modules inspected for pathExists and isDir, \
    {absenceReadAllowlist.size} allowlisted declaration(s), \
    {(absenceControls.filter (·.2)).length}/{absenceControls.length} control(s) of the fixtures \
    in {absenceFixtureRoot} as intended"
  IO.println s!"reported, not failed: {unsafeDeclarations.size} unsafe \
    declaration(s): {unsafeDeclarations.toList}"
  IO.println s!"reported, not failed: {partialDefinitions.size} partial \
    definition(s): {partialDefinitions.toList}"
  IO.println s!"reported, not failed: {dependents.size} definition(s) reach toolchain Lake \
    axiom(s) {(union (·.toolchainAxioms)).toList}: {dependents.toList}"
  let omissions := omissionReports results
  IO.println s!"reported, not failed: {omissions.size} declaration(s) for which Lean's \
    collectAxioms omits axioms they reach in the replayed kernel: \
    {(omissions.map (·.text)).toList}"
  IO.println "trusted, not verified: Lean import and kernel replay, the collector's observations, \
    the toolchain artifact paths, worker processes and JSON transport, and every execution path \
    (the library's executables make no execution claim)"
  unless violations.isEmpty && incomplete.isEmpty do
    throw <| IO.userError s!"operational self-audit{scope}: FAIL ({violations.size} \
      violation(s), {incomplete.size} incomplete module(s))"
  IO.println s!"operational self-audit{scope}: PASS (operational claim only; not a conforming \
    proof surface)"

end Regula.Qualification.SelfAudit
