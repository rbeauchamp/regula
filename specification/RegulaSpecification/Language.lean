/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import LeanIntent.Record
import LeanIntent.Obligations
import LeanIntent.Progress
import Regula.LanguageSet

/-!
# The language check

What the check that reads a project before anything of it is compiled must decide, stated over Lean's
own `Syntax` and independently of the function that decides it. It imports the closed set, which is
data, and no function of Regula.

`languageRecord` is the contract of the decision and `fullGateRecord` that of the gate that runs it.
The owner's confirmed restatement, the status of each consequence and the second reading are in
`confirmation.md`; `README.md` gives the plain words.

What this module cannot state is that a file the decision admits runs no code of the project when Lean
compiles it, because no model of Lean's elaborator exists in Lean. `LeanBehaviour` names that as two
hypotheses, H1 and H2, about Lean at one version, and each theorem that needs them takes them as an
argument.
-/

namespace RegulaSpecification.Language

open Lean (Name Syntax)
open Regula.Language
open LeanIntent

/-- `s` is a position of the tree `t` that the check reads: `t` itself, or a position of a child of a
node whose kind holds a construct and not open text. -/
inductive Occurs : Syntax → Syntax → Prop where
  /-- A tree is a position of itself. -/
  | self (t : Syntax) : Occurs t t
  /-- A position of a child is a position of the node. -/
  | child {s c : Syntax} {i : Lean.SourceInfo} {k : Name} {as : Array Syntax} :
      k ∉ leafKinds → c ∈ as → Occurs s c → Occurs s (.node i k as)

/-- A name that a project may not write, because Lean or its compiler reads that form itself: a
component that starts with `_`, other than a first component `_root_`, or the component `autoParam`,
whose second argument Lean evaluates. -/
inductive ReservedName : Name → Prop where
  /-- The last component starts with `_`. -/
  | underscore {p : Name} {s : String} : s.front = '_' → (p, s) ≠ (.anonymous, "_root_") →
      ReservedName (.str p s)
  /-- The last component is `autoParam`. -/
  | autoParam {p : Name} : ReservedName (.str p "autoParam")
  /-- A component before the last is reserved. -/
  | str {p : Name} {s : String} : ReservedName p → ReservedName (.str p s)
  /-- A component before a number is reserved. -/
  | num {p : Name} {n : Nat} : ReservedName p → ReservedName (.num p n)

/-- `n` is an argument of a `namespace` or `open` command: a direct child, or a child of a direct `null`
node, of what the parser gives for those commands. -/
def TargetOf (as : Array Syntax) (n : Name) : Prop :=
  ∃ i r p, Syntax.ident i r n p ∈ as ∨
    ∃ i' xs, Syntax.node i' `null xs ∈ as ∧ Syntax.ident i r n p ∈ xs

/-- The components of a target of `namespace` or `open`, with any leading `_root_` removed. -/
def targetComponents (n : Name) : List Name :=
  (components n).dropWhile (· = `_root_)

/-- From some namespace, a command with the target `n` can activate the namespace `N`: Lean tries the
target under each enclosing and open namespace, and `namespace A.B` enters `A` first. So some non-empty
start of the target is an end of `N`, by whole components. -/
def CanActivate (N n : Name) : Prop :=
  ∃ i, 0 < i ∧ i ≤ (targetComponents n).length ∧
    (targetComponents n).take i <:+ components N

/-- What one node may be: its kind is in the closed set, and each kind that names something Lean reads
as code or as parser state names only what its own table holds. -/
def NodeAdmitted (scopedParsers : List Name) (k : Name) (as : Array Syntax) : Prop :=
  (k ∈ kinds ∨ k ∈ leafKinds) ∧
  (k = `Lean.Parser.Attr.simple →
    (∃ i r a p, as[0]? = some (.ident i r a p) ∧ a ∈ simpleAttributes) ∧
      ∃ i', as[1]? = some (.node i' `null #[])) ∧
  (k = `Lean.Parser.Command.set_option →
    ∃ i r o p, as[1]? = some (.ident i r o p) ∧ o ∈ options) ∧
  (k = `Lean.Parser.Tactic.posConfigItem →
    ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ configItems) ∧
  (k = `Lean.Parser.Command.derivingClass →
    ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ derivingClasses) ∧
  ((k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple) →
    ∀ n, TargetOf as n → ∀ N ∈ scopedParsers, ¬ CanActivate N n)

/-- What one position may be. A position of Lean's parser that it could not fill is never admitted. -/
def PositionAdmitted (scopedParsers : List Name) : Syntax → Prop
  | .missing => False
  | .atom _ v => v ∈ atoms
  | .ident _ _ n _ => ¬ ReservedName n
  | .node _ k as => NodeAdmitted scopedParsers k as

/-- Every position of the tree is admitted. -/
def TreeAdmitted (scopedParsers : List Name) (t : Syntax) : Prop :=
  ∀ s, Occurs s t → PositionAdmitted scopedParsers s

/-- The header starts with `module`, so Lean itself refuses to evaluate a constant of the project that
is not `meta`, and nothing admitted can declare one. -/
def ModuleFile (header : Syntax) : Prop :=
  ∃ i as, Occurs (.node i `Lean.Parser.Module.moduleTk as) header

/-- The reader reached the end of the file: the last tree is the parser's end of input. -/
def ReadToEnd (commands : List Syntax) : Prop :=
  ∃ i as, commands.getLast? = some (.node i `Lean.Parser.Command.eoi as)

/-- One file is in the closed language. -/
def FileAdmitted (f : FileRead) : Prop :=
  f.parsed = true ∧ ModuleFile f.header ∧ ReadToEnd f.commands ∧
    TreeAdmitted f.scopedParsers f.header ∧ ∀ c ∈ f.commands, TreeAdmitted f.scopedParsers c

/-- A key of `lakefile.toml` is in the closed set: a key of the table, or an option of `options` under
`leanOptions`. -/
def ConfigKeyAdmitted (k : Name) : Prop :=
  k ∈ configKeys ∨ ∃ o ∈ options, k = `leanOptions ++ o

/-- The project's own configuration is closed: the pinned toolchain, no `lakefile.lean`, no other key,
and no package from a local path, which would be code that the project wrote. -/
def ConfigClosed (r : Reading) : Prop :=
  r.toolchainFile = some leanToolchain ∧ r.leanConfig = false ∧
    (∀ k ∈ r.configKeys, ConfigKeyAdmitted k) ∧ ∀ p ∈ r.packages, p.fromGit = true

/-- The checker started outside the project's Lake, everything was read, and nothing the project planted
under `.lake` or a dependency's build output can stand in for what the check read. -/
def ReadInFull (r : Reading) : Prop :=
  r.outside = true ∧ r.unread = [] ∧ r.outputs = []

/-- Some package's Lake configuration is code, which a Lake load of the workspace would run. -/
def DependencyConfigIsCode (r : Reading) : Prop :=
  ∃ p ∈ r.packages, p.tomlConfig = false

/-- Mathlib is in the build's imports. -/
def MathlibReached (r : Reading) : Prop :=
  ∃ m ∈ r.reached, m.getRoot = `Mathlib

/-- There is a claim, each root is reached, and each module reached has its file read. -/
def Covered (r : Reading) : Prop :=
  r.roots ≠ [] ∧ (∀ m ∈ r.roots, m ∈ r.reached) ∧ ∀ m ∈ r.reached, ∃ f ∈ r.files, f.module = m

/-- Each file of the root package is in the closed language. -/
def RootAdmitted (r : Reading) : Prop :=
  ∀ f ∈ r.files, f.inRoot = true → FileAdmitted f

/-- Each file read of a dependency is in the closed language. -/
def DependenciesAdmitted (r : Reading) : Prop :=
  ∀ f ∈ r.files, f.inRoot = false → FileAdmitted f

/-- The contract of the decision. Each clause names what its outcome rests on, and the clauses together
fix the outcome of every reading (`language_o5`). -/
def languageRecord : IntentRecord (Reading → Outcome) where
  shape := .function Reading (fun _ => Outcome)
  dom := []
  props := [
    ⟨"another toolchain, a lakefile.lean, a Lake key outside the closed set or a package from a local path is refused",
      fun d => ∀ r, ¬ ConfigClosed r → d r = .refused⟩,
    ⟨"a checker the project's Lake started, a failure to read or anything under .lake is incomplete",
      fun d => ∀ r, ConfigClosed r → ¬ ReadInFull r → d r = .incomplete⟩,
    ⟨"a dependency whose Lake configuration is code leaves only the proof verdict",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → DependencyConfigIsCode r → d r = .proofOnly⟩,
    ⟨"a build with Mathlib in its imports has only the proof verdict",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → MathlibReached r →
        d r = .proofOnly⟩,
    ⟨"a project with no claim or a module left unread is incomplete",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r →
        ¬ MathlibReached r → ¬ Covered r → d r = .incomplete⟩,
    ⟨"a file of the root package outside the closed language is refused",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r →
        ¬ MathlibReached r → Covered r → ¬ RootAdmitted r → d r = .refused⟩,
    ⟨"a dependency's file outside the closed language leaves only the proof verdict",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r →
        ¬ MathlibReached r → Covered r → RootAdmitted r → ¬ DependenciesAdmitted r →
        d r = .proofOnly⟩,
    ⟨"a project wholly inside the closed language is admitted",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r →
        ¬ MathlibReached r → Covered r → RootAdmitted r → DependenciesAdmitted r →
        d r = .admitted⟩]
  vocab := [
    ⟨"a closed configuration", Reading, ConfigClosed⟩,
    ⟨"a reading in full", Reading, ReadInFull⟩,
    ⟨"a dependency whose configuration is code", Reading, DependencyConfigIsCode⟩,
    ⟨"Mathlib in the imports", Reading, MathlibReached⟩,
    ⟨"a covered reading", Reading, Covered⟩,
    ⟨"an admitted root package", Reading, RootAdmitted⟩,
    ⟨"admitted dependencies", Reading, DependenciesAdmitted⟩,
    ⟨"an admitted file", FileRead, FileAdmitted⟩]

theorem language_meets_iff (d : Reading → Outcome) :
    languageRecord.Meets d ↔
      (∀ r, ¬ ConfigClosed r → d r = .refused) ∧
      (∀ r, ConfigClosed r → ¬ ReadInFull r → d r = .incomplete) ∧
      (∀ r, ConfigClosed r → ReadInFull r → DependencyConfigIsCode r → d r = .proofOnly) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → MathlibReached r →
        d r = .proofOnly) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → ¬ MathlibReached r →
        ¬ Covered r → d r = .incomplete) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → ¬ MathlibReached r →
        Covered r → ¬ RootAdmitted r → d r = .refused) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → ¬ MathlibReached r →
        Covered r → RootAdmitted r → ¬ DependenciesAdmitted r → d r = .proofOnly) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ DependencyConfigIsCode r → ¬ MathlibReached r →
        Covered r → RootAdmitted r → DependenciesAdmitted r → d r = .admitted) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, languageRecord]

/-- The property the check exists for, read off the record: it admits a reading exactly when
everything read is in the closed set, and nothing is left out. -/
def Inside (r : Reading) : Prop :=
  ConfigClosed r ∧ ReadInFull r ∧ ¬ DependencyConfigIsCode r ∧ ¬ MathlibReached r ∧ Covered r ∧
    RootAdmitted r ∧ DependenciesAdmitted r

theorem admitted_iff {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading) :
    d r = .admitted ↔ Inside r := by
  obtain ⟨h1, h2, hc, h3, h4, h5, h6, h7⟩ := (language_meets_iff d).mp h
  constructor
  · intro ha
    by_cases c : ConfigClosed r
    · by_cases f : ReadInFull r
      · by_cases k : DependencyConfigIsCode r
        · simp [hc r c f k] at ha
        · by_cases m : MathlibReached r
          · simp [h3 r c f k m] at ha
          · by_cases v : Covered r
            · by_cases o : RootAdmitted r
              · by_cases p : DependenciesAdmitted r
                · exact ⟨c, f, k, m, v, o, p⟩
                · simp [h6 r c f k m v o p] at ha
              · simp [h5 r c f k m v o] at ha
            · simp [h4 r c f k m v] at ha
      · simp [h2 r c f] at ha
    · simp [h1 r c] at ha
  · rintro ⟨c, f, k, m, v, o, p⟩
    exact h7 r c f k m v o p

/-- Any two decisions that meet the record agree on every reading, so the record leaves nothing about
the outcome unsaid. -/
theorem language_o5 : O5 languageRecord .eq := by
  rw [o5_correct]
  intro u v hu hv
  obtain ⟨u1, u2, uc, u3, u4, u5, u6, u7⟩ := (language_meets_iff u).mp ⟨hu.1, hu.2⟩
  obtain ⟨v1, v2, vc, v3, v4, v5, v6, v7⟩ := (language_meets_iff v).mp ⟨hv.1, hv.2⟩
  funext r
  by_cases c : ConfigClosed r
  · by_cases f : ReadInFull r
    · by_cases k : DependencyConfigIsCode r
      · rw [uc r c f k, vc r c f k]
      · by_cases m : MathlibReached r
        · rw [u3 r c f k m, v3 r c f k m]
        · by_cases w : Covered r
          · by_cases o : RootAdmitted r
            · by_cases p : DependenciesAdmitted r
              · rw [u7 r c f k m w o p, v7 r c f k m w o p]
              · rw [u6 r c f k m w o p, v6 r c f k m w o p]
            · rw [u5 r c f k m w o, v5 r c f k m w o]
          · rw [u4 r c f k m w, v4 r c f k m w]
    · rw [u2 r c f, v2 r c f]
  · rw [u1 r c, v1 r c]

theorem language_o4 : O4 languageRecord := o4_function _ rfl

/-! ## The readings that show the record is not empty on either side -/

/-- The smallest header of a `module` file. -/
def moduleHeader : Syntax :=
  .node .none `Lean.Parser.Module.moduleTk #[.atom .none "module"]

/-- The parser's end of input. -/
def endOfInput : Syntax :=
  .node .none `Lean.Parser.Command.eoi #[.atom .none ""]

/-- A file in the closed language. -/
def goodFile : FileRead :=
  { module := `Good, inRoot := true, header := moduleHeader, commands := [endOfInput], parsed := true,
    scopedParsers := [] }

/-- A project of one such file. -/
def goodReading : Reading :=
  { outside := true, toolchainFile := some leanToolchain, leanConfig := false,
    configKeys := [`name], packages := [], roots := [`Good], reached := [`Good],
    files := [goodFile], unread := [], outputs := [] }

theorem occurs_moduleHeader {s : Syntax} (h : Occurs s moduleHeader) :
    s = moduleHeader ∨ s = .atom .none "module" := by
  cases h with
  | self => exact .inl rfl
  | @child c _ _ _ _ hc hs =>
    have hc' : c = Syntax.atom .none "module" := by simpa using hc
    subst hc'
    cases hs with
    | self => exact .inr rfl

theorem admitted_moduleHeader : TreeAdmitted [] moduleHeader := by
  intro s h
  rcases occurs_moduleHeader h with rfl | rfl
  · refine ⟨.inl (by decide +kernel), ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;>
      first | exact absurd h' (by decide) | exact absurd h'.elim (by decide)
  · show "module" ∈ atoms
    decide +kernel

theorem occurs_endOfInput {s : Syntax} (h : Occurs s endOfInput) : s = endOfInput := by
  cases h with
  | self => rfl
  | child hk _ _ => exact absurd (by decide +kernel) hk

theorem admitted_endOfInput : TreeAdmitted [] endOfInput := by
  intro s h
  rw [occurs_endOfInput h]
  refine ⟨.inr (by decide +kernel), ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;>
    first | exact absurd h' (by decide) | exact absurd h'.elim (by decide)

theorem goodFile_admitted : FileAdmitted goodFile := by
  refine ⟨rfl, ⟨.none, _, .self _⟩, ⟨.none, _, rfl⟩, admitted_moduleHeader, ?_⟩
  intro c hc
  have : c = endOfInput := by simpa [goodFile] using hc
  rw [this]
  exact admitted_endOfInput

theorem closed_of_goodKeys {r : Reading} (ht : r.toolchainFile = some leanToolchain)
    (hl : r.leanConfig = false) (hk : r.configKeys = [`name]) (hp : r.packages = []) :
    ConfigClosed r := by
  refine ⟨ht, hl, ?_, by simp [hp]⟩
  intro k h
  rw [hk] at h
  have : k = `name := by simpa using h
  subst this
  exact .inl (by decide +kernel)

theorem goodReading_inside : Inside goodReading := by
  refine ⟨closed_of_goodKeys rfl rfl rfl rfl, ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨p, hp, -⟩
    simp [goodReading] at hp
  · rintro ⟨m, hm, hr⟩
    have : m = `Good := by simpa [goodReading] using hm
    subst this
    exact absurd hr (by decide)
  · refine ⟨by simp [goodReading], by simp [goodReading], ?_⟩
    intro m hm
    have : m = `Good := by simpa [goodReading] using hm
    subst this
    exact ⟨goodFile, by simp [goodReading], rfl⟩
  · intro f hf _
    have : f = goodFile := by simpa [goodReading] using hf
    subst this
    exact goodFile_admitted
  · intro f hf hr
    have : f = goodFile := by simpa [goodReading] using hf
    subst this
    simp [goodFile] at hr

/-- `goodReading` with a `lakefile.lean`. -/
def leanConfigReading : Reading := { goodReading with leanConfig := true }

/-- `goodReading` from a checker that the project's Lake started. -/
def insideReading : Reading := { goodReading with outside := false }

/-- `goodReading` with a dependency whose configuration is code. -/
def codeDependencyReading : Reading :=
  { goodReading with packages := [{ name := `dep, fromGit := true, tomlConfig := false }] }

/-- `goodReading` with no claim. -/
def noClaimReading : Reading :=
  { goodReading with roots := [], reached := [], files := [] }

/-- `goodReading`, importing Mathlib. -/
def mathlibReading : Reading :=
  { goodReading with reached := [`Good, `Mathlib.Tactic] }

/-- `goodReading` with a module of `reached` that has no file. -/
def uncoveredReading : Reading :=
  { goodReading with reached := [`Good, `Other] }

/-- `goodReading` whose file holds a position the parser could not fill. -/
def badRootReading : Reading :=
  { goodReading with files := [{ goodFile with commands := [.missing, endOfInput] }] }

/-- `goodReading` with a dependency's file that Lean's parser refused. -/
def badDependencyReading : Reading :=
  { goodReading with
    files := [goodFile, { goodFile with module := `Dep, inRoot := false, parsed := false }]
    reached := [`Good, `Dep] }

theorem leanConfig_not_closed : ¬ ConfigClosed leanConfigReading := fun h => by
  simpa [leanConfigReading, goodReading] using h.2.1

theorem noClaim_not_covered : ¬ Covered noClaimReading := fun h => by
  simpa [noClaimReading] using h.1

/-- A decision that meets the record, stated by cases on the predicates. It shows that one subject
serves every reading. -/
noncomputable def modelDecision (r : Reading) : Outcome :=
  open Classical in
  if ¬ ConfigClosed r then .refused
  else if ¬ ReadInFull r then .incomplete
  else if DependencyConfigIsCode r then .proofOnly
  else if MathlibReached r then .proofOnly
  else if ¬ Covered r then .incomplete
  else if ¬ RootAdmitted r then .refused
  else if ¬ DependenciesAdmitted r then .proofOnly
  else .admitted

theorem modelDecision_meets : languageRecord.Meets modelDecision := by
  rw [language_meets_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [modelDecision]

theorem language_o2Run : O2Run languageRecord := o2Run_of_meets modelDecision_meets


theorem good_closed : ConfigClosed goodReading := closed_of_goodKeys rfl rfl rfl rfl

theorem good_full : ReadInFull goodReading := ⟨rfl, rfl, rfl⟩

theorem good_no_code : ¬ DependencyConfigIsCode goodReading := goodReading_inside.2.2.1

theorem no_code_of_no_packages {r : Reading} (h : r.packages = []) : ¬ DependencyConfigIsCode r := by
  rintro ⟨p, hp, -⟩
  simp [h] at hp

theorem mathlib_reached : MathlibReached mathlibReading :=
  ⟨`Mathlib.Tactic, by simp [mathlibReading], by decide⟩

theorem not_mathlib_of_reached {r : Reading} (h : ∀ m ∈ r.reached, m = `Good ∨ m = `Other ∨ m = `Dep) :
    ¬ MathlibReached r := by
  rintro ⟨m, hm, hr⟩
  rcases h m hm with rfl | rfl | rfl <;> exact absurd hr (by decide)

theorem uncovered : ¬ Covered uncoveredReading := by
  rintro ⟨-, -, h⟩
  obtain ⟨f, hf, hm⟩ := h `Other (by simp [uncoveredReading])
  have : f = goodFile := by simpa [uncoveredReading, goodReading] using hf
  subst this
  exact absurd hm (by decide)

theorem badRoot_covered : Covered badRootReading := by
  refine ⟨by simp [badRootReading, goodReading], by simp [badRootReading, goodReading], ?_⟩
  intro m hm
  have : m = `Good := by simpa [badRootReading, goodReading] using hm
  subst this
  exact ⟨{ goodFile with commands := [.missing, endOfInput] }, by simp [badRootReading], rfl⟩

theorem badRoot_refused : ¬ RootAdmitted badRootReading := by
  intro h
  have ha := h { goodFile with commands := [.missing, endOfInput] } (by simp [badRootReading]) rfl
  exact ha.2.2.2.2 .missing (by simp) .missing (.self _)

theorem badDependency_covered : Covered badDependencyReading := by
  refine ⟨by simp [badDependencyReading, goodReading], by simp [badDependencyReading, goodReading], ?_⟩
  intro m hm
  have : m = `Good ∨ m = `Dep := by simpa [badDependencyReading] using hm
  rcases this with rfl | rfl
  · exact ⟨goodFile, by simp [badDependencyReading], rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), rfl⟩

theorem badDependency_root : RootAdmitted badDependencyReading := by
  intro f hf hr
  have : f = goodFile ∨ f = { goodFile with module := `Dep, inRoot := false, parsed := false } := by
    simpa [badDependencyReading] using hf
  rcases this with rfl | rfl
  · exact goodFile_admitted
  · simp at hr

theorem badDependency_refused : ¬ DependenciesAdmitted badDependencyReading := by
  intro h
  have ha := h { goodFile with module := `Dep, inRoot := false, parsed := false }
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) rfl
  exact absurd ha.1 (by simp)

/-- O2 at confirmation: the record has no domain hypothesis, and each predicate has an instance. -/
theorem language_o2 : O2 languageRecord := by
  rw [o2_correct]
  refine ⟨⟨modelDecision, by simp [languageRecord]⟩, ?_⟩
  intro p hp
  simp only [languageRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨goodReading, good_closed⟩
  · exact ⟨goodReading, good_full⟩
  · exact ⟨codeDependencyReading, ⟨{ name := `dep, fromGit := true, tomlConfig := false }, by simp [codeDependencyReading], rfl⟩⟩
  · exact ⟨mathlibReading, mathlib_reached⟩
  · exact ⟨goodReading, goodReading_inside.2.2.2.2.1⟩
  · exact ⟨goodReading, goodReading_inside.2.2.2.2.2.1⟩
  · exact ⟨goodReading, goodReading_inside.2.2.2.2.2.2⟩
  · exact ⟨goodFile, goodFile_admitted⟩

/-- O3: each clause can fail. The subject that fails it is a constant, on the reading the clause is
about. -/
theorem language_o3 : O3 languageRecord := by
  rw [o3_correct]
  intro p hp
  simp only [languageRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  have c {r : Reading} (ht : r.toolchainFile = some leanToolchain) (hl : r.leanConfig = false)
      (hk : r.configKeys = [`name]) (hp : r.packages = []) := closed_of_goodKeys ht hl hk hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun _ => .admitted, fun h => absurd (h leanConfigReading leanConfig_not_closed) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h insideReading (c rfl rfl rfl rfl) fun hf => by simpa [insideReading] using hf.1) (by decide)⟩
  · refine ⟨fun _ => .admitted, fun h => absurd
      (h codeDependencyReading ⟨rfl, rfl, ?_, by simp [codeDependencyReading]⟩ ⟨rfl, rfl, rfl⟩
        ⟨{ name := `dep, fromGit := true, tomlConfig := false }, by simp [codeDependencyReading], rfl⟩) (by decide)⟩
    intro k hk
    have : k = `name := by simpa [codeDependencyReading, goodReading] using hk
    subst this
    exact .inl (by decide +kernel)
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h mathlibReading (c rfl rfl rfl rfl) ⟨rfl, rfl, rfl⟩ (no_code_of_no_packages rfl)
        mathlib_reached) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h noClaimReading (c rfl rfl rfl rfl) ⟨rfl, rfl, rfl⟩ (no_code_of_no_packages rfl)
        (not_mathlib_of_reached (by simp [noClaimReading])) noClaim_not_covered) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h badRootReading (c rfl rfl rfl rfl) ⟨rfl, rfl, rfl⟩ (no_code_of_no_packages rfl)
        (not_mathlib_of_reached (by simp [badRootReading, goodReading])) badRoot_covered
        badRoot_refused) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h badDependencyReading (c rfl rfl rfl rfl) ⟨rfl, rfl, rfl⟩ (no_code_of_no_packages rfl)
        (not_mathlib_of_reached (by simp [badDependencyReading])) badDependency_covered
        badDependency_root badDependency_refused) (by decide)⟩
  · exact ⟨fun _ => .refused, fun h => absurd
      (h goodReading good_closed good_full good_no_code goodReading_inside.2.2.2.1
        goodReading_inside.2.2.2.2.1 goodReading_inside.2.2.2.2.2.1
        goodReading_inside.2.2.2.2.2.2) (by decide)⟩

/-! ## The degenerate decisions

The subject is a function to `Outcome`, which has four values. Each constant fails the record, so a
check that admits everything, refuses everything or does nothing does not satisfy it. -/

theorem constant_fails (o : Outcome) : ¬ languageRecord.Meets (fun _ => o) := by
  intro h
  have ha := (admitted_iff h goodReading).mpr goodReading_inside
  obtain ⟨h1, -⟩ := (language_meets_iff _).mp h
  have hb := h1 leanConfigReading leanConfig_not_closed
  rw [ha] at hb
  exact absurd hb (by decide)

/-! ## The closed set against what the owner's words refuse -/

/-- The kinds of the constructs the owner's words name, and the others of their families, read from
`Init/Tactics.lean`, `Lean/Parser/Command.lean`, `Lean/Parser/Syntax.lean` and `Lean/Elab/` at Lean
v4.35.0. -/
def refusedKinds : List Name :=
  [`Lean.runCmd, `Lean.Parser.Command.eval, `Lean.Parser.Command.evalBang,
    `Lean.Parser.Command.guardCmd, `Lean.guardMsgsCmd, `Lean.runElab, `Lean.runMeta,
    `Lean.Parser.Tactic.nativeDecide, `Lean.Parser.Tactic.runTac, `Lean.byElab,
    `Lean.Parser.Command.macro, `Lean.Parser.Command.macro_rules, `Lean.Parser.Command.syntax,
    `Lean.Parser.Command.syntaxAbbrev, `Lean.Parser.Command.syntaxCat,
    `Lean.Parser.Command.notation, `Lean.Parser.Command.mixfix, `Lean.Parser.Command.elab,
    `Lean.Parser.Command.elab_rules, `Lean.Parser.Command.initialize, `Lean.Parser.Attr.macro,
    `Lean.Parser.Attr.extern, `Lean.Parser.Attr.export, `Lean.Parser.Command.partial,
    `Lean.Parser.Command.unsafe, `Lean.Parser.Term.unsafe, `Lean.Parser.Command.meta,
    `Lean.Parser.Command.deriving, `Lean.Parser.Term.quot, `Lean.Parser.Tactic.quot,
    `Lean.Parser.Term.dynamicQuot, `Lean.Parser.Command.quot, `Lean.includeStr,
    `Lean.Parser.Term.binderTactic, `Lean.Parser.Command.openHiding,
    `Lean.Parser.Command.openRenaming, `Lean.Parser.Command.exit, `Lean.Parser.Command.import,
    `Lean.Parser.Module.prelude, `Lean.Parser.Tactic.tryTrace, `Lean.Parser.Tactic.exact?,
    `Lean.Parser.Tactic.apply?, `Lean.Parser.Command.check_failure]

theorem refusedKinds_outside : ∀ k ∈ refusedKinds, k ∉ kinds ∧ k ∉ leafKinds := by decide +kernel

/-- What `@[name]` must not name: each evaluates the named definition or replaces compiled code. -/
theorem refused_attributes :
    ∀ a ∈ [`implemented_by, `extern, `csimp, `macro_inline, `init, `builtin_init, `export,
      `command_elab, `term_elab, `tactic, `macro, `simproc, `cbv_simproc],
    a ∉ simpleAttributes := by decide +kernel

/-- What a file or the configuration must not set. -/
theorem refused_options :
    ∀ o ∈ [`debug.skipKernelTC, `match.ignoreUnusedAlts, `internal.parseQuotWithCurrentStage,
      `compiler.extract_closed, `doc.verso],
    o ∉ options := by decide +kernel

/-- `decide +native` is refused, and `decide +kernel` is admitted. -/
theorem refused_native : `native ∉ configItems ∧ `kernel ∈ configItems := by decide +kernel

/-- What a project's `lakefile.toml` must not set: each loads or runs something at build time. -/
theorem refused_config_keys :
    ∀ k ∈ [`plugins, `dynlibs, `moreLeanArgs, `weakLeanArgs, `moreServerOptions, `needs,
      `extraDepTargets, `precompileModules, `moreLinkObjs, `moreLinkLibs, `moreLinkArgs, `buildDir,
      `leanLibDir, `lean_lib.plugins, `lean_lib.dynlibs, `lean_lib.moreLeanArgs,
      `lean_lib.needs, `lean_lib.extraDepTargets, `lean_lib.precompileModules, `lean_exe.plugins,
      `lean_exe.needs, `lean_exe.moreLeanArgs, `require.source, `require.path, `testDriver,
      `packagesDir],
    k ∉ configKeys ∧ ∀ o ∈ options, k ≠ `leanOptions ++ o := by decide +kernel

/-- A reading from a checker that the project's Lake started is never admitted, whatever else it holds.
A decision that meets the record gives such a reading no full verdict. -/
theorem started_inside_not_admitted {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : r.outside = false) : d r ≠ .admitted := by
  intro ha
  have := ((admitted_iff h r).mp ha).2.1.1
  simp [hr] at this

/-- Anything under `.lake` at the start stops the reading: a planted checker, build or package cannot
stand in for what the check read. -/
theorem planted_not_admitted {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : r.outputs ≠ []) : d r ≠ .admitted := by
  intro ha
  exact hr ((admitted_iff h r).mp ha).2.1.2.2

/-- A `lakefile.lean` is refused. -/
theorem lean_config_refused {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : r.leanConfig = true) : d r = .refused := by
  obtain ⟨h1, -⟩ := (language_meets_iff d).mp h
  exact h1 r fun hc => by
    have := hc.2.1
    simp [hr] at this

/-- What the owner's words require the closed set to hold. -/
theorem admitted_kinds :
    ∀ k ∈ [`Lean.Parser.Tactic.simp, `Lean.Parser.Tactic.omega, `Lean.Parser.Tactic.decide,
      `Lean.Parser.Command.variable, `Lean.Parser.Command.declaration,
      `Lean.Parser.Command.derivingClass, `Lean.Parser.Tactic.optConfig,
      `Lean.Parser.Tactic.posConfigItem],
    k ∈ kinds := by decide +kernel

/-! ## The gate that runs the check -/

/-- What the gate does and reports, given what the check decided, whether the build and replay ended
with 0, and the rules' verdict on the finished build. -/
abbrev GateRun : Type := Outcome → Bool → Regula.Closed.Verdict → Report × List Step

/-- The contract of the gate. A refusal or a failure to read stops it before anything is compiled, the
rules run only on a build that ended with 0, and the report says which verdict it is. -/
def fullGateRecord : IntentRecord GateRun where
  shape := .function Outcome (fun _ => Bool → Regula.Closed.Verdict → Report × List Step)
  dom := []
  props := [
    ⟨"a refused project is compiled by nothing",
      fun g => ∀ b v, g .refused b v = (.refused, [.read])⟩,
    ⟨"a project that could not be read is compiled by nothing",
      fun g => ∀ b v, g .incomplete b v = (.incomplete, [.read])⟩,
    ⟨"an admitted project gets the full verdict, from the rules on a build that ended with 0",
      fun g => ∀ v, g .admitted true v = (.full v, [.read, .build, .rules])⟩,
    ⟨"an admitted project whose build failed gets a full verdict of failure",
      fun g => ∀ v, g .admitted false v = (.full .fail, [.read, .build])⟩,
    ⟨"a project with only the proof verdict gets it, from the rules on a build that ended with 0",
      fun g => ∀ v, g .proofOnly true v = (.proof v, [.read, .build, .rules])⟩,
    ⟨"a project with only the proof verdict whose build failed gets a proof verdict of failure",
      fun g => ∀ v, g .proofOnly false v = (.proof .fail, [.read, .build])⟩]
  vocab := []

theorem fullGate_meets_iff (g : GateRun) :
    fullGateRecord.Meets g ↔
      (∀ b v, g .refused b v = (.refused, [.read])) ∧
      (∀ b v, g .incomplete b v = (.incomplete, [.read])) ∧
      (∀ v, g .admitted true v = (.full v, [.read, .build, .rules])) ∧
      (∀ v, g .admitted false v = (.full .fail, [.read, .build])) ∧
      (∀ v, g .proofOnly true v = (.proof v, [.read, .build, .rules])) ∧
      (∀ v, g .proofOnly false v = (.proof .fail, [.read, .build])) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, fullGateRecord]

theorem fullGate_o5 : O5 fullGateRecord .eq := by
  rw [o5_correct]
  intro u v hu hv
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := (fullGate_meets_iff u).mp ⟨hu.1, hu.2⟩
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := (fullGate_meets_iff v).mp ⟨hv.1, hv.2⟩
  funext o b w
  cases o <;> cases b <;> simp_all

/-- O4: the gate is a function. -/
theorem fullGate_o4 : O4 fullGateRecord := o4_function _ rfl

/-- O2 at confirmation: the gate's record has no domain hypothesis and no predicate. -/
theorem fullGate_o2 : O2 fullGateRecord := by
  rw [o2_correct]
  exact ⟨⟨fun _ _ _ => (.incomplete, []), by simp [fullGateRecord]⟩, by simp [fullGateRecord]⟩

/-- O3: each clause can fail, for a run that takes no step. -/
theorem fullGate_o3 : O3 fullGateRecord := by
  rw [o3_correct]
  intro p hp
  simp only [fullGateRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨fun _ _ _ => (.incomplete, []), fun h => ?_⟩
  · simpa using h true .pass
  · simpa using h true .pass
  · simpa using h .pass
  · simpa using h .pass
  · simpa using h .pass
  · simpa using h .pass

/-- A build is compiled only after the check, and only when the check let it: `build` is in the steps
only for an admitted or proof-only outcome, and it follows `read`. -/
theorem build_only_after_check {g : GateRun} (h : fullGateRecord.Meets g) (o b v) :
    Step.build ∈ (g o b v).2 → (o = .admitted ∨ o = .proofOnly) ∧ (g o b v).2.head? = some .read := by
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := (fullGate_meets_iff g).mp h
  cases o <;> cases b <;> simp_all

/-- Mathlib in a build's imports never gets a full verdict: `Regula.Language.Report.full` needs an
admitted outcome, which `admitted_iff` refuses. -/
theorem full_needs_no_mathlib {d : Reading → Outcome} {g : GateRun} (hd : languageRecord.Meets d)
    (hg : fullGateRecord.Meets g) (r : Reading) (b v w)
    (hf : (g (d r) b v).1 = .full w) : ¬ MathlibReached r := by
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := (fullGate_meets_iff g).mp hg
  have ha : d r = .admitted := by
    cases ho : d r <;> rw [ho] at hf <;> cases b <;> simp_all
  exact ((admitted_iff hd r).mp ha).2.2.2.1

/-! ## What stays a hypothesis about Lean -/

/-- What Lean does at one version, which no proof in Lean can reach, because `Lean.Parser.parseCommand`
is `partial` and Lean's elaborator has no model here. These are hypotheses, never axioms: the theorem
that uses them names them, and they are re-read at each Lean upgrade (`README.md`, "H1 and H2").

- `h1`: the tree the reader got is the tree Lean's frontend elaborates, for a file of a reading that
  the check admits.
- `h2`: Lean's elaboration of such trees runs no code written in the project and installs nothing that
  replaces what the compiler runs for a definition. -/
structure LeanBehaviour where
  /-- Lean's frontend elaborates these trees for this file. -/
  Elaborates : FileRead → List Syntax → Prop
  /-- Elaborating these trees runs no code that the project wrote and replaces no compiled code. -/
  NoProjectCode : List Syntax → Prop
  /-- H1. -/
  h1 : ∀ r, Inside r → ∀ f ∈ r.files, Elaborates f f.commands
  /-- H2. -/
  h2 : ∀ scopedParsers (ts : List Syntax), (∀ t ∈ ts, TreeAdmitted scopedParsers t) → NoProjectCode ts

/-- What an admitted reading means, under H1 and H2 and no more: for each file, the trees Lean
elaborates are ones that run no project code. The proved part is `admitted_iff`; this theorem only
composes it with the hypotheses. -/
theorem admitted_runs_no_project_code (L : LeanBehaviour) {d : Reading → Outcome}
    (hd : languageRecord.Meets d) (r : Reading) (ha : d r = .admitted) :
    ∀ f ∈ r.files, ∃ ts, L.Elaborates f ts ∧ L.NoProjectCode ts := by
  have hi := (admitted_iff hd r).mp ha
  intro f hf
  have hadm : FileAdmitted f := by
    cases hr : f.inRoot with
    | true => exact hi.2.2.2.2.2.1 f hf hr
    | false => exact hi.2.2.2.2.2.2 f hf hr
  exact ⟨f.commands, L.h1 r hi f hf, L.h2 f.scopedParsers f.commands hadm.2.2.2.2⟩

end RegulaSpecification.Language
