/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Proofs.Paths
import RegulaSpecification.Proofs.Load

/-!
# What the rules ask of a build, by what Lean answered

`RegulaSpecification.Loader.LoadFloor` says what a build must be for the loader and the rules to pass it, in the terms of
`Regula.Load.Facts`, the checker's own reading of what Lean answered. As a premise of an owed pass it would apply the checker's
functions to an answer. `BuildAnswer` holds only the answers: what Lean's import gave, where Lean's search found each `.olean`, and the
two library directories that Lake's load named. `BuildAnswer.Floor` states the same requirement over them, through Lean's own fields and
functions and the components of a path. `loadFloor_iff` relates the two in both directions, so `pass_iff_answer` states the checker's
decision against a property that names none of its functions.
-/

namespace RegulaSpecification.Effects

open Lean (Name ConstantInfo ConstantKind)
open System (FilePath)
open Regula.Effect
open RegulaSpecification.Loader

variable {L E : Type}

/-- What a finished build answered: what Lean's import gave, the toolchain's and the root package's library directories as Lake's load
named them, and each module of the import's header with where Lean found its `.olean`, in the header's order. -/
structure BuildAnswer where
  /-- What Lean's import gave. -/
  env : Lean.Environment
  /-- The toolchain's library directory. -/
  toolchainDir : FilePath
  /-- The root package's library directory. -/
  rootDir : FilePath
  /-- Each module, with where Lean found its `.olean`. -/
  places : List (Name × FilePath)

/-- What a run received of a finished build: `a` is what the answers of `t` state, for the workspace `root`, whose default targets give
the modules `roots`. -/
def BuildAnswered (t : List (Event L E)) (root : Root L) (a : BuildAnswer) (roots : List Name) : Prop :=
  ∃ modules,
    DefaultModules t root root.defaultTargets modules ∧ roots = modules.map (·.1) ∧
    (⟨.importForRules root.leanPath roots.toArray, .ok a.env⟩ : Event L E) ∈ t ∧
    a.toolchainDir = root.leanLib ∧ a.rootDir = root.rootLib ∧
    a.places.map (·.1) = a.env.header.moduleNames.toList ∧
    ∀ x ∈ a.places, (⟨.findOLean root.leanPath x.1, .ok x.2⟩ : Event L E) ∈ t

/-- What the rules read of a constant by its names: those that its type and value mention, each once in the order of their first
occurrence, the fields that `Lean.collectAxioms` walks. -/
def namesOf : ConstantInfo → List Name
  | .axiomInfo v => v.type.getUsedConstants.toList.eraseDups
  | .defnInfo v => (v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList).eraseDups
  | .thmInfo v => (v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList).eraseDups
  | .opaqueInfo v => (v.type.getUsedConstants.toList ++ v.value.getUsedConstants.toList).eraseDups
  | .quotInfo _ => []
  | .ctorInfo v => v.type.getUsedConstants.toList.eraseDups
  | .recInfo v => v.type.getUsedConstants.toList.eraseDups
  | .inductInfo v => (v.type.getUsedConstants.toList ++ v.ctors).eraseDups

/-- What the value of a constant mentions, and nothing of a constant that has no value. -/
def valueNamesOf : ConstantInfo → List Name
  | .defnInfo v => v.value.getUsedConstants.toList
  | .thmInfo v => v.value.getUsedConstants.toList
  | .opaqueInfo v => v.value.getUsedConstants.toList
  | .axiomInfo _ | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => []

/-- Two constants of which the rules read the same: the same kind, the same two flags and the same names. -/
def SameRead (k v : ConstantInfo) : Prop :=
  ConstantKind.ofConstantInfo k = ConstantKind.ofConstantInfo v ∧ k.isUnsafe = v.isUnsafe ∧ k.isPartial = v.isPartial ∧
    namesOf k = namesOf v ∧ valueNamesOf k = valueNamesOf v

namespace BuildAnswer

variable (a : BuildAnswer)

/-- The module that holds a constant, by Lean's index, with where its `.olean` lies. -/
def place? (n : Name) : Option (Name × FilePath) :=
  (a.env.getModuleIdxFor? n).bind fun idx => a.places[idx.toNat]?

/-- A module whose `.olean` lies below the root package's library directory is claimed. -/
def Claimed (m : Name) : Prop :=
  ∃ olean, (m, olean) ∈ a.places ∧ StrictlyBelow a.rootDir olean

/-- What the own data of a loaded module states of a name. -/
def Stated (n : Name) (v : ConstantInfo) : Prop :=
  ∃ data ∈ a.env.header.moduleData, (n, v) ∈ data.constNames.zip data.constants

/-- What a constant mentions: what the constant that the environment keeps mentions, and what any constant that a module states of its
name mentions. -/
def Mention (c u : Name) : Prop :=
  ∃ k, a.env.constants.map₁[c]? = some k ∧ (Mentions k u ∨ ∃ v, a.Stated c v ∧ Mentions v u)

/-- A name that is an axiom: the constant that the environment keeps, or any that a module states of it. -/
def Axiom (n : Name) : Prop :=
  ∃ k, a.env.constants.map₁[n]? = some k ∧ (AxiomInfo k ∨ ∃ v, a.Stated n v ∧ AxiomInfo v)

/-- What a constant reaches through what it mentions. -/
inductive Reaches : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : Reaches c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} : a.Mention c u → Reaches u e → Reaches c e

/-- A constant whose module lies below the toolchain's library directory. -/
def InToolchain (n : Name) : Prop :=
  ∃ x, a.place? n = some x ∧ StrictlyBelow a.toolchainDir x.2

/-- An axiom that a profile admits. -/
def Admits : Regula.Closed.Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, n => (n = ``propext ∨ n = ``Quot.sound) ∧ a.InToolchain n
  | .standardLogical, n => (n = ``propext ∨ n = ``Quot.sound ∨ n = ``Classical.choice) ∧ a.InToolchain n

/-- A constant of the exempted form beside a safe definition of the module `m`, which names no origin. -/
def Helper (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  info.isPartial = true ∧ info.isUnsafe = false ∧
    Lean.Compiler.getImplementedBy? a.env n = none ∧ Lean.isExtern a.env n = false ∧
    ∃ b v, n = .str b "_unsafe_rec" ∧ a.env.constants.map₁[b]? = some (.defnInfo v) ∧
      (∀ w, a.Stated b w → ¬ AxiomInfo w) ∧
      (a.place? b).map (·.1) = some m ∧ (ConstantInfo.defnInfo v).isUnsafe = false ∧
      (ConstantInfo.defnInfo v).isPartial = false ∧
      Lean.Compiler.getImplementedBy? a.env b = none ∧ Lean.isExtern a.env b = false

/-- A constant that a claimed module's own `.olean` holds. -/
def Own (m n : Name) (info : ConstantInfo) : Prop :=
  ∃ (k : Nat) (olean : FilePath) (data : Lean.ModuleData), a.places[k]? = some (m, olean) ∧ StrictlyBelow a.rootDir olean ∧
    a.env.header.moduleData[k]? = some data ∧ (n, info) ∈ data.constNames.zip data.constants

/-- A claimed module's own constant that the environment shows to the rules: it keeps a constant of that name, in a claimed module, of
which the rules read the same. -/
def Shown (n : Name) (info : ConstantInfo) : Prop :=
  ∃ k x, a.env.constants.map₁[n]? = some k ∧ a.place? n = some x ∧ SameRead k info ∧ StrictlyBelow a.rootDir x.2

/-- **What the rules ask of a finished build**, by what Lean and Lake answered and with none of the checker's functions. -/
structure Floor (roots : List Name) (p : Regula.Closed.Profile) : Prop where
  /-- Each module of the default targets is claimed. -/
  roots : ∀ r ∈ roots, a.Claimed r
  /-- Each constant has a module. -/
  placed : ∀ n info, a.env.constants.map₁[n]? = some info → ∃ x, a.place? n = some x
  /-- Each mentioned constant is held. -/
  closed : ∀ n u, a.Mention n u → ∃ info', a.env.constants.map₁[u]? = some info'
  /-- At least one module is claimed. -/
  claims : ∃ m, a.Claimed m
  /-- Each constant of a claimed module is no axiom, is a helper if it has a helper's marks, mentions no loop construct and reaches only axioms that the profile admits. -/
  floor : ∀ n info m, a.env.constants.map₁[n]? = some info → (a.place? n).map (·.1) = some m → a.Claimed m →
    ¬ a.Axiom n ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") → a.Helper n info m) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ e, a.Reaches n e → a.Axiom e → a.Admits p e
  /-- A claimed module's own constant that the environment does not show is a safe theorem with no helper's name, whose value mentions no
  loop construct, and each constant it mentions is held and reaches only axioms that the profile admits. -/
  unshown : ∀ m n info, a.Own m n info → ¬ a.Shown n info →
    (∃ t, info = .thmInfo t) ∧ info.isUnsafe = false ∧ info.isPartial = false ∧
    (∀ b, n ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ u, Mentions info u → (∃ k, a.env.constants.map₁[u]? = some k) ∧ ∀ e, a.Reaches u e → a.Axiom e → a.Admits p e

/-! ## The checker's reading, against these answers -/

/-- The answers that a reading of the checker holds. -/
def ofFacts (f : Regula.Load.Facts) : BuildAnswer where
  env := f.env
  toolchainDir := f.toolchainDir
  rootDir := f.rootDir
  places := f.modules.toList.map fun m => (m.name, m.olean)

variable (f : Regula.Load.Facts)

theorem ofFacts_getElem (k : Nat) :
    (ofFacts f).places[k]? = (f.modules[k]?).map fun m => (m.name, m.olean) := by
  simp [ofFacts]

theorem place_ofFacts (n : Name) : (ofFacts f).place? n = (f.info? n).map fun m => (m.name, m.olean) := by
  simp only [place?, Regula.Load.Facts.info?, ofFacts_getElem]
  cases h : f.env.getModuleIdxFor? n <;> simp [ofFacts, h]

theorem placeName_ofFacts (n : Name) : ((ofFacts f).place? n).map (·.1) = f.moduleOf? n := by
  rw [place_ofFacts]
  simp [Regula.Load.Facts.moduleOf?, Function.comp_def]

theorem claimed_ofFacts (m : Name) : (ofFacts f).Claimed m ↔ m ∈ f.claimed := by
  rw [mem_claimed_place]
  simp only [Claimed, ofFacts, List.mem_map, Array.mem_toList_iff, Prod.mk.injEq, below_eq_true_iff]
  constructor
  · rintro ⟨o, ⟨lm, hm, rfl, rfl⟩, hb⟩
    exact ⟨lm, hm, rfl, hb⟩
  · rintro ⟨lm, hm, rfl, hb⟩
    exact ⟨lm.olean, ⟨lm, hm, rfl, rfl⟩, hb⟩

theorem stated_ofFacts (n : Name) (v : ConstantInfo) : (ofFacts f).Stated n v ↔ v ∈ f.stated.getD n [] :=
  mem_stated.symm

theorem mention_ofFacts (c u : Name) : (ofFacts f).Mention c u ↔ EnvMentions f c u := by
  simp only [Mention, EnvMentions, stated_ofFacts]
  rfl

theorem axiom_ofFacts (n : Name) : (ofFacts f).Axiom n ↔ EnvAxiom f n := by
  simp only [Axiom, EnvAxiom, stated_ofFacts]
  rfl

theorem reaches_ofFacts (c e : Name) : (ofFacts f).Reaches c e ↔ EnvReaches f c e := by
  constructor
  · intro h
    induction h with
    | refl c => exact .refl c
    | step hm _ ih => exact .step ((mention_ofFacts f _ _).mp hm) ih
  · intro h
    induction h with
    | refl c => exact .refl c
    | step hm _ ih => exact .step ((mention_ofFacts f _ _).mpr hm) ih

theorem inToolchain_ofFacts (n : Name) : (ofFacts f).InToolchain n ↔ EnvToolchain f n := by
  rw [toolchain_place]
  simp only [InToolchain, place?, ofFacts_getElem, Option.bind_eq_some_iff, Option.map_eq_some_iff, below_eq_true_iff]
  constructor
  · rintro ⟨x, ⟨idx, hi, lm, hm, rfl⟩, hb⟩
    exact ⟨idx, lm, hi, hm, hb⟩
  · rintro ⟨idx, lm, hi, hm, hb⟩
    exact ⟨(lm.name, lm.olean), ⟨idx, hi, lm, hm, rfl⟩, hb⟩

theorem admits_ofFacts (p : Regula.Closed.Profile) (n : Name) : (ofFacts f).Admits p n ↔ EnvAdmits f p n := by
  cases p <;> simp only [Admits, EnvAdmits, inToolchain_ofFacts]

theorem helper_ofFacts (n : Name) (info : ConstantInfo) (m : Name) : (ofFacts f).Helper n info m ↔ EnvHelper f n info m := by
  simp only [Helper, EnvHelper, stated_ofFacts, placeName_ofFacts]
  rfl

theorem own_ofFacts (m n : Name) (info : ConstantInfo) : (ofFacts f).Own m n info ↔ (m, n, info) ∈ f.claimedConstants := by
  rw [mem_claimedConstants]
  simp only [Own, ofFacts_getElem, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k, o, data, ⟨lm, hm, rfl, rfl⟩, hb, hd, hx⟩
    refine ⟨k, lm, data, hm, ?_, rfl, hd, hx⟩
    have hp := f.placed lm (mem_modules_of_getElem hm)
    rw [hp]
    exact (below_eq_true_iff _ _).mpr hb
  · rintro ⟨k, lm, data, hm, hc, rfl, hd, hx⟩
    refine ⟨k, lm.olean, data, ⟨lm, hm, rfl, rfl⟩, ?_, hd, hx⟩
    have hp := f.placed lm (mem_modules_of_getElem hm)
    rw [hp] at hc
    exact (below_eq_true_iff _ _).mp hc

end BuildAnswer

/-! ## What the rules read of a constant -/

/-- The fold that keeps each first occurrence is Lean's `List.eraseDups`. -/
theorem dedup_eq_eraseDups (all : Array Name) : (Regula.Load.dedup all).toList = all.toList.eraseDups := by
  have key : ∀ (l : List Name) (acc : Array Name) (bs : List Name), acc.toList = bs.reverse →
      (l.foldl (fun acc n => if acc.contains n then acc else acc.push n) acc).toList = List.eraseDupsBy.loop (· == ·) l bs := by
    intro l
    induction l with
    | nil =>
      intro acc bs h
      simpa [List.eraseDupsBy.loop] using h
    | cons a l ih =>
      intro acc bs h
      have hc : acc.contains a = bs.any (a == ·) := by
        have hm : a ∈ acc ↔ a ∈ bs := by rw [← Array.mem_toList_iff, h, List.mem_reverse]
        rw [Bool.eq_iff_iff]
        constructor
        · intro hx
          exact List.any_eq_true.mpr ⟨a, hm.mp (by simpa using hx), by simp⟩
        · intro hx
          obtain ⟨x, hxm, he⟩ := List.any_eq_true.mp hx
          have hax : a = x := by simpa using he
          subst hax
          simpa using hm.mpr hxm
      simp only [List.foldl_cons, hc]
      rw [List.eraseDupsBy.loop]
      cases hb : bs.any (a == ·) with
      | true => simpa using ih acc bs h
      | false => simpa using ih (acc.push a) (a :: bs) (by simp [h])
  simp only [Regula.Load.dedup, List.eraseDups, List.eraseDupsBy]
  rw [← Array.foldl_toList]
  exact key _ _ _ rfl

/-- The kinds of two constants agree as Lean's kinds do. -/
theorem kindOf_eq_iff (k v : ConstantInfo) :
    Regula.Load.kindOf k = Regula.Load.kindOf v ↔ ConstantKind.ofConstantInfo k = ConstantKind.ofConstantInfo v := by
  cases k <;> cases v <;> simp [Regula.Load.kindOf, ConstantKind.ofConstantInfo]

/-- The safety of two constants agrees as their two flags do. -/
theorem safetyOf_eq_iff (k v : ConstantInfo) :
    Regula.Load.safetyOf k = Regula.Load.safetyOf v ↔ k.isUnsafe = v.isUnsafe ∧ k.isPartial = v.isPartial := by
  have hk := not_unsafe_of_partial k
  have hv := not_unsafe_of_partial v
  simp only [Regula.Load.safetyOf]
  cases h1 : k.isUnsafe <;> cases h2 : k.isPartial <;> cases h3 : v.isUnsafe <;> cases h4 : v.isPartial <;> simp_all

theorem usesOf_toList (k : ConstantInfo) : (Regula.Load.usesOf k).toList = namesOf k := by
  cases k <;> simp [Regula.Load.usesOf, namesOf, dedup_eq_eraseDups]

theorem valueUsesOf_toList (k : ConstantInfo) : (Regula.Load.valueUsesOf k).toList = valueNamesOf k := by
  cases k <;> rfl

theorem readOf_eq_iff (k v : ConstantInfo) : Regula.Load.readOf k = Regula.Load.readOf v ↔ SameRead k v := by
  simp only [Regula.Load.readOf, Prod.mk.injEq, SameRead, kindOf_eq_iff, safetyOf_eq_iff, usesOf_toList, valueUsesOf_toList,
    and_assoc]

theorem shown_ofFacts (f : Regula.Load.Facts) (m n : Name) (info : ConstantInfo) :
    (BuildAnswer.ofFacts f).Shown n info ↔ f.shown (m, n, info) = true := by
  simp only [BuildAnswer.Shown, BuildAnswer.place_ofFacts, Regula.Load.Facts.shown, Option.map_eq_some_iff]
  show _ ↔ (match f.env.constants.map₁[n]?, f.info? n with
    | some kept, some m => decide (Regula.Load.readOf kept = Regula.Load.readOf info) && m.claimed
    | none, _ | some _, none => false) = true
  simp only [BuildAnswer.ofFacts]
  cases h1 : f.env.constants.map₁[n]? with
  | none => simp
  | some kept =>
    cases h2 : f.info? n with
    | none => simp
    | some lm =>
      have hp : lm.claimed = Regula.Load.below f.rootDir lm.olean := by
        have hm : lm ∈ f.modules := by
          simp only [Regula.Load.Facts.info?, Option.bind_eq_some_iff] at h2
          obtain ⟨idx, -, hk⟩ := h2
          exact mem_modules_of_getElem hk
        have hq := f.placed lm hm
        rw [hq]
        rfl
      simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq, hp, below_eq_true_iff, readOf_eq_iff]
      constructor
      · rintro ⟨k, x, rfl, ⟨y, rfl, rfl⟩, h3, h4⟩
        exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩
        exact ⟨kept, (lm.name, lm.olean), rfl, ⟨lm, rfl, rfl⟩, h3, h4⟩

theorem kindOf_theorem_iff (info : ConstantInfo) : Regula.Load.kindOf info = .theorem ↔ ∃ t, info = .thmInfo t := by
  cases info <;> simp [Regula.Load.kindOf]

/-- **`LoadFloor`, the requirement over the checker's reading, is `BuildAnswer.Floor` of the answers that reading holds**, in both directions. -/
theorem loadFloor_iff (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile) :
    LoadFloor f roots p ↔ (BuildAnswer.ofFacts f).Floor roots p := by
  have hq (n : Name) : (∃ x, (BuildAnswer.ofFacts f).place? n = some x) ↔ ∃ m, f.info? n = some m := by
    simp only [BuildAnswer.place_ofFacts, Option.map_eq_some_iff]
    constructor
    · rintro ⟨x, m, h, -⟩
      exact ⟨m, h⟩
    · rintro ⟨m, h⟩
      exact ⟨_, m, h, rfl⟩
  have hclaims : (∃ m, (BuildAnswer.ofFacts f).Claimed m) ↔ f.claimed ≠ [] := by
    simp only [BuildAnswer.claimed_ofFacts]
    constructor
    · rintro ⟨m, hm⟩ he
      rw [he] at hm
      cases hm
    · intro he
      cases hc : f.claimed with
      | nil => exact absurd hc he
      | cons x xs => exact ⟨x, by simp⟩
  have hfloor : (∀ n info m, (BuildAnswer.ofFacts f).env.constants.map₁[n]? = some info → ((BuildAnswer.ofFacts f).place? n).map (·.1) = some m →
      (BuildAnswer.ofFacts f).Claimed m →
      ¬ (BuildAnswer.ofFacts f).Axiom n ∧
      ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") → (BuildAnswer.ofFacts f).Helper n info m) ∧
      (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
      ∀ e, (BuildAnswer.ofFacts f).Reaches n e → (BuildAnswer.ofFacts f).Axiom e → (BuildAnswer.ofFacts f).Admits p e) ↔ EnvFloor f p := by
    simp only [EnvFloor, BuildAnswer.placeName_ofFacts, BuildAnswer.claimed_ofFacts, BuildAnswer.axiom_ofFacts, BuildAnswer.helper_ofFacts,
      BuildAnswer.reaches_ofFacts, BuildAnswer.admits_ofFacts]
    rfl
  have hunshown : (∀ m n info, (BuildAnswer.ofFacts f).Own m n info → ¬ (BuildAnswer.ofFacts f).Shown n info →
      (∃ t, info = .thmInfo t) ∧ info.isUnsafe = false ∧ info.isPartial = false ∧
      (∀ b, n ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
      ∀ u, Mentions info u → (∃ k, (BuildAnswer.ofFacts f).env.constants.map₁[u]? = some k) ∧
        ∀ e, (BuildAnswer.ofFacts f).Reaches u e → (BuildAnswer.ofFacts f).Axiom e → (BuildAnswer.ofFacts f).Admits p e) ↔ EnvUnshown f p := by
    simp only [BuildAnswer.reaches_ofFacts, BuildAnswer.axiom_ofFacts, BuildAnswer.admits_ofFacts, BuildAnswer.own_ofFacts]
    constructor
    · intro h x hx hs
      obtain ⟨m, n, info⟩ := x
      have hn : ¬ (BuildAnswer.ofFacts f).Shown n info := fun hh => by
        rw [(shown_ofFacts f m n info).mp hh] at hs
        cases hs
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h m n info hx hn
      exact ⟨(kindOf_theorem_iff _).mpr h1, (safetyOf_safe _).mpr ⟨h2, h3⟩, h4, h5, h6⟩
    · intro h m n info hx hn
      have hs : f.shown (m, n, info) = false := by
        cases hv : f.shown (m, n, info) with
        | false => rfl
        | true => exact absurd ((shown_ofFacts f m n info).mpr hv) hn
      obtain ⟨h1, h2, h3⟩ := h _ hx hs
      obtain ⟨h4, h5⟩ := (safetyOf_safe _).mp h2
      exact ⟨(kindOf_theorem_iff _).mp h1, h4, h5, h3⟩
  constructor
  · intro h
    refine ⟨fun r hr => (BuildAnswer.claimed_ofFacts f r).mpr (h.roots r hr), fun n info hn => (hq n).mpr (h.placed n info hn),
      fun n u hm => h.form.closed n u ((BuildAnswer.mention_ofFacts f n u).mp hm), hclaims.mpr h.form.claims, hfloor.mpr h.floor, hunshown.mpr h.unshown⟩
  · intro h
    exact ⟨fun r hr => (BuildAnswer.claimed_ofFacts f r).mp (h.roots r hr), fun n info hn => (hq n).mp (h.placed n info hn),
      ⟨fun n u hm => h.closed n u ((BuildAnswer.mention_ofFacts f n u).mpr hm), hclaims.mp h.claims⟩, hfloor.mp h.floor, hunshown.mp h.unshown⟩

/-- **The checker's verdict on a build is a pass exactly on `BuildAnswer.Floor` of what the build answered.** -/
theorem pass_iff_answer (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile) :
    (Regula.Closed.decision (f.input roots p)).verdict = .pass ↔ (BuildAnswer.ofFacts f).Floor roots p :=
  pass_iff_floor.trans (loadFloor_iff f roots p)

/-- A reading of the checker is an answer of the run. -/
theorem BuildRead.answered {t : List (Event L E)} {root : Root L} {f : Regula.Load.Facts} {roots : List Name}
    (h : BuildRead t root f roots) : BuildAnswered t root (BuildAnswer.ofFacts f) roots := by
  obtain ⟨modules, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨modules, h1, h2, h3, h4, h5, ?_, ?_⟩
  · simpa [BuildAnswer.ofFacts, Function.comp_def] using f.names
  · intro x hx
    simp only [BuildAnswer.ofFacts, List.mem_map, Array.mem_toList_iff] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact h6 m hm

end RegulaSpecification.Effects
