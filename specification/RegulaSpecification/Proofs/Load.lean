/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.Load
import Regula.Shell
import RegulaSpecification.Proofs.Verdict

/-!
# The loader, against the environment

`Regula.Load.Facts.input` is the pure function that fills the closed input from a loaded
environment, and `Regula.Closed.Input.report` the verdict that the checker gives on that input.
`pass_iff` relates the two to the environment alone: for every environment, a pass is exactly
`EnvForm` and `EnvFloor`, two statements that mention no field of the input. Each constant is read
from
`Environment.constants.map₁` by name. What a name mentions, and whether it names an axiom, is read
from the fields of that `ConstantInfo` and of each constant of the name that any loaded module's own
data states (`EnvMentions`, `EnvAxiom`, `mem_usesIn`), and `mem_stated` anchors those in
`header.moduleData`. So an axiom or a chain of mentions that Lean's import drops still counts. On a
pass, each axiom reached that way from a constant of a claimed module is one that the profile admits
(`EnvFloor`). `pass_held` states a pass of each constant of a claimed module as that module's own
`.olean` states it, also when Lean's import replaced it.

So a loader that dropped a constant, a field or a mention would fail these proofs in the gate's
build of this package. What they leave assumed is Lean's and Lake's behaviour: that `map₁` holds the
constants that `Lean.importModules` keeps and `header.moduleData` what each `.olean` states, what
each query of the environment returns, that `Expr.getUsedConstants` lists each constant of an
expression, and that Lake names the modules of the default targets. The specification's trusted base
lists them. `Proofs/Shell.lean` states the run that gives this function what Lean and Lake returned. `Proofs/Occurrences.lean` states two of what Lean's
interfaces report as hypotheses of a theorem.
-/

namespace RegulaSpecification

open Lean (Name ConstantInfo)
open Link

namespace Loader

variable {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}
  {i : Regula.Closed.Input}

/-! ## What a constant mentions -/

/-- What a constant mentions, read from the fields of its `ConstantInfo`: the type and value of a
definition, theorem or opaque constant, the type of an axiom, constructor or recursor, the type and
constructors of an inductive type, and nothing of a quotient. -/
def Mentions : ConstantInfo → Name → Prop
  | .axiomInfo v, u => u ∈ v.type.getUsedConstants
  | .defnInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .thmInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .opaqueInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .quotInfo _, _ => False
  | .ctorInfo v, u => u ∈ v.type.getUsedConstants
  | .recInfo v, u => u ∈ v.type.getUsedConstants
  | .inductInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.ctors

/-- What the value of a constant mentions, and nothing of a constant that has no value. -/
def ValueMentions : ConstantInfo → Name → Prop
  | .defnInfo v, u => u ∈ v.value.getUsedConstants
  | .thmInfo v, u => u ∈ v.value.getUsedConstants
  | .opaqueInfo v, u => u ∈ v.value.getUsedConstants
  | .axiomInfo _, _ | .quotInfo _, _ | .inductInfo _, _ | .ctorInfo _, _ | .recInfo _, _ => False

/-- The fold that removes repeated names keeps each name. -/
theorem mem_dedupFold (l : List Name) (acc : Array Name) (u : Name) :
    u ∈ l.foldl (fun acc n => if acc.contains n then acc else acc.push n) acc ↔
      u ∈ l ∨ u ∈ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    split
    · rename_i hc
      have ha : a ∈ acc := by simpa using hc
      constructor
      · rintro (h | h)
        · exact .inl (.inr h)
        · exact .inr h
      · rintro ((rfl | h) | h)
        · exact .inr ha
        · exact .inl h
        · exact .inr h
    · simp only [Array.mem_push]
      constructor
      · rintro (h | h | rfl)
        · exact .inl (.inr h)
        · exact .inr h
        · exact .inl (.inl rfl)
      · rintro ((rfl | h) | h)
        · exact .inr (.inr rfl)
        · exact .inl h
        · exact .inr (.inl h)

/-- `dedup` keeps exactly the names it is given. -/
theorem mem_dedup (all : Array Name) (u : Name) : u ∈ Regula.Load.dedup all ↔ u ∈ all := by
  unfold Regula.Load.dedup
  rw [← Array.foldl_toList, mem_dedupFold]
  simp

/-- `usesOf` lists exactly what a constant mentions. -/
theorem mem_usesOf (info : ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.usesOf info).toList ↔ Mentions info u := by
  unfold Regula.Load.usesOf
  rw [Array.mem_toList_iff, mem_dedup]
  cases info <;> simp [Mentions]

/-- The fold of `usesIn` collects what each constant of the list mentions. -/
theorem mem_usesFold (l : List ConstantInfo) (acc : Array Name) (u : Name) :
    u ∈ l.foldl (fun acc v => acc ++ Regula.Load.usesOf v) acc ↔
      u ∈ acc ∨ ∃ v ∈ l, Mentions v u := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    have ha : u ∈ Regula.Load.usesOf a ↔ Mentions a u := by
      simpa using mem_usesOf a u
    simp only [List.foldl_cons, ih, Array.mem_append, ha, List.mem_cons, exists_eq_or_imp, or_assoc]

/-- `usesIn` lists exactly what a constant that the environment keeps mentions, with what each
constant of `stated` mentions. -/
theorem mem_usesIn (info : ConstantInfo) (stated : List ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.usesIn info stated).toList ↔ Mentions info u ∨ ∃ v ∈ stated, Mentions v u := by
  have ha : u ∈ Regula.Load.usesOf info ↔ Mentions info u := by
    simpa using mem_usesOf info u
  unfold Regula.Load.usesIn
  rw [Array.mem_toList_iff, mem_dedup, mem_usesFold, ha]

/-- `valueUsesOf` lists exactly what the value of a constant mentions. -/
theorem mem_valueUsesOf (info : ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.valueUsesOf info).toList ↔ ValueMentions info u := by
  cases info <;> simp [Regula.Load.valueUsesOf, ValueMentions]

/-! ## What the loaded modules state -/

/-- The inner fold of `Facts.stated` adds each constant of the list to the list of its name. -/
theorem mem_statedPairs (l : List (Name × ConstantInfo))
    (acc : Std.HashMap Name (List ConstantInfo)) (n : Name) (v : ConstantInfo) :
    v ∈ (l.foldl (fun acc x => acc.insert x.1 (x.2 :: acc.getD x.1 [])) acc).getD n [] ↔
      (n, v) ∈ l ∨ v ∈ acc.getD n [] := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rcases a with ⟨c, w⟩
    simp only [List.foldl_cons, ih, List.mem_cons, Prod.mk.injEq, Std.HashMap.getD_insert]
    by_cases hc : c = n
    · subst hc
      simp only [beq_self_eq_true, ite_true, List.mem_cons, true_and]
      constructor
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
    · have hb : (c == n) = false := by simpa using hc
      have hn : ¬ n = c := fun h => hc h.symm
      simp [hb, hn]

/-- The outer fold of `Facts.stated` adds the constants of each module's data. -/
theorem mem_statedData (l : List Lean.ModuleData)
    (acc : Std.HashMap Name (List ConstantInfo)) (n : Name) (v : ConstantInfo) :
    v ∈ (l.foldl (fun acc data => (data.constNames.zip data.constants).foldl
        (fun acc x => acc.insert x.1 (x.2 :: acc.getD x.1 [])) acc) acc).getD n [] ↔
      (∃ data ∈ l, (n, v) ∈ data.constNames.zip data.constants) ∨ v ∈ acc.getD n [] := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    have hp := mem_statedPairs (a.constNames.zip a.constants).toList acc n v
    simp only [Array.foldl_toList, Array.mem_toList_iff] at hp
    simp only [List.foldl_cons, ih, hp, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- `Facts.stated` lists of a name exactly what the own data of a loaded module states of it. -/
theorem mem_stated {n : Name} {v : ConstantInfo} :
    v ∈ f.stated.getD n [] ↔ ∃ data ∈ f.env.header.moduleData,
      (n, v) ∈ data.constNames.zip data.constants := by
  have h := mem_statedData f.env.header.moduleData.toList {} n v
  simp only [Array.foldl_toList, Array.mem_toList_iff] at h
  simpa [Regula.Load.Facts.stated] using h

/-! ## The statements over the environment -/

/-- A constant is an axiom, by the constructor of its `ConstantInfo`. -/
def AxiomInfo (k : ConstantInfo) : Prop := ∃ w, k = .axiomInfo w

/-- What the name `c` mentions in the environment: what the constant that the environment keeps
mentions, and what each constant of that name that a loaded module's own data states mentions. -/
def EnvMentions (f : Regula.Load.Facts) (c u : Name) : Prop :=
  ∃ k, f.env.constants.map₁[c]? = some k ∧
    (Mentions k u ∨ ∃ v ∈ f.stated.getD c [], Mentions v u)

/-- The name `a` names an axiom in the environment: the constant that the environment keeps is one,
or a constant of that name that a loaded module's own data states is one. -/
def EnvAxiom (f : Regula.Load.Facts) (a : Name) : Prop :=
  ∃ k, f.env.constants.map₁[a]? = some k ∧
    (AxiomInfo k ∨ ∃ v ∈ f.stated.getD a [], AxiomInfo v)

/-- `c` reaches `e` through what the names of the environment mention. -/
inductive EnvReaches (f : Regula.Load.Facts) : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : EnvReaches f c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} : EnvMentions f c u → EnvReaches f u e → EnvReaches f c e

/-- The closed form of the input, in the terms of the environment: each constant that a name
mentions is held, and at least one module is claimed. -/
structure EnvForm (f : Regula.Load.Facts) : Prop where
  /-- Each mentioned constant is held. -/
  closed : ∀ n u, EnvMentions f n u → ∃ info', f.env.constants.map₁[u]? = some info'
  /-- At least one module is claimed. -/
  claims : f.claimed ≠ []

/-- The constant `a` is one of the toolchain's: the module that holds it lies in its library. -/
def EnvToolchain (f : Regula.Load.Facts) (a : Name) : Prop :=
  ∃ m, f.info? a = some m ∧ m.inToolchain = true

/-- Profile `p` admits the axiom `a` of the environment: one of Lean's three, the toolchain's own
constant of that name, and in the profile's set. -/
def EnvAdmits (f : Regula.Load.Facts) : Regula.Closed.Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, a => (a = ``propext ∨ a = ``Quot.sound) ∧ EnvToolchain f a
  | .standardLogical, a =>
    (a = ``propext ∨ a = ``Quot.sound ∨ a = ``Classical.choice) ∧ EnvToolchain f a

/-- The form of a recursion helper: a partial, safe-flagged constant `b._unsafe_rec` with no
`@[implemented_by]` and not `@[extern]`, beside a safe, total definition `b` of its module of which
the same two hold, and of whose name no loaded module states an axiom. -/
def EnvHelper (f : Regula.Load.Facts) (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  info.isPartial = true ∧ info.isUnsafe = false ∧
    Lean.Compiler.getImplementedBy? f.env n = none ∧ Lean.isExtern f.env n = false ∧
    ∃ b v, n = .str b "_unsafe_rec" ∧ f.env.constants.map₁[b]? = some (.defnInfo v) ∧
      (∀ w ∈ f.stated.getD b [], ¬ AxiomInfo w) ∧
      f.moduleOf? b = some m ∧ (ConstantInfo.defnInfo v).isUnsafe = false ∧
      (ConstantInfo.defnInfo v).isPartial = false ∧
      Lean.Compiler.getImplementedBy? f.env b = none ∧ Lean.isExtern f.env b = false

/-- What RG1001 to RG1006 state of each constant of a claimed module, in the terms of the
environment: no loaded module states an axiom of its name (RG1001). When it is unsafe or partial, or
has a recursion helper's name, it has the form of a recursion helper (RG1006), and its value
mentions no loop construct of Lean (RG1006). Each axiom that it reaches, through what any loaded
module's own
data states, is one that the profile admits (RG1005), which also excludes `sorryAx` (RG1002), a
native proof's axiom (RG1004) and every other axiom (RG1003): `rg1005_of_hole`,
`rg1005_of_compiler`, `rg1005_of_unknown`. -/
def EnvFloor (f : Regula.Load.Facts) (p : Regula.Closed.Profile) : Prop :=
  ∀ n info m, f.env.constants.map₁[n]? = some info → f.moduleOf? n = some m → m ∈ f.claimed →
    ¬ EnvAxiom f n ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      EnvHelper f n info m) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ a, EnvReaches f n a → EnvAxiom f a → EnvAdmits f p a

/-! ## What the facts hold -/

/-- A module of an index is in the modules of the facts. -/
theorem mem_modules_of_getElem {k : Nat} {m : Regula.Load.LoadedModule}
    (h : f.modules[k]? = some m) : m ∈ f.modules :=
  Array.mem_of_getElem? h

/-- A constant's module is in the modules of the facts. -/
theorem mem_modules_of_info {n : Name} {m : Regula.Load.LoadedModule} (h : f.info? n = some m) :
    m ∈ f.modules := by
  simp only [Regula.Load.Facts.info?, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, hm⟩ := h
  exact mem_modules_of_getElem hm

/-- What each index of the facts holds is what the header gives at that index. -/
theorem moduleNames_getElem (f : Regula.Load.Facts) (k : Nat) :
    (f.modules[k]?).map (·.name) = f.env.header.moduleNames[k]? := by
  have h := congrArg (·[k]?) f.names
  simpa using h

/-- The module of a constant is the one that the header gives for it. So this reading of a module
is `Environment.getModuleIdxFor?` and `header.moduleNames`, and nothing that the shell passes in. -/
theorem moduleOf?_eq (f : Regula.Load.Facts) (n : Name) :
    f.moduleOf? n =
      (f.env.getModuleIdxFor? n).bind fun idx => f.env.header.moduleNames[idx.toNat]? := by
  simp only [Regula.Load.Facts.moduleOf?, Regula.Load.Facts.info?]
  cases f.env.getModuleIdxFor? n with
  | none => rfl
  | some idx => exact moduleNames_getElem f idx.toNat

/-- Each claimed module is a module of the facts, whose flag says so. -/
theorem mem_claimed_iff (f : Regula.Load.Facts) (m : Name) :
    m ∈ f.claimed ↔ ∃ lm ∈ f.modules, lm.name = m ∧ lm.claimed = true := by
  simp only [Regula.Load.Facts.claimed, List.mem_map, List.mem_filter, Array.mem_toList_iff]
  constructor
  · rintro ⟨lm, ⟨hm, hc⟩, rfl⟩
    exact ⟨lm, hm, rfl, hc⟩
  · rintro ⟨lm, hm, rfl, hc⟩
    exact ⟨lm, ⟨hm, hc⟩, rfl⟩

/-- Each claimed module is one that the environment loaded: the facts carry that their modules are
those of its header. -/
theorem claimed_loaded (f : Regula.Load.Facts) {m : Name} (h : m ∈ f.claimed) :
    m ∈ f.env.header.moduleNames.toList := by
  obtain ⟨lm, hm, rfl, -⟩ := (mem_claimed_iff f m).mp h
  rw [← f.names]
  exact List.mem_map_of_mem (Array.mem_toList_iff.mpr hm)

/-- The places of the modules decide what is claimed: the modules whose `.olean` lies below the root
package's library directory. -/
theorem mem_claimed_place (f : Regula.Load.Facts) (m : Name) :
    m ∈ f.claimed ↔
      ∃ lm ∈ f.modules, lm.name = m ∧ Regula.Load.below f.rootDir lm.olean = true := by
  rw [mem_claimed_iff]
  refine exists_congr fun lm => and_congr_right fun hm => and_congr_right fun _ => ?_
  have hp := f.placed lm hm
  rw [hp]
  rfl

/-- The places of the modules decide `EnvToolchain`: the constants whose module's `.olean` lies
below the toolchain's library directory. -/
theorem toolchain_place (f : Regula.Load.Facts) (n : Name) :
    EnvToolchain f n ↔
      ∃ (idx : Lean.ModuleIdx) (lm : Regula.Load.LoadedModule),
        f.env.getModuleIdxFor? n = some idx ∧ f.modules[idx.toNat]? = some lm ∧
          Regula.Load.below f.toolchainDir lm.olean = true := by
  have hflag : ∀ lm ∈ f.modules,
      lm.inToolchain = Regula.Load.below f.toolchainDir lm.olean := by
    intro lm hm
    have hp := f.placed lm hm
    rw [hp]
    rfl
  simp only [EnvToolchain, Regula.Load.Facts.info?, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨lm, ⟨idx, hi, hm⟩, ht⟩
    exact ⟨idx, lm, hi, hm, hflag lm (mem_modules_of_getElem hm) ▸ ht⟩
  · rintro ⟨idx, lm, hi, hm, ht⟩
    exact ⟨lm, ⟨idx, hi, hm⟩, (hflag lm (mem_modules_of_getElem hm)).symm ▸ ht⟩

/-! ## The safety of a constant -/

/-- Lean sets at most one of its two flags on a constant. -/
theorem not_unsafe_of_partial (info : ConstantInfo) (h : info.isPartial = true) :
    info.isUnsafe = false := by
  cases info with
  | defnInfo v =>
    simp only [ConstantInfo.isPartial, ConstantInfo.isUnsafe] at h ⊢
    revert h
    cases v.safety <;> decide
  | _ => simp [ConstantInfo.isPartial] at h

/-- `safetyOf` is `.partial` exactly of a partial constant, which is then not unsafe. -/
theorem safetyOf_partial (info : ConstantInfo) :
    Regula.Load.safetyOf info = .partial ↔ info.isPartial = true ∧ info.isUnsafe = false := by
  simp only [Regula.Load.safetyOf]
  cases info.isUnsafe <;> cases info.isPartial <;> simp

/-- `safetyOf` is `.safe` exactly of a constant with neither flag. -/
theorem safetyOf_safe (info : ConstantInfo) :
    Regula.Load.safetyOf info = .safe ↔ info.isUnsafe = false ∧ info.isPartial = false := by
  simp only [Regula.Load.safetyOf]
  cases info.isUnsafe <;> cases info.isPartial <;> simp

/-! ## What the input holds -/

/-- What the loader gives, in the terms of the environment. No name repeats and the closed form
holds by the type of `i`. -/
structure Loaded (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile)
    (i : Regula.Closed.Input) : Prop where
  /-- The profile is the one that the shell read. -/
  profile : i.profile = p
  /-- The claimed modules are those of the facts. -/
  modules : i.modules = f.claimed
  /-- Each module of a default target is claimed. -/
  roots : ∀ r ∈ roots, r ∈ f.claimed
  /-- Each constant of the input is a constant of the environment, with the fields it gives. -/
  sound : ∀ d ∈ i.decls, ∃ info m, f.env.constants.map₁[d.name]? = some info ∧
    f.info? d.name = some m ∧ d = f.declIn d.name m info (f.stated.getD d.name [])
  /-- Each constant of the environment is in the input. -/
  whole : ∀ n info, f.env.constants.map₁[n]? = some info →
    ∃ m, f.info? n = some m ∧ f.declIn n m info (f.stated.getD n []) ∈ i.decls

/-- What `Facts.decl` gives: the constant with its module. -/
theorem decl_ok {n : Name} {info : ConstantInfo} {s : List ConstantInfo} {d : Regula.Closed.Decl}
    (h : f.decl n info s = .ok d) : ∃ m, f.info? n = some m ∧ d = f.declIn n m info s := by
  simp only [Regula.Load.Facts.decl] at h
  split at h
  · rename_i m hm
    simp only [Except.ok.injEq] at h
    exact ⟨m, hm, h.symm⟩
  · cases h

/-- What `Facts.shown` decides. -/
theorem shown_true {x : Name × Name × ConstantInfo} (h : f.shown x = true) :
    ∃ k m, f.env.constants.map₁[x.2.1]? = some k ∧
      Regula.Load.readOf k = Regula.Load.readOf x.2.2 ∧ f.info? x.2.1 = some m ∧
      m.claimed = true := by
  simp only [Regula.Load.Facts.shown] at h
  split at h
  · rename_i k m h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨k, m, h1, h.1, h2, h.2⟩
  · cases h
  · cases h

/-- What `Facts.unread?` decides. -/
theorem unread_none {x : Name × Name × ConstantInfo} (h : f.unread? i = none)
    (hx : x ∈ f.claimedConstants) :
    f.shown x = true ∨ Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true := by
  by_cases hs : f.shown x = true
  · exact .inl hs
  refine .inr ?_
  have hmem : x ∈ f.claimedConstants.filter (!f.shown ·) := by simp [hx, hs]
  simp only [Regula.Load.Facts.unread?] at h
  cases hu : f.claimedConstants.filter (!f.shown ·) with
  | nil =>
    rw [hu] at hmem
    cases hmem
  | cons a l =>
    rw [hu] at h hmem
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
    simpa using h x hmem

/-- What the parts of the loader that give an input establish: `Loaded` of what the admission gave. -/
theorem loaded_of_parts {decls : List Regula.Closed.Decl} {i' : Regula.Closed.Input}
    (hfind : roots.find? (fun x => !f.claimed.contains x) = none)
    (hm : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (f.stated.getD x.1 [])) = .ok decls)
    {unique : (decls.map (·.name)).Nodup}
    (hadmit : ({ profile := p, modules := f.claimed, decls, unique } : Regula.Closed.Draft).admit = .ok i') :
    Loaded f roots p i' := by
  have hd := admit_toDraft hadmit
  obtain ⟨h1, h2, -⟩ := Regula.Load.mapM_ok
    (fun x : Name × ConstantInfo => f.decl x.1 x.2 (f.stated.getD x.1 []))
    (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ hm
  have hdecls : i'.decls = decls := by rw [hd]
  have hp : i'.profile = p := by rw [hd]
  have hmods : i'.modules = f.claimed := by rw [hd]
  refine ⟨hp, hmods, ?_, ?_, ?_⟩
  · intro r hr
    have := List.find?_eq_none.mp hfind r hr
    simpa using this
  · intro d hd'
    rw [hdecls] at hd'
    obtain ⟨⟨n, info⟩, hx, hok⟩ := h1 d hd'
    obtain ⟨m, hmod, hdv⟩ := decl_ok hok
    have hname : d.name = n := f.decl_name hok
    have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx
    subst hname
    exact ⟨info, m, hget, hmod, hdv⟩
  · intro n info hn
    obtain ⟨d, hd', hok⟩ := h2 (n, info) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hn)
    obtain ⟨m, hmod, hdv⟩ := decl_ok hok
    refine ⟨m, hmod, ?_⟩
    rw [hdecls]
    exact hdv ▸ hd'

/-- The function that fills the input gives what `Loaded` states. -/
theorem input_loaded (h : f.input roots p = .ok i) : Loaded f roots p i := by
  simp only [Regula.Load.Facts.input] at h
  split at h
  · cases h
  rename_i hfind
  split at h
  · cases h
  rename_i decls hm
  split at h
  · cases h
  rename_i i' hadmit
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  exact loaded_of_parts hfind hm hadmit

/-- Each constant of a claimed module's `.olean` is shown to the rules, or is what they admit. -/
theorem input_kept (h : f.input roots p = .ok i) {x : Name × Name × ConstantInfo}
    (hx : x ∈ f.claimedConstants) :
    f.shown x = true ∨ Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true := by
  simp only [Regula.Load.Facts.input] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hkeeps
  simp only [Except.ok.injEq] at h
  subst h
  exact unread_none hkeeps hx

/-! ## From the input's statements to the environment's -/

/-- The claimed modules of the specification's input are those of the facts. -/
theorem claimed_iff (hl : Loaded f roots p i) (m : Name) :
    (toSpec i).ClaimedModule m ↔ m ∈ f.claimed := by
  simp [Input.ClaimedModule, toSpec, toSpecDraft, hl.modules]

/-- A constant of the specification's input is a constant of the environment. -/
theorem of_mem {x : Decl} (hl : Loaded f roots p i) (hx : x ∈ (toSpec i).decls) :
    ∃ info m, f.env.constants.map₁[x.name]? = some info ∧ f.info? x.name = some m ∧
      x = decl (f.declIn x.name m info (f.stated.getD x.name [])) := by
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  obtain ⟨info, m, hn, hm, hv⟩ := hl.sound d hd
  exact ⟨info, m, hn, hm, congrArg decl hv⟩

/-- A constant of the environment is a constant of the specification's input. -/
theorem to_mem (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) {m : Regula.Load.LoadedModule}
    (hm : f.info? n = some m) :
    decl (f.declIn n m info (f.stated.getD n [])) ∈ (toSpec i).decls := by
  obtain ⟨m', hm', hmem⟩ := hl.whole n info hn
  rw [hm] at hm'
  cases hm'
  exact mem_decls.mpr ⟨_, hmem, rfl⟩

/-- A constant of the environment has a module. -/
theorem module_of (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) : ∃ m, f.info? n = some m := by
  obtain ⟨m, hm, -⟩ := hl.whole n info hn
  exact ⟨m, hm⟩

/-- `moduleOf?` is the name of what `info?` gives. -/
theorem moduleOf?_eq_some {n m : Name} :
    f.moduleOf? n = some m ↔ ∃ lm, f.info? n = some lm ∧ lm.name = m := by
  simp [Regula.Load.Facts.moduleOf?, Option.map_eq_some_iff]

/-- A name resolves in the specification's input exactly when the environment holds it. -/
theorem resolves_env (hl : Loaded f roots p i) (u : Name) :
    (toSpec i).Resolves u ↔ ∃ info, f.env.constants.map₁[u]? = some info := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨info, -, hn, -, -⟩ := of_mem hl hx
    exact ⟨info, hn⟩
  · rintro ⟨info, hn⟩
    obtain ⟨m, hm⟩ := module_of hl hn
    exact ⟨_, to_mem hl hn hm, rfl⟩

/-- The walk of the input is the walk of the environment. -/
theorem reaches_env (hl : Loaded f roots p i) (c e : Name) :
    (toSpec i).Reaches c e ↔ EnvReaches f c e := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step x hx hc hu _ ih =>
      subst hc
      obtain ⟨info, _, hn, -, hv⟩ := of_mem hl hx
      rw [hv] at hu
      exact .step ⟨info, hn, (mem_usesIn info _ _).mp hu⟩ ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step hm _ ih =>
      obtain ⟨info, hn, hu⟩ := hm
      obtain ⟨m, hmod⟩ := module_of hl hn
      exact .step _ (to_mem hl hn hmod) rfl ((mem_usesIn info _ _).mpr hu) ih

/-- The kind that `kindOf` gives is `axiom` exactly of an axiom. -/
theorem kindOf_axiom (k : ConstantInfo) : Regula.Load.kindOf k = .axiom ↔ AxiomInfo k := by
  cases k <;> simp [Regula.Load.kindOf, AxiomInfo]

/-- `kindIn` gives `axiom` exactly when the kept constant or a constant of the list is an axiom. -/
theorem kindIn_axiom (k : ConstantInfo) (s : List ConstantInfo) :
    Regula.Load.kindIn k s = .axiom ↔ AxiomInfo k ∨ ∃ v ∈ s, AxiomInfo v := by
  simp only [Regula.Load.kindIn]
  split
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    simpa using .inr hs
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    simp [kindOf_axiom, hs]

/-- The kind of the input's constant is `axiom` exactly when `kindIn` says so. -/
theorem kind_axiom {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .axiom ↔ AxiomInfo info ∨ ∃ v ∈ s, AxiomInfo v := by
  rw [← kindIn_axiom]
  simp only [decl, Regula.Load.Facts.declIn]
  cases Regula.Load.kindIn info s <;> simp [constKind]

/-- The kind of the input's constant is `definition` exactly of a definition of whose name no module
states an axiom. -/
theorem kind_definition {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .definition ↔
      (∃ v, info = .defnInfo v) ∧ ∀ w ∈ s, ¬ AxiomInfo w := by
  have hconst : (decl (f.declIn n m info s)).kind = .definition ↔
      Regula.Load.kindIn info s = .definition := by
    simp only [decl, Regula.Load.Facts.declIn]
    cases Regula.Load.kindIn info s <;> simp [constKind]
  rw [hconst]
  simp only [Regula.Load.kindIn]
  split
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    obtain ⟨w, hw, hax⟩ := hs
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun _ hall => hall w hw hax
  · rename_i hs
    have hall : ∀ w ∈ s, ¬ AxiomInfo w := by
      simpa only [List.any_eq_true, beq_iff_eq, kindOf_axiom, not_exists, not_and] using hs
    constructor
    · intro hk
      refine ⟨?_, hall⟩
      cases info <;> simp [Regula.Load.kindOf] at hk ⊢
    · rintro ⟨⟨v, rfl⟩, -⟩
      rfl

/-- Whether the input states an axiom of a held name is `EnvAxiom`. -/
theorem kind_envAxiom {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) :
    (decl (f.declIn n m info (f.stated.getD n []))).kind = .axiom ↔ EnvAxiom f n := by
  rw [kind_axiom]
  constructor
  · exact fun h => ⟨info, hn, h⟩
  · rintro ⟨k, hk, h⟩
    rw [hn] at hk
    cases hk
    exact h

/-- Whether a name names an axiom of the specification's input is `EnvAxiom`. -/
theorem isAxiom_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).IsAxiom a ↔ EnvAxiom f a := by
  constructor
  · rintro ⟨x, hx, rfl, hk⟩
    obtain ⟨info, _, hn, -, hv⟩ := of_mem hl hx
    rw [hv] at hk
    exact (kind_envAxiom hn).mp hk
  · intro h
    obtain ⟨info, hn, -⟩ := id h
    obtain ⟨m, hm⟩ := module_of hl hn
    exact ⟨_, to_mem hl hn hm, rfl, (kind_envAxiom hn).mpr h⟩

/-- What `Input.Known` states of the environment. -/
theorem known_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).Known a ↔ a ∈ logicalAxioms ∧ (∃ info, f.env.constants.map₁[a]? = some info) ∧
      EnvToolchain f a := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨x, hx, rfl, ht⟩
    obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx
    rw [hv] at ht
    exact ⟨⟨info, hn⟩, m, hm, ht⟩
  · rintro ⟨⟨info, hn⟩, m, hm, ht⟩
    exact ⟨_, to_mem hl hn hm, rfl, ht⟩

/-- What a profile admits of a constant of the environment. -/
theorem admits_env (hl : Loaded f roots p i) {a : Name} {info : ConstantInfo}
    (ha : f.env.constants.map₁[a]? = some info) :
    (toSpec i).Admits (toSpec i).profile a ↔ EnvAdmits f p a := by
  have hp : (toSpec i).profile = profile p := by simp [toSpec, toSpecDraft, hl.profile]
  have hlog : a ∈ logicalAxioms ↔ a = ``propext ∨ a = ``Quot.sound ∨ a = ``Classical.choice := by
    simp [logicalAxioms]
  have hheld : ∃ info, f.env.constants.map₁[a]? = some info := ⟨info, ha⟩
  rw [hp]
  cases p with
  | kernelOnly => simp [Input.Admits, profile, EnvAdmits]
  | choiceFree =>
    simp only [Input.Admits, profile, EnvAdmits, known_env hl, hlog]
    constructor
    · rintro ⟨⟨-, -, ht⟩, hs⟩
      exact ⟨hs, ht⟩
    · rintro ⟨hs, ht⟩
      refine ⟨⟨?_, hheld, ht⟩, hs⟩
      rcases hs with h | h
      · exact .inl h
      · exact .inr (.inl h)
  | standardLogical =>
    simp only [Input.Admits, profile, EnvAdmits, known_env hl, hlog]
    constructor
    · rintro ⟨hs, -, ht⟩
      exact ⟨hs, ht⟩
    · rintro ⟨hs, ht⟩
      exact ⟨hs, hheld, ht⟩

/-- The safety of the input's constant is `partial` exactly of a partial constant that is not
unsafe. -/
theorem safety_partial {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).safety = .partial ↔
      info.isPartial = true ∧ info.isUnsafe = false := by
  rw [← safetyOf_partial]
  simp only [decl, Regula.Load.Facts.declIn]
  cases Regula.Load.safetyOf info <;> simp [safety]

/-- The safety of the input's constant is `safe` exactly of a constant with neither flag. -/
theorem safety_safe {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).safety = .safe ↔
      info.isUnsafe = false ∧ info.isPartial = false := by
  rw [← safetyOf_safe]
  simp only [decl, Regula.Load.Facts.declIn]
  cases Regula.Load.safetyOf info <;> simp [safety]

/-- The form of a recursion helper in the input is its form in the environment. -/
theorem helper_env (hl : Loaded f roots p i) (n : Name) (m : Regula.Load.LoadedModule)
    (info : ConstantInfo) :
    (toSpec i).RecursionHelper (decl (f.declIn n m info (f.stated.getD n []))) ↔
      EnvHelper f n info m.name := by
  constructor
  · rintro ⟨h1, h2, h3, base, hb, hname, hk, hm, hu, hi', he⟩
    obtain ⟨hp, hs⟩ := safety_partial.mp h1
    obtain ⟨info', lm, hn', hm', hv⟩ := of_mem hl hb
    rw [hv] at hk hu hi' he
    obtain ⟨⟨v, rfl⟩, hst⟩ := kind_definition.mp hk
    obtain ⟨hu1, hu2⟩ := safety_safe.mp hu
    have hmod : f.moduleOf? base.name = some m.name :=
      moduleOf?_eq_some.mpr ⟨lm, hm', (congrArg Decl.module hv).symm.trans hm⟩
    exact ⟨hp, hs, h2, h3, base.name, v, hname, hn', hst, hmod, hu1, hu2, hi', he⟩
  · rintro ⟨hp, hs, h2, h3, b, v, hname, hn', hst, hmod, hu1, hu2, hi', he⟩
    obtain ⟨lm, hm', hlm⟩ := moduleOf?_eq_some.mp hmod
    exact ⟨safety_partial.mpr ⟨hp, hs⟩, h2, h3, _, to_mem hl hn' hm', hname,
      kind_definition.mpr ⟨⟨v, rfl⟩, hst⟩, hlm, safety_safe.mpr ⟨hu1, hu2⟩, hi', he⟩

/-- The closed form of the input is `EnvForm` of the environment. -/
theorem wf_env (hl : Loaded f roots p i) : (toSpec i).WellFormed ↔ EnvForm f := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro n u ⟨info, hn, hm⟩
      obtain ⟨m, hmod⟩ := module_of hl hn
      exact (resolves_env hl u).mp (h.closed _ (to_mem hl hn hmod) u ((mem_usesIn info _ u).mpr hm))
    · simpa [toSpec, toSpecDraft, hl.modules] using h.claims
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx u hu
      obtain ⟨info, _, hn, -, hv⟩ := of_mem hl hx
      rw [hv] at hu
      exact (resolves_env hl u).mpr (h.closed _ u ⟨info, hn, (mem_usesIn info _ u).mp hu⟩)
    · simpa [toSpec, toSpecDraft, hl.modules] using h.claims

/-- A constant flagged in the input is one flagged in the environment. -/
theorem flagged_iff {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    ((decl (f.declIn n m info s)).safety ≠ .safe ∨ HelperNamed (decl (f.declIn n m info s))) ↔
      (info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") := by
  have hs : (decl (f.declIn n m info s)).safety ≠ .safe ↔
      info.isUnsafe = true ∨ info.isPartial = true := by
    rw [ne_eq, safety_safe]
    cases info.isUnsafe <;> cases info.isPartial <;> simp
  rw [hs, or_assoc]
  rfl

/-- Every rule holding of the input is `EnvFloor` of the environment. -/
theorem allHold_env (hl : Loaded f roots p i) : AllHold (toSpec i) ↔ EnvFloor f p := by
  constructor
  · rintro ⟨h1, -, -, -, h5, h6⟩ n info m hn hm hc
    obtain ⟨lm, hlm, rfl⟩ := moduleOf?_eq_some.mp hm
    have hx := to_mem hl hn hlm
    have hcm := (claimed_iff hl _).mpr hc
    refine ⟨fun hax => ?_, fun hflag => ?_, fun l hl' hv => ?_, fun a hr hax => ?_⟩
    · exact h1 n ⟨_, hx, rfl, hcm, (kind_envAxiom hn).mpr hax⟩
    · refine Classical.byContradiction fun hno =>
        h6 n ⟨_, hx, rfl, hcm, .inl ⟨flagged_iff.mpr hflag, fun hh => ?_⟩⟩
      exact hno ((helper_env hl n lm info).mp hh)
    · exact h6 n ⟨_, hx, rfl, hcm, .inr ⟨l, hl', (mem_valueUsesOf info l).mpr hv⟩⟩
    · obtain ⟨k, ha, -⟩ := id hax
      refine Classical.byContradiction fun hno => h5 n ⟨⟨_, hx, rfl, hcm⟩, a,
        ⟨(reaches_env hl n a).mpr hr, (isAxiom_env hl a).mpr hax⟩, fun hadm => ?_⟩
      exact hno ((admits_env hl ha).mp hadm)
  · intro hf
    have hmod : ∀ {x : Decl} {info m}, f.info? x.name = some m → x = decl
        (f.declIn x.name m info (f.stated.getD x.name [])) → f.moduleOf? x.name = some x.module :=
      fun {x info m} hm hv => moduleOf?_eq_some.mpr ⟨m, hm, by rw [hv]; rfl⟩
    have no5 : ∀ c, ¬ Violates1005 (toSpec i) c := by
      rintro c ⟨⟨x, hx, rfl, hcm⟩, a, ⟨hr, hax⟩, hna⟩
      obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx
      have hax' := (isAxiom_env hl a).mp hax
      obtain ⟨k, ha, -⟩ := id hax'
      exact hna ((admits_env hl ha).mpr
        ((hf _ _ _ hn (hmod hm hv) ((claimed_iff hl _).mp hcm)).2.2.2 a
          ((reaches_env hl _ a).mp hr) hax'))
    refine ⟨?_, fun c h => no5 c (rg1005_of_hole h), fun c h => no5 c (rg1005_of_unknown h),
      fun c h => no5 c (rg1005_of_compiler h), no5, ?_⟩
    · rintro c ⟨x, hx, rfl, hcm, hk⟩
      obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx
      have hmd := hmod hm hv
      rw [hv] at hk
      exact (hf _ _ _ hn hmd ((claimed_iff hl _).mp hcm)).1 ((kind_envAxiom hn).mp hk)
    · rintro c ⟨x, hx, rfl, hcm, hv⟩
      obtain ⟨info, m, hn, hm, hd⟩ := of_mem hl hx
      have hmd := hmod hm hd
      obtain ⟨-, h6, h7, -⟩ := hf _ _ _ hn hmd ((claimed_iff hl _).mp hcm)
      have hmn : m.name = x.module := by rw [hd]; rfl
      rw [hd] at hv
      rcases hv with ⟨hflag, hno⟩ | ⟨l, hl', hu⟩
      · exact hno ((helper_env hl _ m info).mpr (hmn ▸ h6 (flagged_iff.mp hflag)))
      · exact h7 l hl' ((mem_valueUsesOf info l).mp hu)

/-! ## The theorems -/

/-- The closed form holds of each environment that the loader gives an input for: it refuses each
other one. -/
theorem input_form (h : f.input roots p = .ok i) : EnvForm f :=
  (wf_env (input_loaded h)).mp (wf_toSpec i)

/-- For every environment, every set of facts about it and every profile: when the loader gives an
input, the checker passes on it exactly when the environment has `EnvForm` and `EnvFloor`. Neither
names the input, and no hypothesis says anything of the loader. -/
theorem pass_iff (h : f.input roots p = .ok i) :
    i.report.verdict = .pass ↔ EnvForm f ∧ EnvFloor f p := by
  have hl := input_loaded h
  rw [(report_complete i).2, allHold_env hl]
  exact ⟨fun hf => ⟨input_form h, hf⟩, (·.2)⟩

/-- A load that fails is never a pass. -/
theorem decision_failed (why : String) :
    (Regula.Closed.decision (.error why)).verdict = .incomplete := rfl

/-- The verdict that the shell reports is a pass only on an input that the load gave. -/
theorem decision_pass {r : Except String Regula.Closed.Input}
    (h : (Regula.Closed.decision r).verdict = .pass) :
    ∃ i, r = .ok i ∧ i.report.verdict = .pass := by
  cases r with
  | error why => cases h
  | ok i => exact ⟨i, rfl, h⟩

/-- The floor, on the path that the shell runs: when the verdict of the loader's result is a pass,
each module of a default target is claimed, each claimed module is loaded, each constant of the
environment has a module, and the environment has `EnvForm` and `EnvFloor`. -/
theorem pass_floor (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) :
    (∀ r ∈ roots, r ∈ f.claimed) ∧ (∀ m ∈ f.claimed, m ∈ f.env.header.moduleNames.toList) ∧
      (∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.moduleOf? n = some m) ∧
      EnvForm f ∧ EnvFloor f p := by
  obtain ⟨i, hi, hp⟩ := decision_pass h
  have hl := input_loaded hi
  refine ⟨hl.roots, fun _ hm => claimed_loaded f hm, fun _ _ hn => ?_, (pass_iff hi).mp hp⟩
  obtain ⟨m, hm⟩ := module_of hl hn
  exact ⟨m.name, moduleOf?_eq_some.mpr ⟨m, hm, rfl⟩⟩

/-- What the claimed modules' own `.olean` files hold: `Facts.claimedConstants` lists each constant
of each claimed module, as the header of the environment gives that module's data at its index. -/
theorem mem_claimedConstants {m n : Name} {info : ConstantInfo} :
    (m, n, info) ∈ f.claimedConstants ↔ ∃ (k : Nat) (lm : Regula.Load.LoadedModule) (data :
        Lean.ModuleData), f.modules[k]? = some lm ∧ lm.claimed = true ∧ lm.name = m ∧
      f.env.header.moduleData[k]? = some data ∧ (n, info) ∈ data.constNames.zip data.constants := by
  simp only [Regula.Load.Facts.claimedConstants, List.mem_flatMap, List.mem_filter,
    Array.mem_toList_iff, List.mem_map, Prod.mk.injEq, Array.mem_iff_getElem?,
    Array.getElem?_zip_eq_some]
  constructor
  · rintro ⟨⟨lm, data⟩, ⟨⟨k, h1, h2⟩, hc⟩, ⟨n', info'⟩, hx, rfl, rfl, rfl⟩
    exact ⟨k, lm, data, h1, hc, rfl, h2, hx⟩
  · rintro ⟨k, lm, data, h1, hc, rfl, h2, hx⟩
    exact ⟨(lm, data), ⟨⟨k, h1, h2⟩, hc⟩, (n, info), hx, rfl, rfl, rfl⟩

/-- A pass holds of each constant of a claimed module as that module's own `.olean` states it, not
only of the constant that Lean's import keeps under its name (`Facts.shown`, `Facts.unread?`): it is
no axiom, it is a partial, safe-flagged constant when it has either flag or a recursion helper's
name, its value mentions no loop construct, and each axiom that it reaches, through what any loaded
module's own data states, is one that the profile admits. -/
theorem pass_held (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) {m n : Name}
    {info : ConstantInfo} (hx : (m, n, info) ∈ f.claimedConstants) :
    (∀ v, info ≠ .axiomInfo v) ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      info.isPartial = true ∧ info.isUnsafe = false) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ u, Mentions info u → ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨i, hi, hp⟩ := decision_pass h
  have hl := input_loaded hi
  rcases (input_kept hi hx).symm with hfits | hshown
  · simp only [Regula.Load.fitsUnshown, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      List.all_eq_true, Array.all_eq_true_iff_forall_mem] at hfits
    obtain ⟨⟨⟨⟨hkind, hsafety⟩, hname⟩, hloop⟩, huses⟩ := hfits
    obtain ⟨hunsafe, hpartial⟩ := (safetyOf_safe info).mp hsafety
    refine ⟨?_, fun hflag => ?_, ?_, ?_⟩
    · rintro v rfl
      simp [Regula.Load.kindOf] at hkind
    · rcases hflag with hf | hf | ⟨b, hb⟩
      · rw [hunsafe] at hf
        cases hf
      · rw [hpartial] at hf
        cases hf
      · simp [(isUnsafeRecName_eq n b).mpr hb] at hname
    · intro l hl' hv
      have hc := hloop l (by simpa [Regula.Closed.loopConstructs, loopConstructs] using hl')
      have hc' : l ∉ Regula.Load.valueUsesOf info := by simpa using hc
      exact hc' (by simpa using (mem_valueUsesOf info l).mpr hv)
    · intro u hu a hr hea
      have hall := (huses u (by simpa using (mem_usesOf info u).mpr hu)).2
      have hax : a ∈ i.tables.axiomSet u :=
        (axiomSet_iff _ u a).mpr ⟨(reaches_env hl u a).mpr hr, (isAxiom_env hl a).mpr hea⟩
      obtain ⟨k, ha, -⟩ := id hea
      exact (admits_env hl ha).mp ((admits_iff _ i.profile a).mp (hall a hax))
  obtain ⟨k, lm, hk, hread, hinfo, hclaimed⟩ := shown_true hshown
  have hmod : f.moduleOf? n = some lm.name := moduleOf?_eq_some.mpr ⟨lm, hinfo, rfl⟩
  have hcl : lm.name ∈ f.claimed :=
    (mem_claimed_iff f _).mpr ⟨lm, mem_modules_of_info hinfo, rfl, hclaimed⟩
  obtain ⟨h1, h2, h3, h4⟩ := ((pass_iff hi).mp hp).2 n k lm.name hk hmod hcl
  simp only [Regula.Load.readOf, Prod.mk.injEq] at hread
  obtain ⟨hkind, hsafety, huses, hvalue⟩ := hread
  have hsafe : k.isUnsafe = info.isUnsafe ∧ k.isPartial = info.isPartial := by
    have hb : ∀ c : ConstantInfo, c.isUnsafe = (Regula.Load.safetyOf c == .unsafe) ∧
        c.isPartial = (Regula.Load.safetyOf c == .partial) := by
      intro c
      simp only [Regula.Load.safetyOf]
      cases hu : c.isUnsafe <;> cases hq : c.isPartial <;> simp
      exact absurd (not_unsafe_of_partial c hq) (by simp [hu])
    rw [(hb k).1, (hb k).2, (hb info).1, (hb info).2, hsafety]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro v rfl
    have hax : AxiomInfo k := (kindOf_axiom k).mp (by simpa [Regula.Load.kindOf] using hkind)
    exact h1 ⟨k, hk, .inl hax⟩
  · intro hflag
    have hflag' : k.isUnsafe = true ∨ k.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec" := by
      rwa [hsafe.1, hsafe.2]
    obtain ⟨hpart, hsf, -⟩ := h2 hflag'
    exact ⟨hsafe.2 ▸ hpart, hsafe.1 ▸ hsf⟩
  · intro l hl' hv
    exact h3 l hl' ((mem_valueUsesOf k l).mp (hvalue ▸ (mem_valueUsesOf info l).mpr hv))
  · intro u hu a hr hax
    have hm : Mentions k u := (mem_usesOf k u).mp (huses ▸ (mem_usesOf info u).mpr hu)
    exact h4 a (.step ⟨k, hk, .inl hm⟩ hr) hax

/-- A run has a profile only on the release that this revision reads, with exactly one argument, and
that argument names the profile. -/
theorem profileOfRun_ok {version commit : String} {args : List String}
    {q : Regula.Closed.Profile} (h : Regula.Shell.profileOfRun version commit args = .ok q) :
    version = "4.35.0" ∧ commit = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" ∧
      ∃ text, args = [text] ∧ Regula.Closed.Profile.ofSpelling? text = some q := by
  simp only [Regula.Shell.profileOfRun] at h
  split at h
  · cases h
  · rename_i hs
    have hs' : Regula.Shell.supportsLean version commit = true := by simpa using hs
    simp only [Regula.Shell.supportsLean, Regula.Closed.pinnedLean, beq_iff_eq, Prod.mk.injEq] at hs'
    refine ⟨hs'.1, hs'.2, ?_⟩
    split at h
    · rename_i text
      split at h
      · rename_i q' hq
        simp only [Except.ok.injEq] at h
        exact ⟨text, rfl, h ▸ hq⟩
      · cases h
    · cases h

/-- The text of a profile names it: the three spellings and no other. -/
theorem profileOf_eq_some {text : String} {q : Regula.Closed.Profile}
    (h : Regula.Closed.Profile.ofSpelling? text = some q) :
    (text = "kernel-only" ∧ q = .kernelOnly) ∨ (text = "choice-free" ∧ q = .choiceFree) ∨
      (text = "standard-logical" ∧ q = .standardLogical) := by
  have hs := Regula.Closed.Profile.ofSpelling?_eq_some.mp h
  subst hs
  cases q <;> simp [Regula.Closed.Profile.spelling]

/-- `below` states what its name says, by the components of the two paths: the directory's are a
proper prefix of the path's. -/
theorem below_iff (dir path : System.FilePath) :
    Regula.Load.below dir path = true ↔
      Regula.Load.parts dir <+: Regula.Load.parts path ∧
        Regula.Load.parts dir ≠ Regula.Load.parts path := by
  simp [Regula.Load.below, List.isPrefixOf_iff_prefix]

/-- `exactBelow` states what its name says, by the components of the three paths, each with `.` removed:
the real path's are the path's, and the directory's are a prefix of them. -/
theorem exactBelow_iff (dir path real : System.FilePath) :
    Regula.Load.exactBelow dir path real = true ↔
      Regula.Load.exactParts real = Regula.Load.exactParts path ∧
        Regula.Load.exactParts dir <+: Regula.Load.exactParts path := by
  simp [Regula.Load.exactBelow, List.isPrefixOf_iff_prefix]

/-- A path with a `..` passes `exactBelow` against no real path that has none, so a `..` needs no test of
its own. That `IO.FS.realPath` gives a path with no `..` is the operating system's. -/
theorem exactBelow_no_parent (dir path real : System.FilePath)
    (h : Regula.Load.exactBelow dir path real = true) (hr : ".." ∉ Regula.Load.parts real) :
    ".." ∉ Regula.Load.parts path := by
  intro hp
  have he := ((exactBelow_iff dir path real).mp h).1
  have hm : ".." ∈ Regula.Load.exactParts path := by simp [Regula.Load.exactParts, hp]
  rw [← he] at hm
  exact hr (List.mem_filter.mp hm).1

/-! ## A pass is owed -/

/-- What the loader asks of each constant of a claimed module's own `.olean` that the environment does not show to the rules
(`Facts.shown`), in the terms of the environment: a safe theorem with no recursion helper's name, whose value mentions no
loop construct, and each constant it mentions is held and reaches only axioms that the profile admits. Lean's import
replaces such a constant (`Facts.stated`), so no rule reads it as a subject. -/
def EnvUnshown (f : Regula.Load.Facts) (p : Regula.Closed.Profile) : Prop :=
  ∀ x ∈ f.claimedConstants, f.shown x = false →
    Regula.Load.kindOf x.2.2 = .theorem ∧ Regula.Load.safetyOf x.2.2 = .safe ∧
    (∀ b, x.2.1 ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions x.2.2 l) ∧
    ∀ u, Mentions x.2.2 u → (∃ k, f.env.constants.map₁[u]? = some k) ∧
      ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a

/-- What a build must be for the loader and the rules to pass it, in the terms of the environment and the roots alone:
each module of a default target is claimed, each constant has a module, and the environment has `EnvForm`, `EnvFloor` and
`EnvUnshown`. -/
structure LoadFloor (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile) : Prop where
  /-- Each module of a default target is claimed. -/
  roots : ∀ r ∈ roots, r ∈ f.claimed
  /-- Each constant has a module. -/
  placed : ∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.info? n = some m
  /-- The closed form. -/
  form : EnvForm f
  /-- The floor of the rules. -/
  floor : EnvFloor f p
  /-- What the environment does not show. -/
  unshown : EnvUnshown f p

/-- `fitsUnshown` is what `EnvUnshown` states of one constant. -/
theorem fitsUnshown_iff (hl : Loaded f roots p i) (x : Name × Name × ConstantInfo) :
    Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true ↔
      Regula.Load.kindOf x.2.2 = .theorem ∧ Regula.Load.safetyOf x.2.2 = .safe ∧
      (∀ b, x.2.1 ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions x.2.2 l) ∧
      ∀ u, Mentions x.2.2 u → (∃ k, f.env.constants.map₁[u]? = some k) ∧
        ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨m, n, info⟩ := x
  have hheld : ∀ u, i.tables.index.contains u = true ↔ ∃ k, f.env.constants.map₁[u]? = some k := by
    intro u
    rw [← resolves_env hl u]
    constructor
    · intro hc
      obtain ⟨d, hd⟩ : ∃ d, i.tables.index[u]? = some d := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        exact Option.isSome_iff_exists.mp hc
      obtain ⟨hmem, rfl⟩ := (i.tables.mem_index _ _).mp hd
      exact ⟨_, mem_decls.mpr ⟨d, hmem, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      change i.tables.index[d.name]?.isSome = true
      rw [(i.tables.mem_index _ _).mpr ⟨hd, rfl⟩]
      rfl
  simp only [Regula.Load.fitsUnshown, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true, Array.all_eq_true_iff_forall_mem, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro hname b hb
      simp [(isUnsafeRecName_eq n b).mpr hb] at hname
    · intro hname
      cases hu : Lean.Compiler.isUnsafeRecName? n with
      | none => rfl
      | some b => exact absurd ((isUnsafeRecName_eq n b).mp hu) (hname b)
  · constructor
    · intro hloop l hl' hv
      have hc := hloop l (by simpa [Regula.Closed.loopConstructs, loopConstructs] using hl')
      have hc' : l ∉ Regula.Load.valueUsesOf info := by simpa using hc
      exact hc' (by simpa using (mem_valueUsesOf info l).mpr hv)
    · intro hloop l hl'
      have hn : l ∉ Regula.Load.valueUsesOf info := fun hin =>
        hloop l (by simpa [Regula.Closed.loopConstructs, loopConstructs] using hl')
          ((mem_valueUsesOf info l).mp (by simpa using hin))
      simpa using hn
  · have hadm : ∀ u, (∀ a ∈ i.tables.axiomSet u, i.tables.admits i.profile a = true) ↔
        ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
      intro u
      constructor
      · intro hall a hr hea
        have hax : a ∈ i.tables.axiomSet u :=
          (axiomSet_iff _ u a).mpr ⟨(reaches_env hl u a).mpr hr, (isAxiom_env hl a).mpr hea⟩
        obtain ⟨k, ha, -⟩ := id hea
        exact (admits_env hl ha).mp ((admits_iff _ i.profile a).mp (hall a hax))
      · intro hall a hax
        obtain ⟨hr, hia⟩ := (axiomSet_iff _ u a).mp hax
        have hea := (isAxiom_env hl a).mp hia
        obtain ⟨k, ha, -⟩ := id hea
        exact (admits_iff _ i.profile a).mpr
          ((admits_env hl ha).mpr (hall a ((reaches_env hl u a).mp hr) hea))
    constructor
    · intro huses u hu
      obtain ⟨h1, h2⟩ := huses u (by simpa using (mem_usesOf info u).mpr hu)
      exact ⟨(hheld u).mp h1, (hadm u).mp h2⟩
    · intro huses u hu
      obtain ⟨h1, h2⟩ := huses u ((mem_usesOf info u).mp (by simpa using hu))
      exact ⟨(hheld u).mpr h1, (hadm u).mpr h2⟩

/-- `Facts.unread?` gives nothing when each constant is shown or fits. -/
theorem unread_none_of {i : Regula.Closed.Input}
    (h : ∀ x ∈ f.claimedConstants, f.shown x = true ∨ Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true) :
    f.unread? i = none := by
  simp only [Regula.Load.Facts.unread?]
  cases hu : f.claimedConstants.filter (!f.shown ·) with
  | nil => rfl
  | cons a l =>
    simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true']
    intro x hx
    have hmem : x ∈ f.claimedConstants.filter (!f.shown ·) := hu ▸ hx
    simp only [List.mem_filter, Bool.not_eq_true'] at hmem
    rcases h x hmem.1 with hs | hf
    · simp [hmem.2] at hs
    · simpa using hf

/-- Running a function of `Except` over a list fails only on a member. -/
theorem mapM_error {α β ε : Type} (g : α → Except ε β) (l : List α) (e : ε) (h : l.mapM g = .error e) :
    ∃ a ∈ l, ∃ e', g a = .error e' := by
  induction l generalizing e with
  | nil => simp [List.mapM_nil, pure, Except.pure] at h
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e' => exact ⟨a, List.mem_cons_self .., e', hg⟩
    | ok b =>
      rw [hg] at h
      simp only at h
      cases hl : l.mapM g with
      | error e' =>
        obtain ⟨x, hx, hy⟩ := ih e' hl
        exact ⟨x, List.mem_cons_of_mem _ hx, hy⟩
      | ok r =>
        rw [hl] at h
        cases h

/-- The floor gives the input: the loader refuses nothing that `LoadFloor` holds of. -/
theorem input_of_floor (h : LoadFloor f roots p) : ∃ i, f.input roots p = .ok i := by
  simp only [Regula.Load.Facts.input]
  split
  · rename_i m hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hnot := List.find?_some hfind
    have := h.roots m hmem
    simp [this] at hnot
  rename_i hfind
  split
  · rename_i why hm
    obtain ⟨⟨n, info⟩, hx, e', he⟩ := mapM_error _ _ _ hm
    have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx
    obtain ⟨m, hmod⟩ := h.placed n info hget
    simp [Regula.Load.Facts.decl, hmod] at he
  rename_i decls hm
  obtain ⟨h1, h2, -⟩ := Regula.Load.mapM_ok
    (fun x : Name × ConstantInfo => f.decl x.1 x.2 (f.stated.getD x.1 []))
    (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ hm
  split
  · rename_i why hadmit
    have hwf : (toSpecDraft
        { profile := p, modules := f.claimed, decls := decls,
          unique := f.decls_nodup (stated := fun n => f.stated.getD n []) hm }).WellFormed := by
      rw [wf_toSpecDraft_iff]
      refine ⟨fun x hx u hu => ?_, h.form.claims⟩
      obtain ⟨⟨n, info⟩, hin, hok⟩ := h1 x hx
      obtain ⟨m, -, rfl⟩ := decl_ok hok
      have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hin
      obtain ⟨k, hk⟩ := h.form.closed n u ⟨info, hget, (mem_usesIn info _ u).mp hu⟩
      obtain ⟨y, hy, hoky⟩ := h2 (u, k) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk)
      exact ⟨y, hy, f.decl_name hoky⟩
    obtain ⟨i, hi⟩ := (admit_ok_iff _).mpr hwf
    rw [hi] at hadmit
    cases hadmit
  rename_i i' hadmit
  have hl := loaded_of_parts hfind hm hadmit
  have hnone : f.unread? i' = none := unread_none_of fun x hx => by
    by_cases hs : f.shown x = true
    · exact .inl hs
    · exact .inr ((fitsUnshown_iff hl x).mpr (h.unshown x hx (by simpa using hs)))
  rw [hnone]
  exact ⟨_, rfl⟩

/-- The verdict of the loader's result is a pass exactly on `LoadFloor`, which names no field of the input: so for every
environment the loader and the rules refuse only what that statement excludes. -/
theorem pass_iff_floor :
    (Regula.Closed.decision (f.input roots p)).verdict = .pass ↔ LoadFloor f roots p := by
  constructor
  · intro h
    obtain ⟨h1, -, h3, h4, h5⟩ := pass_floor h
    obtain ⟨i, hi, -⟩ := decision_pass h
    have hl := input_loaded hi
    refine ⟨h1, fun n info hn => ?_, h4, h5, fun x hx hs => ?_⟩
    · obtain ⟨m, hm⟩ := module_of hl hn
      exact ⟨m, hm⟩
    · rcases input_kept hi hx with h' | h'
      · simp [hs] at h'
      · exact (fitsUnshown_iff hl x).mp h'
  · intro h
    obtain ⟨i, hi⟩ := input_of_floor h
    have hl := input_loaded hi
    rw [hi]
    exact (pass_iff hi).mpr ⟨h.form, h.floor⟩

end Loader

end RegulaSpecification
