import Regula.Load
import Regula.Shell
import RegulaSpecification.Proofs.Verdict

/-!
# The loader, against the environment

`Regula.Load.Facts.input` is the pure function that fills the closed input from a loaded
environment, and `Regula.Closed.run` the verdict that the checker gives on that input. `pass_iff`
relates the two to the environment alone: for every environment, a pass is exactly `EnvForm` and
`EnvFloor`, two statements that mention no field of the input. Each constant is read from
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
lists them, and the thin effects that no theorem here reads: `Regula.Load.places`,
`Regula.Load.loadInput` and `Regula.Shell.run`.
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
  | _, _ => False

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
mentions is held, at least one module is claimed, and each claimed module is loaded. -/
structure EnvForm (f : Regula.Load.Facts) : Prop where
  /-- Each mentioned constant is held. -/
  closed : ∀ n u, EnvMentions f n u → ∃ info', f.env.constants.map₁[u]? = some info'
  /-- At least one module is claimed. -/
  claims : f.claimed ≠ []
  /-- Each claimed module is loaded. -/
  loaded : ∀ m ∈ f.claimed, m ∈ f.env.header.moduleNames.toList

/-- Profile `p` admits the axiom `a` of the environment: one of Lean's three, the toolchain's own
constant of that name, and in the profile's set. -/
def EnvAdmits (f : Regula.Load.Facts) : Regula.Closed.Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, a => (a = ``propext ∨ a = ``Quot.sound) ∧ f.toolchain a = true
  | .standardLogical, a =>
    (a = ``propext ∨ a = ``Quot.sound ∨ a = ``Classical.choice) ∧ f.toolchain a = true

/-- The form of a recursion helper: a partial, safe-flagged constant `b._unsafe_rec` with no
`@[implemented_by]` and not `@[extern]`, beside a safe, total definition `b` of its module of which
the same two hold, and of whose name no loaded module states an axiom. -/
def EnvHelper (f : Regula.Load.Facts) (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  info.isPartial = true ∧ info.isUnsafe = false ∧
    Lean.Compiler.getImplementedBy? f.env n = none ∧ Lean.isExtern f.env n = false ∧
    ∃ b v, n = .str b "_unsafe_rec" ∧ f.env.constants.map₁[b]? = some (.defnInfo v) ∧
      (∀ w ∈ f.stated.getD b [], ¬ AxiomInfo w) ∧
      f.moduleOf b = some m ∧ (ConstantInfo.defnInfo v).isUnsafe = false ∧
      (ConstantInfo.defnInfo v).isPartial = false ∧
      Lean.Compiler.getImplementedBy? f.env b = none ∧ Lean.isExtern f.env b = false

/-- What RG1001 to RG1006 state of each constant of a claimed module, in the terms of the
environment: no loaded module states an axiom of its name (RG1001). When it is unsafe or partial, or
has a recursion helper's name, it has the form of a recursion helper (RG1006), and its value mentions
no loop construct of Lean (RG1006). Each axiom that it reaches, through what any loaded module's own
data states, is one that the profile admits (RG1005), which also excludes `sorryAx` (RG1002), a
native proof's axiom (RG1004) and every other axiom (RG1003): `rg1005_of_hole`,
`rg1005_of_compiler`, `rg1005_of_unknown`. -/
def EnvFloor (f : Regula.Load.Facts) (p : Regula.Closed.Profile) : Prop :=
  ∀ n info m, f.env.constants.map₁[n]? = some info → f.moduleOf n = some m → m ∈ f.claimed →
    ¬ EnvAxiom f n ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      EnvHelper f n info m) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ a, EnvReaches f n a → EnvAxiom f a → EnvAdmits f p a

/-! ## What the input holds -/

/-- What running a function of `Except` over a list gives, member by member. -/
theorem mapM_ok {α β ε : Type} (g : α → Except ε β) (name : β → Name) (key : α → Name)
    (hname : ∀ a b, g a = .ok b → name b = key a) (l : List α) (r : List β)
    (h : l.mapM g = .ok r) :
    (∀ b ∈ r, ∃ a ∈ l, g a = .ok b) ∧ (∀ a ∈ l, ∃ b ∈ r, g a = .ok b) ∧
      r.map name = l.map key := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e =>
      rw [hg] at h
      cases h
    | ok b =>
      rw [hg] at h
      simp only at h
      cases hl : l.mapM g with
      | error e =>
        rw [hl] at h
        cases h
      | ok r' =>
        rw [hl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := ih r' hl
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, List.mem_cons_self .., hg⟩
          · obtain ⟨x, hx, hxy⟩ := h1 y hy
            exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b, List.mem_cons_self .., hg⟩
          · obtain ⟨y, hy, hxy⟩ := h2 x hx
            exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
        · simp [hname a b hg, h3]

/-- What the loader gives, in the terms of the environment. -/
structure Loaded (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile)
    (i : Regula.Closed.Input) : Prop where
  /-- The profile is the one that the shell read. -/
  profile : i.profile = p
  /-- The claimed modules are those of the facts. -/
  modules : i.modules = f.claimed
  /-- The loaded modules are the header's. -/
  loads : i.loads = f.env.header.moduleNames.toList
  /-- Each module of a default target is claimed. -/
  roots : ∀ r ∈ roots, r ∈ f.claimed
  /-- Each constant of the input is a constant of the environment, with the fields it gives. -/
  sound : ∀ d ∈ i.decls, ∃ info, f.env.constants.map₁[d.name]? = some info ∧
    f.moduleOf d.name = some d.module ∧
      d = f.declIn d.name d.module info (f.stated.getD d.name [])
  /-- Each constant of the environment is in the input. -/
  whole : ∀ n info, f.env.constants.map₁[n]? = some info →
    ∃ m, f.moduleOf n = some m ∧ f.declIn n m info (f.stated.getD n []) ∈ i.decls
  /-- No name repeats: the keys of a hash map are distinct. -/
  unique : (i.decls.map (·.name)).Nodup
  /-- Each constant of a claimed module's `.olean` is shown to the rules, or is what they admit. -/
  kept : ∀ x ∈ f.claimedConstants,
    f.shown x = true ∨ Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true

theorem decl_ok {n : Name} {info : ConstantInfo} {s : List ConstantInfo} {d : Regula.Closed.Decl}
    (h : f.decl n info s = .ok d) : f.moduleOf n = some d.module ∧ d.name = n ∧
      d = f.declIn n d.module info s := by
  unfold Regula.Load.Facts.decl at h
  split at h
  · rename_i m hm
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨hm, rfl, rfl⟩
  · cases h

theorem shown_true {x : Name × Name × ConstantInfo} (h : f.shown x = true) :
    ∃ k m, f.env.constants.map₁[x.2.1]? = some k ∧
      Regula.Load.readOf k = Regula.Load.readOf x.2.2 ∧ f.moduleOf x.2.1 = some m ∧
      m ∈ f.claimed := by
  unfold Regula.Load.Facts.shown at h
  split at h
  · rename_i k m h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    exact ⟨k, m, h1, h.1, h2, h.2⟩
  · cases h

theorem unread_none {x : Name × Name × ConstantInfo} (h : f.unread? i = none)
    (hx : x ∈ f.claimedConstants) :
    f.shown x = true ∨ Regula.Load.fitsUnshown i.tables x.2.1 x.2.2 = true := by
  by_cases hs : f.shown x = true
  · exact .inl hs
  refine .inr ?_
  have hmem : x ∈ f.claimedConstants.filter (!f.shown ·) := by simp [hx, hs]
  unfold Regula.Load.Facts.unread? at h
  cases hu : f.claimedConstants.filter (!f.shown ·) with
  | nil =>
    rw [hu] at hmem
    cases hmem
  | cons a l =>
    rw [hu] at h hmem
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
    simpa using h x hmem

/-- The function that fills the input gives what `Loaded` states. -/
theorem input_loaded (h : f.input roots p = .ok i) : Loaded f roots p i := by
  unfold Regula.Load.Facts.input at h
  split at h
  · cases h
  rename_i hfind
  cases hm : f.env.constants.map₁.toList.mapM
      (fun x => f.decl x.1 x.2 (f.stated.getD x.1 [])) with
  | error e =>
    simp only [hm, Except.bind] at h
    cases h
  | ok decls =>
    simp only [hm, Except.bind] at h
    split at h
    · cases h
    · rename_i hkeeps
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := mapM_ok
        (fun x : Name × ConstantInfo => f.decl x.1 x.2 (f.stated.getD x.1 []))
        (·.name) (·.1) (fun a _ hb => (decl_ok hb).2.1) _ _ hm
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr
        have := List.find?_eq_none.mp hfind r hr
        simpa using this
      · intro d hd
        obtain ⟨⟨n, info⟩, hx, hok⟩ := h1 d hd
        obtain ⟨hmod, hname, hdv⟩ := decl_ok hok
        have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx
        subst hname
        exact ⟨info, hget, hmod, hdv⟩
      · intro n info hn
        obtain ⟨d, hd, hok⟩ := h2 (n, info) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hn)
        obtain ⟨hmod, -, hdv⟩ := decl_ok hok
        exact ⟨d.module, hmod, hdv ▸ hd⟩
      · show (decls.map (·.name)).Nodup
        rw [h3]
        have := Std.HashMap.distinct_keys_toList (m := f.env.constants.map₁)
        refine List.pairwise_map.mpr (this.imp ?_)
        intro a b hab heq
        simp [heq] at hab
      · exact fun x hx => unread_none hkeeps hx

/-! ## From the input's statements to the environment's -/

theorem claimed_iff (hl : Loaded f roots p i) (m : Name) :
    (toSpec i).ClaimedModule m ↔ m ∈ f.claimed := by
  simp [Input.ClaimedModule, toSpec, hl.modules]

/-- A constant of the specification's input is a constant of the environment. -/
theorem of_mem {x : Decl} (hl : Loaded f roots p i) (hx : x ∈ (toSpec i).decls) :
    ∃ info, f.env.constants.map₁[x.name]? = some info ∧ f.moduleOf x.name = some x.module ∧
      x = decl (f.declIn x.name x.module info (f.stated.getD x.name [])) := by
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  obtain ⟨info, hn, hm, hv⟩ := hl.sound d hd
  exact ⟨info, hn, hm, congrArg decl hv⟩

/-- A constant of the environment is a constant of the specification's input. -/
theorem to_mem (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) {m : Name} (hm : f.moduleOf n = some m) :
    decl (f.declIn n m info (f.stated.getD n [])) ∈ (toSpec i).decls := by
  obtain ⟨m', hm', hmem⟩ := hl.whole n info hn
  rw [hm] at hm'
  cases hm'
  exact mem_decls.mpr ⟨_, hmem, rfl⟩

/-- A constant of the environment has a module. -/
theorem module_of (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) : ∃ m, f.moduleOf n = some m := by
  obtain ⟨m, hm, -⟩ := hl.whole n info hn
  exact ⟨m, hm⟩

theorem resolves_env (hl : Loaded f roots p i) (u : Name) :
    (toSpec i).Resolves u ↔ ∃ info, f.env.constants.map₁[u]? = some info := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨info, hn, -, -⟩ := of_mem hl hx
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
      obtain ⟨info, hn, -, hv⟩ := of_mem hl hx
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
  unfold Regula.Load.kindIn
  split
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    simpa using .inr hs
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    simp [kindOf_axiom, hs]

theorem kind_axiom {n m : Name} {info : ConstantInfo} {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .axiom ↔ AxiomInfo info ∨ ∃ v ∈ s, AxiomInfo v := by
  rw [← kindIn_axiom]
  simp only [decl, Regula.Load.Facts.declIn]
  cases Regula.Load.kindIn info s <;> simp [constKind]

theorem kind_definition {n m : Name} {info : ConstantInfo} {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .definition ↔
      (∃ v, info = .defnInfo v) ∧ ∀ w ∈ s, ¬ AxiomInfo w := by
  have hconst : (decl (f.declIn n m info s)).kind = .definition ↔
      Regula.Load.kindIn info s = .definition := by
    simp only [decl, Regula.Load.Facts.declIn]
    cases Regula.Load.kindIn info s <;> simp [constKind]
  rw [hconst]
  unfold Regula.Load.kindIn
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
theorem kind_envAxiom {n m : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) :
    (decl (f.declIn n m info (f.stated.getD n []))).kind = .axiom ↔ EnvAxiom f n := by
  rw [kind_axiom]
  constructor
  · exact fun h => ⟨info, hn, h⟩
  · rintro ⟨k, hk, h⟩
    rw [hn] at hk
    cases hk
    exact h

theorem isAxiom_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).IsAxiom a ↔ EnvAxiom f a := by
  constructor
  · rintro ⟨x, hx, rfl, hk⟩
    obtain ⟨info, hn, -, hv⟩ := of_mem hl hx
    rw [hv] at hk
    exact (kind_envAxiom hn).mp hk
  · intro h
    obtain ⟨info, hn, -⟩ := id h
    obtain ⟨m, hm⟩ := module_of hl hn
    exact ⟨_, to_mem hl hn hm, rfl, (kind_envAxiom hn).mpr h⟩

theorem known_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).Known a ↔ a ∈ logicalAxioms ∧ (∃ info, f.env.constants.map₁[a]? = some info) ∧
      f.toolchain a = true := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨x, hx, rfl, ht⟩
    obtain ⟨info, hn, -, hv⟩ := of_mem hl hx
    rw [hv] at ht
    exact ⟨⟨info, hn⟩, ht⟩
  · rintro ⟨⟨info, hn⟩, ht⟩
    obtain ⟨m, hm⟩ := module_of hl hn
    exact ⟨_, to_mem hl hn hm, rfl, ht⟩

/-- What a profile admits of a constant of the environment. -/
theorem admits_env (hl : Loaded f roots p i) {a : Name} {info : ConstantInfo}
    (ha : f.env.constants.map₁[a]? = some info) :
    (toSpec i).Admits (toSpec i).profile a ↔ EnvAdmits f p a := by
  have hp : (toSpec i).profile = profile p := by simp [toSpec, hl.profile]
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

/-- The form of a recursion helper in the input is its form in the environment. -/
theorem helper_env (hl : Loaded f roots p i) (n m : Name) (info : ConstantInfo) :
    (toSpec i).RecursionHelper (decl (f.declIn n m info (f.stated.getD n []))) ↔
      EnvHelper f n info m := by
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  constructor
  · rintro ⟨base, hb, hname, hk, hm, hu, hp', hi', he⟩
    obtain ⟨info', hn', hm', hv⟩ := of_mem hl hb
    rw [hv] at hk hu hp' hi' he
    obtain ⟨⟨v, rfl⟩, hs⟩ := kind_definition.mp hk
    have hm'' : base.module = m := hm
    exact ⟨base.name, v, hname, hn', hs, hm'' ▸ hm', hu, hp', hi', he⟩
  · rintro ⟨b, v, hname, hn', hs, hm', hu, hp', hi', he⟩
    exact ⟨_, to_mem hl hn' hm', hname, kind_definition.mpr ⟨⟨v, rfl⟩, hs⟩, rfl, hu, hp', hi', he⟩

/-- The closed form of the input is `EnvForm` of the environment. -/
theorem wf_env (hl : Loaded f roots p i) : (toSpec i).WellFormed ↔ EnvForm f := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro n u ⟨info, hn, hm⟩
      obtain ⟨m, hmod⟩ := module_of hl hn
      exact (resolves_env hl u).mp (h.closed _ (to_mem hl hn hmod) u ((mem_usesIn info _ u).mpr hm))
    · simpa [toSpec, hl.modules] using h.claims
    · simpa [toSpec, hl.modules, hl.loads] using h.loaded
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [names_toSpec]
      exact hl.unique
    · intro x hx u hu
      obtain ⟨info, hn, -, hv⟩ := of_mem hl hx
      rw [hv] at hu
      exact (resolves_env hl u).mpr (h.closed _ u ⟨info, hn, (mem_usesIn info _ u).mp hu⟩)
    · simpa [toSpec, hl.modules] using h.claims
    · simpa [toSpec, hl.modules, hl.loads] using h.loaded

/-- Every rule holding of the input is `EnvFloor` of the environment. -/
theorem allHold_env (hl : Loaded f roots p i) : AllHold (toSpec i) ↔ EnvFloor f p := by
  constructor
  · rintro ⟨h1, -, -, -, h5, h6⟩ n info m hn hm hc
    have hx := to_mem hl hn hm
    have hcm := (claimed_iff hl m).mpr hc
    refine ⟨fun hax => ?_, fun hflag => ?_, fun l hl' hv => ?_, fun a hr hax => ?_⟩
    · exact h1 n ⟨_, hx, rfl, hcm, (kind_envAxiom hn).mpr hax⟩
    · refine Classical.byContradiction fun hno => h6 n ⟨_, hx, rfl, hcm, .inl ⟨hflag, fun hh => ?_⟩⟩
      exact hno ((helper_env hl n m info).mp hh)
    · exact h6 n ⟨_, hx, rfl, hcm, .inr ⟨l, hl', (mem_valueUsesOf info l).mpr hv⟩⟩
    · obtain ⟨k, ha, -⟩ := id hax
      refine Classical.byContradiction fun hno => h5 n ⟨⟨_, hx, rfl, hcm⟩, a,
        ⟨(reaches_env hl n a).mpr hr, (isAxiom_env hl a).mpr hax⟩, fun hadm => ?_⟩
      exact hno ((admits_env hl ha).mp hadm)
  · intro hf
    have no5 : ∀ c, ¬ Violates1005 (toSpec i) c := by
      rintro c ⟨⟨x, hx, rfl, hcm⟩, a, ⟨hr, hax⟩, hna⟩
      obtain ⟨info, hn, hm, -⟩ := of_mem hl hx
      have hax' := (isAxiom_env hl a).mp hax
      obtain ⟨k, ha, -⟩ := id hax'
      exact hna ((admits_env hl ha).mpr
        ((hf _ _ _ hn hm ((claimed_iff hl _).mp hcm)).2.2.2 a ((reaches_env hl _ a).mp hr) hax'))
    refine ⟨?_, fun c h => no5 c (rg1005_of_hole h), fun c h => no5 c (rg1005_of_unknown h),
      fun c h => no5 c (rg1005_of_compiler h), no5, ?_⟩
    · rintro c ⟨x, hx, rfl, hcm, hk⟩
      obtain ⟨info, hn, hm, hv⟩ := of_mem hl hx
      rw [hv] at hk
      exact (hf _ _ _ hn hm ((claimed_iff hl _).mp hcm)).1 ((kind_envAxiom hn).mp hk)
    · rintro c ⟨x, hx, rfl, hcm, hv⟩
      obtain ⟨info, hn, hm, hd⟩ := of_mem hl hx
      obtain ⟨-, h6, h7, -⟩ := hf _ _ _ hn hm ((claimed_iff hl _).mp hcm)
      rw [hd] at hv
      rcases hv with ⟨hflag, hno⟩ | ⟨l, hl', hu⟩
      · exact hno ((helper_env hl _ _ info).mpr (h6 hflag))
      · exact h7 l hl' ((mem_valueUsesOf info l).mp hu)

/-! ## The theorems -/

/-- For every environment, every set of facts about it and every profile: when the loader gives an
input, the checker passes on it exactly when the environment has `EnvForm` and `EnvFloor`. Neither
names the input, and no hypothesis says anything of the loader. -/
theorem pass_iff (h : f.input roots p = .ok i) :
    (Regula.Closed.run i).1 = .pass ↔ EnvForm f ∧ EnvFloor f p := by
  have hl := input_loaded h
  rw [run_pass_iff, wf_env hl, allHold_env hl]

/-- A load that fails is never a pass. -/
theorem decision_failed (why : String) :
    (Regula.Shell.decision (.error why)).1 = .incomplete := rfl

/-- The verdict that the shell reports is a pass only on an input that the load gave. -/
theorem decision_pass {r : Except String Regula.Closed.Input}
    (h : (Regula.Shell.decision r).1 = .pass) :
    ∃ i, r = .ok i ∧ (Regula.Closed.run i).1 = .pass := by
  cases r with
  | error why => cases h
  | ok i => exact ⟨i, rfl, h⟩

/-- The floor, on the path that the shell runs: when the verdict of the loader's result is a pass,
each module of a default target is claimed, each constant of the environment has a module, and the
environment has `EnvForm` and `EnvFloor`. -/
theorem pass_floor (h : (Regula.Shell.decision (f.input roots p)).1 = .pass) :
    (∀ r ∈ roots, r ∈ f.claimed) ∧
      (∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.moduleOf n = some m) ∧
      EnvForm f ∧ EnvFloor f p := by
  obtain ⟨i, hi, hp⟩ := decision_pass h
  have hl := input_loaded hi
  exact ⟨hl.roots, fun _ _ hn => module_of hl hn, (pass_iff hi).mp hp⟩

/-- What the claimed modules' own `.olean` files hold: `Facts.claimedConstants` lists each constant
of each claimed module, as the header of the environment gives that module's data. -/
theorem mem_claimedConstants {m n : Name} {info : ConstantInfo} :
    (m, n, info) ∈ f.claimedConstants ↔ m ∈ f.claimed ∧
      ∃ data, (m, data) ∈ f.env.header.moduleNames.zip f.env.header.moduleData ∧
        (n, info) ∈ data.constNames.zip data.constants := by
  simp only [Regula.Load.Facts.claimedConstants, List.mem_flatMap, List.mem_filter,
    Array.mem_toList_iff, List.mem_map, Prod.mk.injEq, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨m', data⟩, ⟨hz, hc⟩, ⟨n', info'⟩, hx, rfl, rfl, rfl⟩
    exact ⟨hc, data, hz, hx⟩
  · rintro ⟨hc, data, hz, hx⟩
    exact ⟨(m, data), ⟨hz, hc⟩, (n, info), hx, rfl, rfl, rfl⟩

/-- A pass holds of each constant of a claimed module as that module's own `.olean` states it, not
only of the constant that Lean's import keeps under its name (`Facts.shown`, `Facts.unread?`): it is
no axiom, it is a partial, safe-flagged constant when it has either flag or a recursion helper's
name, its value mentions no loop construct, and each axiom that it reaches, through what any loaded
module's own data states, is one that the profile admits. -/
theorem pass_held (h : (Regula.Shell.decision (f.input roots p)).1 = .pass) {m n : Name}
    {info : ConstantInfo} (hx : (m, n, info) ∈ f.claimedConstants) :
    (∀ v, info ≠ .axiomInfo v) ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      info.isPartial = true ∧ info.isUnsafe = false) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ∀ u, Mentions info u → ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨i, hi, hp⟩ := decision_pass h
  have hl := input_loaded hi
  rcases (hl.kept _ hx).symm with hfits | hshown
  · simp only [Regula.Load.fitsUnshown, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      List.all_eq_true, Array.all_eq_true_iff_forall_mem] at hfits
    obtain ⟨⟨⟨⟨⟨hkind, hunsafe⟩, hpartial⟩, hname⟩, hloop⟩, huses⟩ := hfits
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
        (axiomSet_iff u a).mpr ⟨(reaches_env hl u a).mpr hr, (isAxiom_env hl a).mpr hea⟩
      obtain ⟨k, ha, -⟩ := id hea
      exact (admits_env hl ha).mp ((admits_iff hl.unique i.profile a).mp (hall a hax))
  obtain ⟨k, m', hk, hread, hmod, hclaimed⟩ := shown_true hshown
  obtain ⟨h1, h2, h3, h4⟩ := ((pass_iff hi).mp hp).2 n k m' hk hmod hclaimed
  simp only [Regula.Load.readOf, Prod.mk.injEq] at hread
  obtain ⟨hkind, hunsafe, hpartial, huses, hvalue⟩ := hread
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro v rfl
    have hax : AxiomInfo k := (kindOf_axiom k).mp (by simpa [Regula.Load.kindOf] using hkind)
    exact h1 ⟨k, hk, .inl hax⟩
  · intro hflag
    have hflag' : k.isUnsafe = true ∨ k.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec" := by
      rwa [hunsafe, hpartial]
    obtain ⟨hpart, hsafe, -⟩ := h2 hflag'
    exact ⟨hpartial ▸ hpart, hunsafe ▸ hsafe⟩
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
      ∃ text, args = [text] ∧ Regula.Shell.profileOf? text = some q := by
  unfold Regula.Shell.profileOfRun at h
  split at h
  · cases h
  · rename_i hs
    have hs' : Regula.Shell.supportsLean version commit = true := by simpa using hs
    simp only [Regula.Shell.supportsLean, Bool.and_eq_true, beq_iff_eq] at hs'
    refine ⟨hs'.1, hs'.2, ?_⟩
    split at h
    · rename_i text
      split at h
      · rename_i q' hq
        simp only [Except.ok.injEq] at h
        exact ⟨text, rfl, h ▸ hq⟩
      · cases h
    · cases h

/-- The places of the modules decide what `Facts.ofPlaces` claims: the modules whose `.olean` lies
below the root package's library directory. -/
theorem mem_claimed_ofPlaces (env : Lean.Environment) (td rd : System.FilePath)
    (ps : Array System.FilePath) (m : Name) :
    m ∈ (Regula.Load.Facts.ofPlaces env td rd ps).claimed ↔
      ∃ (k : Nat) (place : System.FilePath), env.header.moduleNames[k]? = some m ∧
        ps[k]? = some place ∧ Regula.Load.below rd place = true := by
  simp only [Regula.Load.Facts.ofPlaces, List.mem_map, List.mem_filter, Array.mem_toList_iff,
    Array.mem_iff_getElem?, Array.getElem?_zip_eq_some]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨k, h1, h2⟩, h3⟩, rfl⟩
    exact ⟨k, b, h1, h2, h3⟩
  · rintro ⟨k, place, h1, h2, h3⟩
    exact ⟨(m, place), ⟨⟨k, h1, h2⟩, h3⟩, rfl⟩

/-- The places of the modules decide `Facts.toolchain` of `Facts.ofPlaces`: the constants whose
module's `.olean` lies below the toolchain's library directory. -/
theorem toolchain_ofPlaces (env : Lean.Environment) (td rd : System.FilePath)
    (ps : Array System.FilePath) (n : Name) :
    (Regula.Load.Facts.ofPlaces env td rd ps).toolchain n = true ↔
      ∃ (idx : Lean.ModuleIdx) (place : System.FilePath), env.getModuleIdxFor? n = some idx ∧
        ps[idx.toNat]? = some place ∧ Regula.Load.below td place = true := by
  simp only [Regula.Load.Facts.toolchain, Regula.Load.Facts.ofPlaces]
  cases hi : env.getModuleIdxFor? n with
  | none => simp
  | some idx =>
    simp only [Option.bind_some, Array.getElem?_map]
    cases hp : ps[idx.toNat]? with
    | none => simp [hp]
    | some place => simp [hp]

/-- The text of a profile names it: the three spellings and no other. -/
theorem profileOf_eq_some {text : String} {q : Regula.Closed.Profile}
    (h : Regula.Shell.profileOf? text = some q) :
    (text = "kernel-only" ∧ q = .kernelOnly) ∨ (text = "choice-free" ∧ q = .choiceFree) ∨
      (text = "standard-logical" ∧ q = .standardLogical) := by
  unfold Regula.Shell.profileOf? at h
  split at h <;> simp_all

/-- `below` states what its name says, by the components of the two paths: the directory's are a
proper prefix of the path's. -/
theorem below_iff (dir path : System.FilePath) :
    Regula.Load.below dir path = true ↔
      Regula.Load.parts dir <+: Regula.Load.parts path ∧
        Regula.Load.parts dir ≠ Regula.Load.parts path := by
  simp [Regula.Load.below, List.isPrefixOf_iff_prefix]

end Loader

end RegulaSpecification
