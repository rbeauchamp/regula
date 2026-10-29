import RegulaSpecification.Gate

/-!
# The cases each rule must admit and must refuse

For each kept and new rule, a small well-formed project that the rule must refuse, and a subject
of a realistic compliant project (`base`) that it must admit. With them `RuleRecord.adequate`
discharges lean-intent's obligations for the rule's record, and `silent_fails` and `noisy_fails`
prove that neither the checker that reports nothing nor the one that reports every candidate meets
it. A statement that a do-nothing checker met, or that refused the compliant case, would fail here.

`base` is one claimed library `Good` (choice-free, reported execution) and one claimed executable
`app` (standard-logical, checked execution). `Good.t` is a theorem that uses `propext`; `Good.f` is
a safe recursive definition with the recursion helper Lean adds, a decision contract `Good.f_spec`
against `Good.Spec`, and a deliverable with the intent record `Good.intent`; `main` runs `Good.f`.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Witnesses

/-- A safe, computable, project constant with nothing marked. -/
def plain (name module : Name) (kind : Kind) (uses : List Name) : Decl :=
  { name, module, kind, isUnsafe := false, isPartial := false, uses, implementedBy := none,
    csimpTarget := none, isExtern := false, isInitialized := false, isNoncomputable := false, isBoolTest := false,
    inToolchain := false }

/-- A constant of the toolchain's own library. -/
def toolchain (name : Name) (kind : Kind) : Decl :=
  { plain name `Init.Core kind [] with inToolchain := true }

/-- The two options every claimed target sets. -/
def strict : List (Name × String) := [(`autoImplicit, "false"), (`relaxedAutoImplicit, "false")]

def helperDecl : Decl :=
  { plain `Good.f._unsafe_rec `Good .definition [`Good.f._unsafe_rec] with isPartial := true }

def baseDecls : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext],
    plain `Good.f `Good .definition [], helperDecl, plain `Good.Spec `Good .definition [],
    plain `Good.f_spec `Good .theorem [`Good.f, `Good.Spec],
    plain `Good.intent `Good .definition [], plain `main `App .definition [`Good.f]]

/-- The compliant project. -/
def base : Input where
  targets :=
    [⟨`Good, .library, [`Good], strict, [], true⟩, ⟨`app, .executable, [`App], strict, [], true⟩]
  manifest := [⟨`Good, .claimed .choiceFree .report⟩, ⟨`app, .claimed .standardLogical .checked⟩]
  modules := [⟨`Good, [`Init], [`Lean.declRangeExt]⟩, ⟨`App, [`Init, `Good], []⟩]
  decls := baseDecls
  loads := [`Good, `App]
  contracts := [⟨`Good.f_spec, `Good.f, 0, .decides, [`Good.Spec], []⟩]
  decisions := [`Good.f]
  decidableResults := []
  inventory := some [(`Good.f, `Good.intent)]
  proved := [.obligation .o1 `Good.intent, .obligation .o2 `Good.intent,
    .obligation .o3 `Good.intent, .obligation .o4 `Good.intent, .obligation .o5 `Good.intent,
    .obligation .o2Run `Good.intent, .obligation .nondegenerate `Good.intent,
    .fulfils `Good.f `Good.intent, .corresponds `Good.f]
  confirmed := []

/-- `base` with the constants `extra` added in module `Good`. -/
def withDecls (extra : List Decl) : Input := { base with decls := base.decls ++ extra }

/-- What reaches from a name in `S` stays in `S` when each constant named in `S` uses only
names in `S`. -/
theorem reaches_closed {i : Input} (S : Name → Prop)
    (h : ∀ d ∈ i.decls, S d.name → ∀ u ∈ d.uses, S u) {c e : Name} (hc : S c)
    (hr : i.Reaches c e) : S e := by
  induction hr with
  | refl => exact hc
  | step d hd hn hu _ ih => exact ih (h d hd (hn ▸ hc) _ hu)

theorem wf_base : base.WellFormed := by
  refine ⟨by decide, ?_, ?_⟩
  · intro d hd
    simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
    suffices h : ∀ u ∈ d.uses, u ∈ baseDecls.map (·.name) by
      intro u hu
      obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h u hu)
      exact ⟨d', hd', hn⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [baseDecls, plain, toolchain, helperDecl]
  · intro t ht m hm
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp at hm <;> subst hm <;> simp [base]

/-- From `Good.t`, only `Good.t` and `propext` are reached in `base`. -/
theorem base_reaches_t {e : Name} (h : base.Reaches `Good.t e) : e = `Good.t ∨ e = ``propext := by
  refine reaches_closed (i := base) (fun n => n = `Good.t ∨ n = ``propext) ?_ (Or.inl rfl) h
  intro d hd hS u hu
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl] at hS hu ⊢ <;> simp_all

/-- In `base`, the only axiom `Good.t` depends on is `propext`. -/
theorem base_axioms_t {a : Name} (h : base.AxiomOf `Good.t a) : a = ``propext := by
  rcases base_reaches_t h.1 with rfl | rfl
  · obtain ⟨d, hd, hn, hk⟩ := h.2
    simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [plain, toolchain, helperDecl] at hn hk
  · rfl

theorem base_known_propext : base.Known ``propext :=
  ⟨by simp [logicalAxioms], toolchain ``propext .axiom, by simp [base, baseDecls], rfl, rfl⟩

theorem base_claims_good : base.Claimed `Good .choiceFree .report :=
  ⟨⟨`Good, .library, [`Good], strict, [], true⟩, by simp [base], by simp, by simp [base]⟩

theorem base_claimed_t : base.ClaimedName `Good.t :=
  ⟨plain `Good.t `Good .theorem [``propext], by simp [base, baseDecls], rfl, _, _, base_claims_good⟩

theorem resolves_withDecls {extra : List Decl} {u : Name} (h : base.Resolves u) :
    (withDecls extra).Resolves u := by
  obtain ⟨d, hd, hn⟩ := h
  exact ⟨d, List.mem_append_left _ hd, hn⟩

/-- `base` with constants added stays well-formed when the names stay distinct and each added
constant mentions only constants of the result. -/
theorem wf_withDecls (extra : List Decl)
    (hn : ((base.decls ++ extra).map (·.name)).Nodup)
    (hc : ∀ d ∈ extra, ∀ u ∈ d.uses, (withDecls extra).Resolves u) :
    (withDecls extra).WellFormed := by
  refine ⟨hn, ?_, wf_base.loaded⟩
  intro d hd u hu
  rcases List.mem_append.mp hd with hd | hd
  · exact resolves_withDecls (wf_base.closed d hd u hu)
  · exact hc d hd u hu

/-- Well-formedness reads only the constants, the targets and the modules. -/
theorem wf_congr {i j : Input} (h : i.WellFormed) (hd : j.decls = i.decls)
    (ht : j.targets = i.targets) (hm : j.modules = i.modules) : j.WellFormed := by
  obtain ⟨u, c, l⟩ := h
  refine ⟨by rw [hd]; exact u, ?_, ?_⟩
  · intro d hdj v hv
    rw [hd] at hdj
    obtain ⟨d', h1, h2⟩ := c d hdj v hv
    exact ⟨d', by rw [hd]; exact h1, h2⟩
  · intro t htj m hm'
    rw [ht] at htj
    obtain ⟨r, h1, h2⟩ := l t htj m hm'
    exact ⟨r, by rw [hm]; exact h1, h2⟩

/-- The added constants mention only constants of the result. -/
theorem uses_resolve {extra : List Decl}
    (h : ∀ d ∈ extra, ∀ u ∈ d.uses, u ∈ (base.decls ++ extra).map (·.name)) :
    ∀ d ∈ extra, ∀ u ∈ d.uses, (withDecls extra).Resolves u := by
  intro d hd u hu
  obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h d hd u hu)
  exact ⟨d', hd', hn⟩

/-- A claimed module of `base` with constants added. -/
theorem claimed_withDecls {extra : List Decl} : (withDecls extra).Claimed `Good .choiceFree .report :=
  base_claims_good

end Witnesses

end RegulaSpecification
