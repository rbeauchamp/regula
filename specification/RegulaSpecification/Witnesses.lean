import RegulaSpecification.Gate

/-!
# The cases each rule must admit and must refuse

For each rule, a small well-formed project that the rule must refuse, and a subject of a compliant
project (`base`) that it must admit. With them `RuleRecord.adequate` discharges lean-intent's
obligations for the rule's record, and `silent_fails` and `noisy_fails` prove that neither the
checker that reports nothing nor the one that reports every candidate meets it. A statement that a
do-nothing checker met, or that refused the compliant case, would fail here.

`base` is one claimed module `Good` under the choice-free profile. `Good.t` is a theorem that uses
`propext`, and `Good.f` is a safe recursive definition with the recursion helper Lean adds.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Witnesses

/-- A safe constant with nothing marked, outside the toolchain. -/
def plain (name module : Name) (kind : Kind) (uses : List Name) : Decl :=
  { name, module, kind, isUnsafe := false, isPartial := false, uses, valueUses := [],
    implementedBy := none,
    isExtern := false, inToolchain := false }

/-- A constant of the toolchain's own library. -/
def toolchain (name : Name) (kind : Kind) : Decl :=
  { plain name `Init.Core kind [] with inToolchain := true }

/-- The recursion helper of `Good.f`. -/
def helperDecl : Decl :=
  { plain `Good.f._unsafe_rec `Good .definition [`Good.f._unsafe_rec] with isPartial := true }

/-- `Good.f`, the safe base of the helper. -/
def fDecl : Decl := plain `Good.f `Good .definition []

/-- The constants of `base`. -/
def baseDecls : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext], fDecl, helperDecl]

/-- The compliant project. -/
def base : Input where
  profile := .choiceFree
  modules := [`Good]
  decls := baseDecls
  loads := [`Good]

/-- `base` with the constants `extra` added. -/
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
  refine ⟨by decide, ?_, by simp [base], by simp [base]⟩
  intro d hd
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  suffices h : ∀ u ∈ d.uses, u ∈ baseDecls.map (·.name) by
    intro u hu
    obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h u hu)
    exact ⟨d', hd', hn⟩
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [baseDecls, plain, toolchain, helperDecl, fDecl]

/-- From `Good.t`, only `Good.t` and `propext` are reached in `base`. -/
theorem base_reaches_t {e : Name} (h : base.Reaches `Good.t e) : e = `Good.t ∨ e = ``propext := by
  refine reaches_closed (i := base) (fun n => n = `Good.t ∨ n = ``propext) ?_ (Or.inl rfl) h
  intro d hd hS u hu
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl, fDecl] at hS hu ⊢ <;> simp_all

/-- In `base`, the only axiom `Good.t` depends on is `propext`. -/
theorem base_axioms_t {a : Name} (h : base.AxiomOf `Good.t a) : a = ``propext := by
  rcases base_reaches_t h.1 with rfl | rfl
  · obtain ⟨d, hd, hn, hk⟩ := h.2
    simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [plain, toolchain, helperDecl, fDecl] at hn hk
  · rfl

theorem base_known_propext : base.Known ``propext :=
  ⟨by simp [logicalAxioms], toolchain ``propext .axiom, by simp [base, baseDecls], rfl, rfl⟩

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
  refine ⟨hn, ?_, wf_base.claims, wf_base.loaded⟩
  intro d hd u hu
  rcases List.mem_append.mp hd with hd | hd
  · exact resolves_withDecls (wf_base.closed d hd u hu)
  · exact hc d hd u hu

/-- The added constants mention only constants of the result. -/
theorem uses_resolve {extra : List Decl}
    (h : ∀ d ∈ extra, ∀ u ∈ d.uses, u ∈ (base.decls ++ extra).map (·.name)) :
    ∀ d ∈ extra, ∀ u ∈ d.uses, (withDecls extra).Resolves u := by
  intro d hd u hu
  obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h d hd u hu)
  exact ⟨d', hd', hn⟩

/-- The claimed module of `base`, with constants added. -/
theorem claimed_withDecls {extra : List Decl} : (withDecls extra).ClaimedModule `Good := by
  simp [withDecls, base, Input.ClaimedModule]

end Witnesses

end RegulaSpecification
