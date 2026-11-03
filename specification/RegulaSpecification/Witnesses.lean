import RegulaSpecification.Foundation

/-!
# The compliant project that the cases of each rule extend

For each rule, its module below {lit}`Rules/` gives a small well-formed project that the rule must refuse, built on
the compliant project here ({lit}`base`), and a subject of {lit}`base` that it must admit. With them {name (full := RegulaSpecification.adequate)}`adequate` discharges lean-intent's obligations for the rule's
record, and {name (full := RegulaSpecification.silent_fails)}`silent_fails` and {name (full := RegulaSpecification.noisy_fails)}`noisy_fails` prove that neither the checker that reports nothing nor the one
that reports every candidate meets it. A statement that a do-nothing checker met, or that refused the
compliant case, would fail here.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Witnesses

/-- A safe constant with nothing marked, outside the toolchain. -/
def plain (name module : Name) (kind : Kind) (uses : List Name) : Decl :=
  { name, module, kind, safety := .safe, uses, valueUses := [], implementedBy := none,
    isExtern := false, inToolchain := false }

/-- A constant of the toolchain's own library. -/
def toolchain (name : Name) (kind : Kind) : Decl :=
  { plain name `Init.Core kind [] with inToolchain := true }

/-- A constant of the exempted form beside `Good.f`. -/
def helperDecl : Decl :=
  { plain `Good.f._unsafe_rec `Good .definition [`Good.f._unsafe_rec] with safety := .partial }

/-- `Good.f`, the safe definition beside it. -/
def fDecl : Decl := plain `Good.f `Good .definition []

/-- The constants of {lit}`base`. -/
def baseDecls : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext], fDecl, helperDecl]

/-- The compliant project. -/
def base : Input where
  profile := .choiceFree
  modules := [`Good]
  decls := baseDecls
  unique := by decide

/-- {name}`base` with the constants {name}`extra` added, whose names stay distinct. -/
def withDecls (extra : List Decl) (hn : ((base.decls ++ extra).map (·.name)).Nodup) : Input :=
  { base with decls := base.decls ++ extra, unique := hn }

theorem reaches_closed {i : Input} (S : Name → Prop)
    (h : ∀ d ∈ i.decls, S d.name → ∀ u ∈ d.uses, S u) {c e : Name} (hc : S c)
    (hr : i.Reaches c e) : S e := by
  induction hr with
  | refl => exact hc
  | step d hd hn hu _ ih => exact ih (h d hd (hn ▸ hc) _ hu)

theorem wf_base : base.WellFormed := by
  refine ⟨?_, by simp [base]⟩
  intro d hd
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  suffices h : ∀ u ∈ d.uses, u ∈ baseDecls.map (·.name) by
    intro u hu
    obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h u hu)
    exact ⟨d', hd', hn⟩
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [baseDecls, plain, toolchain, helperDecl, fDecl]

theorem base_reaches_t {e : Name} (h : base.Reaches `Good.t e) : e = `Good.t ∨ e = ``propext := by
  refine reaches_closed (i := base) (fun n => n = `Good.t ∨ n = ``propext) ?_ (Or.inl rfl) h
  intro d hd hS u hu
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp_all [plain, toolchain, helperDecl, fDecl]

theorem base_axioms_t {a : Name} (h : base.AxiomOf `Good.t a) : a = ``propext := by
  rcases base_reaches_t h.1 with rfl | rfl
  · obtain ⟨d, hd, hn, hk⟩ := h.2
    simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [plain, toolchain, helperDecl, fDecl] at hn hk
  · rfl

theorem base_known_propext : base.Known ``propext :=
  ⟨by simp [logicalAxioms], toolchain ``propext .axiom, by simp [base, baseDecls], rfl, rfl⟩

theorem resolves_withDecls {extra : List Decl} {hn : ((base.decls ++ extra).map (·.name)).Nodup}
    {u : Name} (h : base.Resolves u) : (withDecls extra hn).Resolves u := by
  obtain ⟨d, hd, hn⟩ := h
  exact ⟨d, List.mem_append_left _ hd, hn⟩

theorem wf_withDecls (extra : List Decl) (hn : ((base.decls ++ extra).map (·.name)).Nodup)
    (hc : ∀ d ∈ extra, ∀ u ∈ d.uses, (withDecls extra hn).Resolves u) :
    (withDecls extra hn).WellFormed := by
  refine ⟨?_, wf_base.claims⟩
  intro d hd u hu
  rcases List.mem_append.mp hd with hd | hd
  · exact resolves_withDecls (wf_base.closed d hd u hu)
  · exact hc d hd u hu

theorem uses_resolve {extra : List Decl} {hn : ((base.decls ++ extra).map (·.name)).Nodup}
    (h : ∀ d ∈ extra, ∀ u ∈ d.uses, u ∈ (base.decls ++ extra).map (·.name)) :
    ∀ d ∈ extra, ∀ u ∈ d.uses, (withDecls extra hn).Resolves u := by
  intro d hd u hu
  obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h d hd u hu)
  exact ⟨d', hd', hn⟩

theorem claimed_withDecls {extra : List Decl} {hn : ((base.decls ++ extra).map (·.name)).Nodup} :
    (withDecls extra hn).ClaimedModule `Good := by
  simp [withDecls, base, Input.ClaimedModule]

theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · rw [ex, ey]
    · exact absurd (List.mem_map.mpr ⟨y, hy', by rw [← hxy, ex]⟩) h.1
    · exact absurd (List.mem_map.mpr ⟨x, hx', by rw [hxy, ey]⟩) h.1
    · exact eq_of_mem_of_nodup_map h.2 hx' hy' hxy

theorem eq_of_name {i : Input} {d d' : Decl} (hd : d ∈ i.decls)
    (hd' : d' ∈ i.decls) (h : d.name = d'.name) : d = d' :=
  eq_of_mem_of_nodup_map i.unique hd hd' h

theorem name_mem {i : Input} {c : Name} {P : Decl → Prop} (h : ∃ d ∈ i.decls, d.name = c ∧ P d) :
    c ∈ i.decls.map (·.name) := by
  obtain ⟨d, hd, rfl, -⟩ := h
  exact List.mem_map_of_mem hd

/-- The theorem `Good.t` of {name}`base`. -/
def tDecl : Decl := plain `Good.t `Good .theorem [``propext]

theorem t_mem : tDecl ∈ base.decls := by simp [tDecl, base, baseDecls]

theorem t_of_name {d : Decl} (hd : d ∈ base.decls) (hn : d.name = `Good.t) : d = tDecl :=
  eq_of_name hd t_mem (by simp [hn, tDecl, plain])

theorem t_mem_support : `Good.t ∈ base.decls.map (·.name) := List.mem_map_of_mem t_mem

theorem not_native_of_components {a : Name} (h : components a < 3) : ¬ NativeProofAxiom a :=
  fun hn => absurd (components_of_native hn) (by omega)

theorem not_known_of_not_logical {i : Input} {a : Name} (h : a ∉ logicalAxioms) : ¬ i.Known a :=
  fun hk => h hk.1

end Witnesses

end RegulaSpecification
