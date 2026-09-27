/-! Pure scheduling decisions of the rule-example corpus producer window. The corpus
driver (`Regula.Qualification.RuleExamples.check`) launches exactly the jobs these
definitions name, awaits records in `consumed` order, and applies `consume` once per
record. The theorems below are about these exact definitions. They do not describe
Task scheduling, process or filesystem behavior: `IO.asTask`, `IO.wait`, process
reaping and the outer group kill remain trusted runtime and OS mechanisms. -/
namespace RegulaQualification.CorpusWindow

/-- Window state over `total` productions consumed in fixed order: Tasks exist for the
jobs `[0, launched)`, and the records `[0, consumed)` have been taken. -/
structure State where
  width : Nat
  total : Nat
  launched : Nat
  consumed : Nat
  deriving Repr

/-- Before any consumption, the first `min width total` jobs are launched. -/
def init (width total : Nat) : State := ⟨width, total, min width total, 0⟩

/-- The job launched when record `consumed` is taken: `consumed + width`, if in range. -/
def refill (s : State) : Option Nat :=
  if s.consumed + s.width < s.total then some (s.consumed + s.width) else none

/-- Take one record and apply its refill decision. -/
def consume (s : State) : State :=
  { s with consumed := s.consumed + 1,
           launched := if (refill s).isSome then s.launched + 1 else s.launched }

/-- The window invariant: consumption stays in range and the launched prefix is always
exactly `min (consumed + width) total`. -/
def State.Inv (s : State) : Prop :=
  s.consumed ≤ s.total ∧ s.launched = min (s.consumed + s.width) s.total

theorem init_inv (width total : Nat) : (init width total).Inv := by
  simp [init, State.Inv]

theorem consume_inv (s : State) (h : s.Inv) (hc : s.consumed < s.total) : (consume s).Inv := by
  unfold State.Inv consume refill at *
  split <;> simp_all <;> omega

theorem consume_consumed (s : State) : (consume s).consumed = s.consumed + 1 := rfl

theorem consume_width (s : State) : (consume s).width = s.width := rfl

theorem consume_total (s : State) : (consume s).total = s.total := rfl

/-- Width: launched-but-unconsumed Tasks never exceed `width`. -/
theorem launched_le (s : State) (h : s.Inv) : s.launched ≤ s.consumed + s.width := by
  unfold State.Inv at h; omega

/-- The awaited record's Task exists: with a positive width, the next record to consume
was already launched. -/
theorem consumed_lt_launched (s : State) (h : s.Inv) (hw : 0 < s.width)
    (hc : s.consumed < s.total) : s.consumed < s.launched := by
  unfold State.Inv at h; omega

/-- Refill order: a refill launches exactly the next unlaunched job, and it is in range. -/
theorem refill_next (s : State) (h : s.Inv) (j : Nat) (hr : refill s = some j) :
    j = s.launched ∧ j < s.total := by
  unfold refill at hr
  unfold State.Inv at h
  split at hr <;> simp_all <;> omega

/-- Without a refill every job is already launched. -/
theorem refill_none (s : State) (h : s.Inv) (hr : refill s = none) : s.launched = s.total := by
  unfold refill at hr
  unfold State.Inv at h
  split at hr <;> simp_all

/-- After every record is taken, every job was launched, so the consumer has awaited
every launched Task. -/
theorem launched_eq_total (s : State) (h : s.Inv) (hc : s.consumed = s.total) :
    s.launched = s.total := by
  unfold State.Inv at h; omega

/-- The refills issued over `n` consumptions, in order. -/
def refills : Nat → State → List Nat
  | 0, _ => []
  | n + 1, s => (refill s).toList ++ refills n (consume s)

theorem refills_range (n : Nat) (s : State) (h : s.Inv) (hn : s.consumed + n = s.total) :
    refills n s = List.range' s.launched (s.total - s.launched) := by
  induction n generalizing s with
  | zero =>
    unfold State.Inv at h
    have : s.total - s.launched = 0 := by omega
    simp [refills, this]
  | succ n ih =>
    have hc : s.consumed < s.total := by omega
    have hinv := consume_inv s h hc
    have hn' : (consume s).consumed + n = (consume s).total := by
      simp only [consume_consumed, consume_total]; omega
    rw [refills, ih (consume s) hinv hn']
    cases hr : refill s with
    | none =>
      have hl := refill_none s h hr
      simp [consume, hr, hl]
    | some j =>
      obtain ⟨hj, hjt⟩ := refill_next s h j hr
      have hlen : s.total - s.launched = (s.total - (s.launched + 1)) + 1 := by omega
      simp [consume, hr, hj, hlen, List.range'_succ]

/-- Launch order: the initial launches followed by every refill of a complete run name
each job exactly once, in increasing order. Tasks pushed in this order therefore sit at
their job index. -/
theorem launch_order (width total : Nat) :
    List.range (init width total).launched ++ refills total (init width total) =
      List.range total := by
  rw [refills_range total (init width total) (init_inv width total) (by simp [init])]
  simp only [init, List.range_eq_range']
  have split := @List.range'_append_1 0 (min width total) (total - min width total)
  rw [Nat.zero_add] at split
  rw [split]
  congr 1
  omega

/-! Production identities. Each production runs in the fresh workspace named by its
`(rule, phase)` pair; the driver refuses an existing workspace directory. -/

/-- The canonical Fixed and Violation records of the selected rules, in selection order. -/
def records (selected : List String) : List (String × String) :=
  selected.flatMap fun rule => [(rule, "Fixed"), (rule, "Violation")]

/-- The special refusal controls of the selected rules, in their fixed order. -/
def specials (selected : List String) : List (String × String) :=
  (if "RG1005" ∈ selected then [("RG1005", "WrongClaim")] else []) ++
    (if "RG4004" ∈ selected then [("RG4004", "TrustedControl"), ("RG4004", "NegativeControl")]
      else [])

/-- Every production, in pool order: records first, then special controls. -/
def productions (selected : List String) : List (String × String) :=
  records selected ++ specials selected

theorem records_nodup (selected : List String) (h : selected.Nodup) :
    (records selected).Nodup := by
  induction selected with
  | nil => simp [records]
  | cons a t ih =>
    simp only [List.nodup_cons] at h
    simp only [records, List.flatMap_cons, List.cons_append, List.nil_append,
      List.nodup_cons, List.mem_cons, List.mem_flatMap] at ih ⊢
    refine ⟨?_, ?_, ih h.2⟩
    · rintro (hx | ⟨r, hr, hx⟩)
      · simp at hx
      · simp only [Prod.mk.injEq, and_true, String.reduceEq, and_false, List.not_mem_nil,
          or_self, or_false] at hx
        rcases hx with rfl | hx <;> simp_all
    · rintro ⟨r, hr, hx⟩
      simp only [Prod.mk.injEq, String.reduceEq, and_false, and_true, List.not_mem_nil, or_false,
        false_or] at hx
      subst hx
      exact h.1 hr

theorem mem_records_phase (selected : List String) (p : String × String)
    (hp : p ∈ records selected) : p.2 = "Fixed" ∨ p.2 = "Violation" := by
  simp only [records, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨_, _, hp | hp⟩ := hp <;> simp [hp]

theorem mem_specials_phase (selected : List String) (p : String × String)
    (hp : p ∈ specials selected) : p.2 ≠ "Fixed" ∧ p.2 ≠ "Violation" := by
  have hall : (specials selected).all (fun q => q.2 != "Fixed" && q.2 != "Violation") = true := by
    unfold specials
    split <;> split <;> decide
  have := List.all_eq_true.mp hall p hp
  simp_all

theorem specials_nodup (selected : List String) : (specials selected).Nodup := by
  unfold specials
  split <;> split <;> decide

/-- Workspace distinctness: with a duplicate-free selection, no two productions share a
`(rule, phase)` workspace identity. -/
theorem productions_nodup (selected : List String) (h : selected.Nodup) :
    (productions selected).Nodup := by
  unfold productions
  refine List.nodup_append.mpr ⟨records_nodup selected h, specials_nodup selected, ?_⟩
  intro a ha b hb hab
  subst hab
  have := mem_specials_phase selected a hb
  rcases mem_records_phase selected a ha with h' | h' <;> simp_all

end RegulaQualification.CorpusWindow
