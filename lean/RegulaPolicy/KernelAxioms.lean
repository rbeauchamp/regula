module

public import Lean.Util.FoldConsts
public import Lean.Util.CollectAxioms
public import Lean.OriginalConstKind
public import Std.Data.HashMap.Lemmas
public import Std.Data.HashSet.Lemmas

/-! # Axioms reached in a kernel environment

The axioms a declaration rests on, computed from the constants of a kernel environment alone: the
names its type and value reach, through the types and values of the constants they use, that the
environment holds as axioms (`ReachesAxiom`). `axiomTable` computes them in a kernel environment
from its constants alone, never from the axiom table `exportedAxiomsExt` that Lean's
`collectAxioms` reads first for an imported name.

A search of a graph of names (`search`) underlies both computations here: `axiomTable`, one backward
search from each axiom that a forward search from every requested name (`searchEdges`) found, for
all the names of their closure in one environment, and `axiomsWith`, a search from one name that
stops at the names of such a table. `axiomTable_some` and `axiomsWith_some` state that each returns
exactly the axioms `ReachesAxiom` relates to a name. `reachedAxioms` and `reachedAxiomTable` read
the axioms of names in an environment with no replayed kernel, such as the editor's, by the same
searches (`axiomsThrough_some`, `axiomTableThrough_some`), taking Lean's table only for a name
whose body the module system hid; a table search can stop at the imported names whose axioms an
earlier one computed (`MemoInv`, `tableThrough_agree`). Each search is bounded by its fuel: a
search that runs out returns `none`, and the caller refuses.

A step follows `ConstantInfo.getUsedConstantsAsSet`: the constants of the type and the value,
the constructors of an inductive type, the inductive types of a recursor. Each step that Lean's
`collectAxioms` takes from a constant is one of these, so on the same constants every axiom it
reports is reached here too. -/

@[expose] public section

namespace RegulaPolicy.KernelAxioms
open Lean

/-! ## Searching a graph of names -/

/-- Push `m` onto the pending names unless it was seen before. -/
def pushNew (acc : List Name × Std.HashSet Name) (m : Name) : List Name × Std.HashSet Name :=
  if acc.2.contains m then acc else (m :: acc.1, acc.2.insert m)

/-- `pushNew` leaves a seen name's state unchanged. -/
theorem pushNew_seen {p : List Name} {s : Std.HashSet Name} {m : Name}
    (h : s.contains m = true) : pushNew (p, s) m = (p, s) := by
  simp [pushNew, h]

/-- `pushNew` pushes and records an unseen name. -/
theorem pushNew_unseen {p : List Name} {s : Std.HashSet Name} {m : Name}
    (h : ¬ s.contains m = true) : pushNew (p, s) m = (m :: p, s.insert m) := by
  simp [pushNew, h]

/-- What folding `pushNew` over `names` does to the pending names `p` and the seen names `s`. -/
theorem foldl_pushNew (names p : List Name) (s : Std.HashSet Name) :
    (∀ x, x ∈ (names.foldl pushNew (p, s)).2 ↔ x ∈ s ∨ x ∈ names) ∧
    (∀ x ∈ (names.foldl pushNew (p, s)).1, x ∈ p ∨ x ∈ names) ∧
    (∀ x ∈ p, x ∈ (names.foldl pushNew (p, s)).1) ∧
    (∀ x ∈ (names.foldl pushNew (p, s)).2, x ∈ s ∨ x ∈ (names.foldl pushNew (p, s)).1) := by
  induction names generalizing p s with
  | nil => exact ⟨by simp, by simp, by simp, fun x hx => .inl hx⟩
  | cons m names ih =>
    simp only [List.foldl_cons]
    by_cases hm : s.contains m
    · rw [pushNew_seen hm]
      obtain ⟨h1, h2, h3, h4⟩ := ih p s
      have hms : m ∈ s := Std.HashSet.mem_iff_contains.mpr hm
      refine ⟨fun x => ?_, fun x hx => ?_, h3, h4⟩
      · rw [h1 x, List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl hx
          · exact .inl hms
          · exact .inr hx
      · rcases h2 x hx with hx | hx
        · exact .inl hx
        · exact .inr (List.mem_cons_of_mem _ hx)
    · rw [pushNew_unseen hm]
      obtain ⟨h1, h2, h3, h4⟩ := ih (m :: p) (s.insert m)
      refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => h3 x (List.mem_cons_of_mem _ hx),
        fun x hx => ?_⟩
      · rw [h1 x, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
        constructor
        · rintro ((rfl | hx) | hx)
          · exact .inr (.inl rfl)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl (.inr hx)
          · exact .inl (.inl rfl)
          · exact .inr hx
      · rcases h2 x hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inr List.mem_cons_self
          · exact .inl hx
        · exact .inr (List.mem_cons_of_mem _ hx)
      · rcases h4 x hx with hx | hx
        · rcases Std.HashSet.mem_insert.mp hx with hx | hx
          · rw [← beq_iff_eq.mp hx]
            exact .inr (h3 m List.mem_cons_self)
          · exact .inl hx
        · exact .inr hx

/-- `x` is reachable from `n` along `next`, in zero or more steps. -/
inductive Reach (next : Name → Array Name) : Name → Name → Prop
  /-- Every name reaches itself. -/
  | refl (n : Name) : Reach next n n
  /-- A name reaches whatever a name after it reaches. -/
  | step {n m x : Name} : m ∈ next n → Reach next m x → Reach next n x

/-- Reachability extends by one more step. -/
theorem Reach.tail {next : Name → Array Name} {n x y : Name} (h : Reach next n x)
    (hy : y ∈ next x) : Reach next n y := by
  induction h with
  | refl => exact .step hy (.refl y)
  | step hm _ ih => exact .step hm (ih hy)

/-- Reachability is transitive. -/
theorem Reach.trans {next : Name → Array Name} {n m x : Name} (h : Reach next n m)
    (h' : Reach next m x) : Reach next n x := by
  induction h with
  | refl => exact h'
  | step hm _ ih => exact .step hm (ih h')

/-- Expand the `pending` names, recording in `seen` every name ever pushed, and in `edges` each
expanded name with the names after it. It returns the seen names and the edges once nothing is
pending, or `none` when `fuel` runs out first. -/
def searchLoop (next : Name → Array Name) :
    Nat → List Name → Std.HashSet Name → List (Name × Array Name) →
      Option (Std.HashSet Name × List (Name × Array Name))
  | _, [], seen, edges => some (seen, edges)
  | 0, _ :: _, _, _ => none
  | fuel + 1, n :: rest, seen, edges =>
    let after := next n
    let pushed := after.toList.foldl pushNew (rest, seen)
    searchLoop next fuel pushed.1 pushed.2 ((n, after) :: edges)

/-- Every name reachable along `next` from a name of `start`, with each such name and the names
after it, within `fuel` expansions, or `none` when the fuel runs out. -/
def searchEdges (next : Name → Array Name) (fuel : Nat) (start : List Name) :
    Option (Std.HashSet Name × List (Name × Array Name)) :=
  let first := start.foldl pushNew ([], {})
  searchLoop next fuel first.1 first.2 []

/-- Every name reachable along `next` from a name of `start`, within `fuel` expansions, or
`none` when the fuel runs out. -/
def search (next : Name → Array Name) (fuel : Nat) (start : List Name) :
    Option (Std.HashSet Name) :=
  (searchEdges next fuel start).map (·.1)

/-- The loop invariant: pending names were seen; every seen name is pending or has an edge; every
edge is of a seen name that is not pending, with the names after it, all seen; and every seen name
is reachable from a name of `start`. -/
private def LoopInv (next : Name → Array Name) (start : List Name) (pending : List Name)
    (seen : Std.HashSet Name) (edges : List (Name × Array Name)) : Prop :=
  (∀ x ∈ pending, x ∈ seen) ∧
    (∀ x ∈ seen, x ∈ pending ∨ ∃ e ∈ edges, e.1 = x) ∧
    (∀ e ∈ edges, e.2 = next e.1 ∧ ∀ m ∈ e.2, m ∈ seen) ∧
    ∀ x ∈ seen, ∃ s ∈ start, Reach next s x

/-- A loop that returns from an invariant state returns a set holding every seen name and only
names reachable from `start`, and edges that give each name of the set the names after it, all in
the set. -/
private theorem searchLoop_some {next : Name → Array Name} {start : List Name} :
    ∀ (fuel : Nat) (pending : List Name) (seen : Std.HashSet Name)
      (edges : List (Name × Array Name)) (result : Std.HashSet Name)
      (resultEdges : List (Name × Array Name)),
      LoopInv next start pending seen edges →
      searchLoop next fuel pending seen edges = some (result, resultEdges) →
      (∀ x ∈ seen, x ∈ result) ∧ (∀ x ∈ result, ∃ e ∈ resultEdges, e.1 = x) ∧
        (∀ e ∈ resultEdges, e.2 = next e.1 ∧ ∀ m ∈ e.2, m ∈ result) ∧
        ∀ x ∈ result, ∃ s ∈ start, Reach next s x := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending seen edges result resultEdges hinv h
    cases pending with
    | nil =>
      simp only [searchLoop, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun _ hx => hx, fun x hx => ?_, hinv.2.2.1, hinv.2.2.2⟩
      rcases hinv.2.1 x hx with hx | hx
      · simp at hx
      · exact hx
    | cons n rest => simp [searchLoop] at h
  | succ fuel ih =>
    intro pending seen edges result resultEdges hinv h
    cases pending with
    | nil =>
      simp only [searchLoop, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun _ hx => hx, fun x hx => ?_, hinv.2.2.1, hinv.2.2.2⟩
      rcases hinv.2.1 x hx with hx | hx
      · simp at hx
      · exact hx
    | cons n rest =>
      simp only [searchLoop] at h
      obtain ⟨f1, f2, f3, f4⟩ := foldl_pushNew (next n).toList rest seen
      have hn : n ∈ seen := hinv.1 n List.mem_cons_self
      obtain ⟨s₀, hs₀, hreach⟩ := hinv.2.2.2 n hn
      have inv : LoopInv next start ((next n).toList.foldl pushNew (rest, seen)).1
          ((next n).toList.foldl pushNew (rest, seen)).2 ((n, next n) :: edges) := by
        refine ⟨fun x hx => ?_, fun x hx => ?_, fun e he => ?_, fun x hx => ?_⟩
        · rcases f2 x hx with hx | hx
          · exact (f1 x).mpr (.inl (hinv.1 x (List.mem_cons_of_mem _ hx)))
          · exact (f1 x).mpr (.inr hx)
        · rcases f4 x hx with hx | hx
          · rcases hinv.2.1 x hx with hp | ⟨e, he, hex⟩
            · rcases List.mem_cons.mp hp with rfl | hp
              · exact .inr ⟨(x, next x), List.mem_cons_self, rfl⟩
              · exact .inl (f3 x hp)
            · exact .inr ⟨e, List.mem_cons_of_mem _ he, hex⟩
          · exact .inl hx
        · rcases List.mem_cons.mp he with rfl | he
          · exact ⟨rfl, fun m hm => (f1 m).mpr (.inr (Array.mem_toList_iff.mpr hm))⟩
          · obtain ⟨hnext, hseen⟩ := hinv.2.2.1 e he
            exact ⟨hnext, fun m hm => (f1 m).mpr (.inl (hseen m hm))⟩
        · rcases (f1 x).mp hx with hx | hx
          · exact hinv.2.2.2 x hx
          · exact ⟨s₀, hs₀, hreach.tail (Array.mem_toList_iff.mp hx)⟩
      obtain ⟨r1, r2, r3, r4⟩ := ih _ _ _ result resultEdges inv h
      exact ⟨fun x hx => r1 x ((f1 x).mpr (.inl hx)), r2, r3, r4⟩

/-- **A completed `searchEdges` holds exactly the names reachable from `start`**, and its edges
give each of them the names after it. -/
theorem searchEdges_some {next : Name → Array Name} {fuel : Nat} {start : List Name}
    {result : Std.HashSet Name} {edges : List (Name × Array Name)}
    (h : searchEdges next fuel start = some (result, edges)) :
    (∀ s ∈ start, ∀ x, Reach next s x → x ∈ result) ∧
      (∀ x ∈ result, ∃ s ∈ start, Reach next s x) ∧
      (∀ x ∈ result, ∃ e ∈ edges, e.1 = x) ∧ ∀ e ∈ edges, e.2 = next e.1 := by
  obtain ⟨f1, f2, -, f4⟩ := foldl_pushNew start [] {}
  have inv : LoopInv next start (start.foldl pushNew ([], {})).1
      (start.foldl pushNew ([], {})).2 [] := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun e he => by simp at he, fun x hx => ?_⟩
    · rcases f2 x hx with hx | hx
      · simp at hx
      · exact (f1 x).mpr (.inr hx)
    · rcases f4 x hx with hx | hx
      · simp at hx
      · exact .inl hx
    · rcases (f1 x).mp hx with hx | hx
      · simp at hx
      · exact ⟨x, hx, .refl x⟩
  obtain ⟨contains, hasEdge, edgeOK, sound⟩ := searchLoop_some fuel _ _ [] result edges inv h
  have closed : ∀ x ∈ result, ∀ m ∈ next x, m ∈ result := by
    intro x hx m hm
    obtain ⟨e, he, rfl⟩ := hasEdge x hx
    obtain ⟨hnext, hall⟩ := edgeOK e he
    exact hall m (hnext ▸ hm)
  refine ⟨fun s hs x hx => ?_, sound, hasEdge, fun e he => (edgeOK e he).1⟩
  have hs' : s ∈ result := contains s ((f1 s).mpr (.inr hs))
  clear hs
  induction hx with
  | refl => exact hs'
  | step hm _ ih => exact ih (closed _ hs' _ hm)

/-- **A completed `search` holds exactly the names reachable from `start`:** every such name is
in it, and every name in it is such a name. -/
theorem search_some {next : Name → Array Name} {fuel : Nat} {start : List Name}
    {result : Std.HashSet Name} (h : search next fuel start = some result) :
    (∀ s ∈ start, ∀ x, Reach next s x → x ∈ result) ∧
      ∀ x ∈ result, ∃ s ∈ start, Reach next s x := by
  unfold search at h
  cases he : searchEdges next fuel start with
  | none => simp [he] at h
  | some found =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨complete, sound, -, -⟩ := searchEdges_some (result := found.1) (edges := found.2) he
    exact ⟨complete, sound⟩

/-- What a search may still expand: its pending names and the entries of `bound` it has not
seen. -/
private def remaining (bound pending : List Name) (seen : Std.HashSet Name) : Nat :=
  pending.length + bound.countP fun x => !seen.contains x

/-- Pushing a name of `bound` never increases `remaining`: an unseen name adds one pending name
and removes at least its own entry from the unseen ones. -/
private theorem remaining_pushNew {bound p : List Name} {s : Std.HashSet Name} {m : Name}
    (hm : m ∈ bound) :
    remaining bound (pushNew (p, s) m).1 (pushNew (p, s) m).2 ≤ remaining bound p s := by
  by_cases hs : s.contains m
  · rw [pushNew_seen hs]
    exact Nat.le_refl _
  · rw [pushNew_unseen hs]
    have fewer : ∀ l : List Name, m ∈ l →
        (l.countP fun x => !(s.insert m).contains x) + 1 ≤ l.countP fun x => !s.contains x := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        intro hl
        simp only [List.countP_cons, Std.HashSet.contains_insert]
        by_cases ha : a = m
        · subst ha
          have le : (l.countP fun x => !(a == x || s.contains x)) ≤
              l.countP fun x => !s.contains x :=
            List.countP_mono_left fun x _ h => by simp_all
          simp only [beq_self_eq_true, Bool.true_or, Bool.not_true, hs, Bool.not_false]
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          exact Nat.succ_le_succ le
        · have hl' : m ∈ l := (List.mem_cons.mp hl).resolve_left (Ne.symm ha)
          have hne : (m == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm ha)
          simp only [hne, Bool.false_or]
          have := ih hl'
          simp only [Std.HashSet.contains_insert] at this
          split <;> omega
    have := fewer bound hm
    unfold remaining
    simp only [List.length_cons]
    omega

/-- Folding `pushNew` over names of `bound` never increases `remaining`. -/
private theorem remaining_foldl_pushNew {bound : List Name} :
    ∀ (names p : List Name) (s : Std.HashSet Name), (∀ m ∈ names, m ∈ bound) →
      remaining bound (names.foldl pushNew (p, s)).1 (names.foldl pushNew (p, s)).2 ≤
        remaining bound p s := by
  intro names
  induction names with
  | nil => intro p s _; exact Nat.le_refl _
  | cons m names ih =>
    intro p s hnames
    simp only [List.foldl_cons]
    have step := remaining_pushNew (p := p) (s := s) (hnames m List.mem_cons_self)
    have rest := ih (pushNew (p, s) m).1 (pushNew (p, s) m).2
      (fun x hx => hnames x (List.mem_cons_of_mem _ hx))
    exact Nat.le_trans rest step

/-- A loop whose seen names lie in `bound`, which `next` keeps within, completes when its fuel
is at least what it may still expand (`remaining`). -/
private theorem searchLoop_isSome {next : Name → Array Name} {bound : List Name}
    (closed : ∀ x ∈ bound, ∀ y ∈ next x, y ∈ bound) :
    ∀ (fuel : Nat) (pending : List Name) (seen : Std.HashSet Name)
      (edges : List (Name × Array Name)), (∀ x ∈ pending, x ∈ seen) →
      (∀ x ∈ seen, x ∈ bound) → remaining bound pending seen ≤ fuel →
      (searchLoop next fuel pending seen edges).isSome := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending seen edges _ _ hfuel
    cases pending with
    | nil => simp [searchLoop]
    | cons n rest => simp [remaining] at hfuel
  | succ fuel ih =>
    intro pending seen edges hpending hseen hfuel
    cases pending with
    | nil => simp [searchLoop]
    | cons n rest =>
      simp only [searchLoop]
      have hn : n ∈ bound := hseen n (hpending n List.mem_cons_self)
      have hnext : ∀ m ∈ (next n).toList, m ∈ bound :=
        fun m hm => closed n hn m (Array.mem_toList_iff.mp hm)
      obtain ⟨f1, f2, -, -⟩ := foldl_pushNew (next n).toList rest seen
      refine ih _ _ _ (fun x hx => ?_) (fun x hx => ?_) ?_
      · rcases f2 x hx with hx | hx
        · exact (f1 x).mpr (.inl (hpending x (List.mem_cons_of_mem _ hx)))
        · exact (f1 x).mpr (.inr hx)
      · rcases (f1 x).mp hx with hx | hx
        · exact hseen x hx
        · exact hnext x hx
      · have := remaining_foldl_pushNew (next n).toList rest seen hnext
        simp only [remaining, List.length_cons] at hfuel this ⊢
        omega

/-- **A search completes when every name it can meet lies in `bound` and its fuel is at least
the length of `bound`:** every name of `start` is in `bound`, and `next` keeps within it. So
`search_some` then describes its result with no condition on the fuel. -/
theorem search_isSome {next : Name → Array Name} {bound : List Name} {fuel : Nat}
    {start : List Name} (hstart : ∀ s ∈ start, s ∈ bound)
    (closed : ∀ x ∈ bound, ∀ y ∈ next x, y ∈ bound) (hfuel : bound.length ≤ fuel) :
    (search next fuel start).isSome := by
  unfold search searchEdges
  obtain ⟨f1, f2, -, -⟩ := foldl_pushNew start [] {}
  have initial := remaining_foldl_pushNew start [] {} hstart
  have empty : remaining bound [] {} = bound.length := by
    simp [remaining]
  rw [Option.isSome_map]
  refine searchLoop_isSome closed fuel _ _ [] (fun x hx => ?_) (fun x hx => ?_) ?_
  · rcases f2 x hx with hx | hx
    · simp at hx
    · exact (f1 x).mpr (.inr hx)
  · rcases (f1 x).mp hx with hx | hx
    · simp at hx
    · exact hstart x hx
  · omega

/-! ## The constants of a kernel environment -/

/-- The constants the type and value of `info` use (`ConstantInfo.getUsedConstantsAsSet`), with
the constructors of an inductive type and the inductive types of a recursor. -/
def successorsOf (info : ConstantInfo) : Array Name :=
  Std.TreeSet.toArray info.getUsedConstantsAsSet

/-- The constants the constant `find` holds under `n` uses, or none when it holds none. -/
def successors (find : Name → Option ConstantInfo) (n : Name) : Array Name :=
  match find n with
  | some info => successorsOf info
  | none => #[]

/-- Every name reachable from the constants `start` uses, within `fuel` expansions, or `none`
when the fuel runs out. -/
def reachSet (find : Name → Option ConstantInfo) (fuel : Nat) (start : ConstantInfo) :
    Option (Std.HashSet Name) :=
  search (successors find) fuel (successorsOf start).toList

/-- A completed `reachSet` holds exactly the names reachable from the constants `start` uses:
every such name is in it, and every name in it is such a name. -/
theorem reachSet_some {find : Name → Option ConstantInfo} {fuel : Nat} {start : ConstantInfo}
    {result : Std.HashSet Name} (h : reachSet find fuel start = some result) :
    (∀ m ∈ successorsOf start, ∀ x, Reach (successors find) m x → x ∈ result) ∧
      ∀ x ∈ result, ∃ m ∈ successorsOf start, Reach (successors find) m x := by
  obtain ⟨complete, sound⟩ := search_some h
  exact ⟨fun m hm => complete m (Array.mem_toList_iff.mpr hm),
    fun x hx => (sound x hx).elim fun m ⟨hm, hr⟩ => ⟨m, Array.mem_toList_iff.mp hm, hr⟩⟩

/-- Whether `find` holds an axiom under `n`. -/
def isAxiomIn (find : Name → Option ConstantInfo) (n : Name) : Bool :=
  match find n with
  | some (.axiomInfo _) => true
  | _ => false

/-- `find` holds an axiom under `n`, as a proposition. `isAxiomIn` decides it
(`isAxiomIn_iff`). -/
def IsAxiomIn (find : Name → Option ConstantInfo) (n : Name) : Prop :=
  ∃ value, find n = some (.axiomInfo value)

/-- The executed test accepts exactly the names that `find` holds as axioms. -/
theorem isAxiomIn_iff (find : Name → Option ConstantInfo) (n : Name) :
    isAxiomIn find n = true ↔ IsAxiomIn find n := by
  unfold isAxiomIn IsAxiomIn
  split <;> simp_all

/-! ## The axioms a name reaches -/

/-- `n` rests on the axiom `a` in `find`: `a` is reachable from `n` through the types and values
of the constants used (`successors`), `n` itself included, and `find` holds an axiom under `a`. -/
def ReachesAxiom (find : Name → Option ConstantInfo) (n a : Name) : Prop :=
  Reach (successors find) n a ∧ IsAxiomIn find a

/-- Each name of `edges` under each name after it: the names before each name. -/
def predecessors (edges : List (Name × Array Name)) : Std.HashMap Name (List Name) :=
  edges.foldl (init := {}) fun preds edge =>
    edge.2.toList.foldl (init := preds) fun preds y => preds.insert y (edge.1 :: preds.getD y [])

/-- What folding the names after one name `x` adds to the names before each name. -/
private theorem mem_insertAfter (x : Name) (ys : List Name) (init : Std.HashMap Name (List Name))
    (y z : Name) :
    z ∈ (ys.foldl (init := init) fun preds y => preds.insert y (x :: preds.getD y [])).getD y [] ↔
      z ∈ init.getD y [] ∨ (z = x ∧ y ∈ ys) := by
  induction ys generalizing init with
  | nil => simp
  | cons w ys ih =>
    simp only [List.foldl_cons]
    rw [ih, Std.HashMap.getD_insert]
    by_cases hw : w = y
    · subst hw
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, true_or, and_true]
      constructor
      · rintro ((h | h) | ⟨h, -⟩)
        · exact .inr h
        · exact .inl h
        · exact .inr h
      · rintro (h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h)
    · have : (w == y) = false := beq_false_of_ne hw
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact .inl h
        · exact .inr ⟨rfl, .inr h⟩
      · rintro (h | ⟨rfl, rfl | h⟩)
        · exact .inl h
        · exact absurd rfl hw
        · exact .inr ⟨rfl, h⟩

/-- A name is before `y` exactly when it is the first name of an edge that has `y` after it. -/
theorem mem_predecessors (edges : List (Name × Array Name)) (y z : Name) :
    z ∈ (predecessors edges).getD y [] ↔ ∃ e ∈ edges, e.1 = z ∧ y ∈ e.2 := by
  suffices ∀ (init : Std.HashMap Name (List Name)),
      z ∈ (edges.foldl (init := init) fun preds edge =>
        edge.2.toList.foldl (init := preds)
          fun preds y => preds.insert y (edge.1 :: preds.getD y [])).getD y [] ↔
        z ∈ init.getD y [] ∨ ∃ e ∈ edges, e.1 = z ∧ y ∈ e.2 by
    rw [predecessors, this]
    simp
  intro init
  induction edges generalizing init with
  | nil => simp
  | cons edge edges ih =>
    simp only [List.foldl_cons]
    rw [ih, mem_insertAfter]
    simp only [Array.mem_toList_iff]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨e, he, rfl, h⟩)
      · exact .inl h
      · exact .inr ⟨edge, List.mem_cons_self, rfl, h⟩
      · exact .inr ⟨e, List.mem_cons_of_mem _ he, rfl, h⟩
    · rintro (h | ⟨e, he, rfl, h⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.mp he with rfl | he
        · exact .inl (.inr ⟨rfl, h⟩)
        · exact .inr ⟨e, he, rfl, h⟩

/-- Search back from each axiom of `axioms` along `back`: each axiom with the names that reach it,
or `none` when a search runs out of fuel. -/
def searchBack (back : Name → Array Name) (fuel : Nat) :
    List Name → Option (List (Name × Std.HashSet Name))
  | [] => some []
  | a :: rest => do
    let reaching ← search back fuel [a]
    return (a, reaching) :: (← searchBack back fuel rest)

/-- Each axiom of a completed `searchBack` has an entry with exactly what its search returned,
and every entry is one of these. -/
theorem searchBack_some {back : Name → Array Name} {fuel : Nat} :
    ∀ {axioms : List Name} {found : List (Name × Std.HashSet Name)},
      searchBack back fuel axioms = some found →
      (∀ a ∈ axioms, ∃ reaching, (a, reaching) ∈ found ∧ search back fuel [a] = some reaching) ∧
        ∀ entry ∈ found, entry.1 ∈ axioms ∧ search back fuel [entry.1] = some entry.2
  | [], found, h => by
    simp only [searchBack, Option.some.injEq] at h
    subst h
    simp
  | a :: rest, found, h => by
    simp only [searchBack, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨reaching, hr, tail, ht, rfl⟩ := h
    obtain ⟨tailAll, tailSound⟩ := searchBack_some ht
    refine ⟨fun b hb => ?_, fun entry he => ?_⟩
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨reaching, List.mem_cons_self, hr⟩
      · obtain ⟨r, hmem, hs⟩ := tailAll b hb
        exact ⟨r, List.mem_cons_of_mem _ hmem, hs⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨List.mem_cons_self, hr⟩
      · obtain ⟨hmem, hs⟩ := tailSound entry he
        exact ⟨List.mem_cons_of_mem _ hmem, hs⟩

/-- The axioms `n` reaches, read from the backward searches `found`: each axiom whose search
reached `n`. -/
def reachedFrom (found : List (Name × Std.HashSet Name)) (n : Name) : Array Name :=
  (found.filterMap fun (a, reaching) => if reaching.contains n then some a else none).toArray

/-- The leaves that each name of a completed forward search `forward` (`searchEdges`) reaches,
under that name, where a leaf is a name that `leaf` accepts: one search back from each leaf the
forward search found, along the edges it recorded, so the names after each name are computed once,
by the forward search, whatever the leaves. The table holds every name the forward search reached.
`none` when a search back runs out of `fuel`. `axiomTable` is this table with the axioms of a
kernel environment as the leaves. -/
def leafTable (leaf : Name → Bool) (fuel : Nat)
    (forward : Std.HashSet Name × List (Name × Array Name)) :
    Option (Std.HashMap Name (Array Name)) := do
  let (seen, edges) := forward
  let preds := predecessors edges
  let found ← searchBack (fun y => (preds.getD y []).toArray) fuel (seen.toList.filter leaf)
  return seen.toList.foldl (init := {}) fun table n => table.insert n (reachedFrom found n)

/-- Folding `insert m (f m)` over `names` gives each name of `names` `f` of it, and leaves every
other name as `init` has it. -/
private theorem foldl_insert_getElem? (f : Name → Array Name) :
    ∀ (names : List Name) (init : Std.HashMap Name (Array Name)) (n : Name),
      (names.foldl (init := init) fun table m => table.insert m (f m))[n]? =
        if n ∈ names then some (f n) else init[n]? := by
  intro names
  induction names with
  | nil => simp
  | cons m rest ih =>
    intro init n
    simp only [List.foldl_cons]
    rw [ih, Std.HashMap.getElem?_insert]
    by_cases hr : n ∈ rest
    · simp [hr]
    · by_cases hm : m = n
      · subst hm
        simp [hr]
      · have : (m == n) = false := beq_false_of_ne hm
        simp [hr, this, List.mem_cons, Ne.symm hm]

/-- A name reached from a name of the set `nodes`, along the names after each name in it, is in
it, and the reversed path runs along `back`, which has every name of `nodes` before each name
after it. -/
private theorem reach_back {next back : Name → Array Name} {nodes : Std.HashSet Name}
    (closed : ∀ x ∈ nodes, ∀ y ∈ next x, y ∈ nodes)
    (before : ∀ x ∈ nodes, ∀ y ∈ next x, x ∈ back y) {x a : Name} (hx : x ∈ nodes)
    (h : Reach next x a) : Reach back a x := by
  induction h with
  | refl => exact .refl _
  | step hm _ ih => exact (ih (closed _ hx _ hm)).tail (before _ hx _ hm)

/-- A path along `back`, which has a name before `y` only when `y` is after it along `next`, is a
reversed path along `next`. -/
private theorem reach_forward {next back : Name → Array Name}
    (after : ∀ x y, x ∈ back y → y ∈ next x) {a x : Name} (h : Reach back a x) :
    Reach next x a := by
  induction h with
  | refl => exact .refl _
  | step hm _ ih => exact ih.tail (after _ _ hm)

/-- **Along the edges a completed `searchEdges` recorded, read backward (`predecessors`), a name
`a` reaches a name `x` the search reached exactly when `x` reaches `a` along `next`.** -/
theorem reach_predecessors_iff {next : Name → Array Name} {fuel : Nat} {start : List Name}
    {seen : Std.HashSet Name} {edges : List (Name × Array Name)}
    (hs : searchEdges next fuel start = some (seen, edges)) {x a : Name} (hx : x ∈ seen) :
    Reach (fun y => ((predecessors edges).getD y []).toArray) a x ↔ Reach next x a := by
  obtain ⟨complete, sound, hasEdge, edgeOK⟩ := searchEdges_some hs
  have after : ∀ x y, x ∈ ((predecessors edges).getD y []).toArray → y ∈ next x := by
    intro x y hx
    simp only [List.mem_toArray, mem_predecessors] at hx
    obtain ⟨e, he, rfl, hy⟩ := hx
    rwa [edgeOK e he] at hy
  have before : ∀ x ∈ seen, ∀ y ∈ next x, x ∈ ((predecessors edges).getD y []).toArray := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := hasEdge x hx
    simp only [List.mem_toArray, mem_predecessors]
    exact ⟨e, he, rfl, (edgeOK e he) ▸ hy⟩
  have closed : ∀ x ∈ seen, ∀ y ∈ next x, y ∈ seen := by
    intro x hx y hy
    obtain ⟨s, hs, hr⟩ := sound x hx
    exact complete s hs y (hr.tail hy)
  exact ⟨reach_forward after, reach_back closed before hx⟩

/-- **`leafTable` of the forward search from `roots` along `next` holds each name of `roots`, and
gives each name it holds exactly the leaves that name reaches along `next`.** -/
theorem leafTable_some {next : Name → Array Name} {leaf : Name → Bool} {fuel : Nat}
    {roots : Array Name} {forward : Std.HashSet Name × List (Name × Array Name)}
    {table : Std.HashMap Name (Array Name)}
    (hs : searchEdges next fuel roots.toList = some forward)
    (h : leafTable leaf fuel forward = some table) :
    (∀ n ∈ roots, ∃ leaves, table[n]? = some leaves) ∧
      ∀ n leaves, table[n]? = some leaves → ∀ a, a ∈ leaves ↔ Reach next n a ∧ leaf a = true := by
  obtain ⟨seen, edges⟩ := forward
  unfold leafTable at h
  obtain ⟨complete, sound, hasEdge, edgeOK⟩ := searchEdges_some hs
  let back := fun y => ((predecessors edges).getD y []).toArray
  cases hb : searchBack back fuel (seen.toList.filter leaf) with
  | none => simp [hb, back] at h
  | some found =>
    simp only [hb, back, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      Option.some.injEq] at h
    subst h
    have lookup : ∀ n, (seen.toList.foldl (init := ({} : Std.HashMap Name (Array Name)))
        fun table m => table.insert m (reachedFrom found m))[n]? =
          if n ∈ seen then some (reachedFrom found n) else none := by
      intro n
      rw [foldl_insert_getElem?]
      simp [Std.HashSet.mem_toList]
    refine ⟨fun n hn => ⟨reachedFrom found n, ?_⟩, fun n axioms hn a => ?_⟩
    · rw [lookup]
      simp [complete n (Array.mem_toList_iff.mpr hn) n (.refl n)]
    rw [lookup] at hn
    by_cases hseen : n ∈ seen
    · simp only [hseen, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      have after : ∀ x y, x ∈ back y → y ∈ next x := by
        intro x y hx
        simp only [back, List.mem_toArray, mem_predecessors] at hx
        obtain ⟨e, he, rfl, hy⟩ := hx
        rwa [edgeOK e he] at hy
      have before : ∀ x ∈ seen, ∀ y ∈ next x, x ∈ back y := by
        intro x hx y hy
        obtain ⟨e, he, rfl⟩ := hasEdge x hx
        simp only [back, List.mem_toArray, mem_predecessors]
        exact ⟨e, he, rfl, (edgeOK e he) ▸ hy⟩
      have closed : ∀ x ∈ seen, ∀ y ∈ next x, y ∈ seen := by
        intro x hx y hy
        obtain ⟨s, hs, hr⟩ := sound x hx
        exact complete s hs y (hr.tail hy)
      obtain ⟨searched, entries⟩ := searchBack_some hb
      simp only [reachedFrom, List.mem_toArray, List.mem_filterMap,
        Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists]
      constructor
      · rintro ⟨b, reaching, hentry, hcontains, rfl⟩
        obtain ⟨haxiom, hsearch⟩ := entries _ hentry
        obtain ⟨-, hfound⟩ := search_some hsearch
        obtain ⟨s, hs, hr⟩ := hfound n (Std.HashSet.mem_iff_contains.mpr hcontains)
        rw [List.mem_singleton.mp hs] at hr
        simp only [List.mem_filter] at haxiom
        exact ⟨reach_forward after hr, haxiom.2⟩
      · rintro ⟨hr, hax⟩
        have haxiom : a ∈ seen.toList.filter leaf := by
          simp only [List.mem_filter, Std.HashSet.mem_toList]
          obtain ⟨s, hs, hsr⟩ := sound n hseen
          exact ⟨complete s hs a (hsr.trans hr), hax⟩
        obtain ⟨reaching, hentry, hsearch⟩ := searched a haxiom
        have hback : Reach back a n := reach_back closed before hseen hr
        exact ⟨a, reaching, hentry,
          Std.HashSet.mem_iff_contains.mp ((search_some hsearch).1 a List.mem_cons_self n hback),
          rfl⟩
    · simp [hseen] at hn

/-- The axioms that each name of the forward search `forward` reaches in `find`, under that name:
the `leafTable` of the search, with the axioms as the leaves. When `forward` is the search of the
constants used (`successors find`) from the roots, each constant's successors are computed once.
The table holds every name the forward search reached, so a later search can stop at any of them
(`axiomsWith`). `none` when a search back runs out of `fuel`. -/
def axiomTable (find : Name → Option ConstantInfo) (fuel : Nat)
    (forward : Std.HashSet Name × List (Name × Array Name)) :
    Option (Std.HashMap Name (Array Name)) :=
  leafTable (isAxiomIn find) fuel forward

/-- **`axiomTable` of the search of the constants used from `roots` holds each name of `roots`, and
gives each name it holds exactly the axioms that name reaches** (`ReachesAxiom`). -/
theorem axiomTable_some {find : Name → Option ConstantInfo} {fuel : Nat} {roots : Array Name}
    {forward : Std.HashSet Name × List (Name × Array Name)}
    {table : Std.HashMap Name (Array Name)}
    (hs : searchEdges (successors find) fuel roots.toList = some forward)
    (h : axiomTable find fuel forward = some table) :
    (∀ n ∈ roots, ∃ axioms, table[n]? = some axioms) ∧
      ∀ n axioms, table[n]? = some axioms → ∀ a, a ∈ axioms ↔ ReachesAxiom find n a :=
  have ⟨holds, exact⟩ := leafTable_some hs h
  ⟨holds, fun n axioms found a => (exact n axioms found a).trans
    ⟨fun ⟨reach, isAxiom⟩ => ⟨reach, (isAxiomIn_iff find a).mp isAxiom⟩,
      fun ⟨reach, isAxiom⟩ => ⟨reach, (isAxiomIn_iff find a).mpr isAxiom⟩⟩⟩

/-! ## A search that stops at names of known axioms

The checks of proofs that the checker builds itself (a recursion equation, an execution
correspondence) add a theorem to the audited environment and need its axioms. The search from it
stops at each name whose axioms a table already holds (`axiomsWith`), the table of the owned
declarations' closure that admission computed in the replayed kernel, and reads that entry
instead. -/

/-- The names after `n` along `next`, or none when `cached` holds `n`: the search stops there. -/
def stopAt (cached : Std.HashMap Name (Array Name)) (next : Name → Array Name) (n : Name) :
    Array Name :=
  if cached.contains n then #[] else next n

/-- Each entry of `cached` gives its name exactly the axioms that name reaches in `find`. -/
def CacheCorrect (find : Name → Option ConstantInfo) (cached : Std.HashMap Name (Array Name)) :
    Prop :=
  ∀ n axioms, cached[n]? = some axioms → ∀ a, a ∈ axioms ↔ ReachesAxiom find n a

/-- The axioms that the names `names` give through the table `cached`: the entry of each name
`cached` holds, and each other name that `find` holds as an axiom. -/
def expand (find : Name → Option ConstantInfo) (cached : Std.HashMap Name (Array Name))
    (names : List Name) : Array Name :=
  (names.flatMap fun m => match cached[m]? with
    | some axioms => axioms.toList
    | none => if isAxiomIn find m then [m] else []).toArray

/-- The axioms `n` reaches in `find`, read through the table `cached`: the search from `n` stops
at each name `cached` holds and takes that name's entry, and takes each other name it reaches
that `find` holds as an axiom. `none` when the search runs out of `fuel`. -/
def axiomsWith (find : Name → Option ConstantInfo) (cached : Std.HashMap Name (Array Name))
    (fuel : Nat) (n : Name) : Option (Array Name) :=
  (search (stopAt cached (successors find)) fuel [n]).map fun seen =>
    expand find cached seen.toList

/-- Reachability along a relation is reachability along any relation that has its steps. -/
theorem Reach.mono {next next' : Name → Array Name} (sub : ∀ x m, m ∈ next x → m ∈ next' x)
    {x y : Name} (h : Reach next x y) : Reach next' x y := by
  induction h with
  | refl => exact .refl _
  | step hm _ ih => exact .step (sub _ _ hm) ih

/-- Each name after `x` along `stopAt cached next` is after it along `next`. -/
theorem stopAt_sub {cached : Std.HashMap Name (Array Name)} {next : Name → Array Name}
    (x m : Name) (hm : m ∈ stopAt cached next x) : m ∈ next x := by
  unfold stopAt at hm
  split at hm
  · simp at hm
  · exact hm

/-- A path either reaches a name `cached` holds while it stops at none, and goes on from there,
or it reaches its end, a name `cached` does not hold, while it stops at none. -/
private theorem reach_stop {cached : Std.HashMap Name (Array Name)} {next : Name → Array Name}
    {x a : Name} (h : Reach next x a) :
    (∃ c, cached.contains c = true ∧ Reach (stopAt cached next) x c ∧ Reach next c a) ∨
      (Reach (stopAt cached next) x a ∧ cached.contains a = false) := by
  induction h with
  | refl n =>
    cases hc : cached.contains n
    · exact .inr ⟨.refl n, rfl⟩
    · exact .inl ⟨n, hc, .refl n, .refl n⟩
  | @step n m x hm rest ih =>
    cases hc : cached.contains n
    · have hstep : m ∈ stopAt cached next n := by simp [stopAt, hc, hm]
      rcases ih with ⟨c, hcc, hrc, hca⟩ | ⟨hra, hna⟩
      · exact .inl ⟨c, hcc, .step hstep hrc, hca⟩
      · exact .inr ⟨.step hstep hra, hna⟩
    · exact .inl ⟨n, hc, .refl n, .step hm rest⟩

/-- **With a correct table, `expand` of names that `n` reaches, among them each name the search
from `n` that stops at the names of the table reaches and that the table holds or `find` holds as
an axiom, is exactly the axioms `n` reaches** (`ReachesAxiom`). -/
theorem mem_expand {find : Name → Option ConstantInfo} {cached : Std.HashMap Name (Array Name)}
    {n : Name} {names : List Name} (correct : CacheCorrect find cached)
    (sound : ∀ m ∈ names, Reach (successors find) n m)
    (complete : ∀ m, Reach (stopAt cached (successors find)) n m →
      cached.contains m = true ∨ isAxiomIn find m = true → m ∈ names) (a : Name) :
    a ∈ expand find cached names ↔ ReachesAxiom find n a := by
  unfold expand
  simp only [List.mem_toArray, List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, ha⟩
    cases hc : cached[m]? with
    | some entry =>
      rw [hc] at ha
      obtain ⟨hr, hax⟩ := (correct m entry hc a).mp (Array.mem_toList_iff.mp ha)
      exact ⟨(sound m hm).trans hr, hax⟩
    | none =>
      rw [hc] at ha
      by_cases hax : isAxiomIn find m = true
      · simp only [hax, ↓reduceIte, List.mem_singleton] at ha
        subst ha
        exact ⟨sound a hm, (isAxiomIn_iff find a).mp hax⟩
      · simp [hax] at ha
  · rintro ⟨hr, hax⟩
    rcases reach_stop (cached := cached) hr with ⟨c, hcc, hrc, hca⟩ | ⟨hra, hna⟩
    · have hsome : (cached[c]?).isSome = true := by
        rw [← Std.HashMap.contains_eq_isSome_getElem?]
        exact hcc
      obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨c, complete c hrc (.inl hcc), ?_⟩
      rw [hentry]
      exact Array.mem_toList_iff.mpr ((correct c entry hentry a).mpr ⟨hca, hax⟩)
    · refine ⟨a, complete a hra (.inr ((isAxiomIn_iff find a).mpr hax)), ?_⟩
      have hnone : cached[a]? = none := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hna
        simpa using hna
      rw [hnone]
      simp [(isAxiomIn_iff find a).mpr hax]

/-- **With a correct table, `axiomsWith` returns exactly the axioms `n` reaches**
(`ReachesAxiom`). -/
theorem axiomsWith_some {find : Name → Option ConstantInfo}
    {cached : Std.HashMap Name (Array Name)} {fuel : Nat} {n : Name} {axioms : Array Name}
    (correct : CacheCorrect find cached) (h : axiomsWith find cached fuel n = some axioms) :
    ∀ a, a ∈ axioms ↔ ReachesAxiom find n a := by
  unfold axiomsWith at h
  cases hs : search (stopAt cached (successors find)) fuel [n] with
  | none => simp [hs] at h
  | some seen =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨complete, sound⟩ := search_some hs
    refine mem_expand correct (fun m hm => ?_)
      (fun m hr _ => Std.HashSet.mem_toList.mpr (complete n List.mem_cons_self m hr))
    obtain ⟨s, hs, hr⟩ := sound m (Std.HashSet.mem_toList.mp hm)
    rw [List.mem_singleton.mp hs] at hr
    exact hr.mono stopAt_sub

/-- The axioms that each name of the forward search `forward` reaches in `find`, under that name,
read through the table `cached`: the `leafTable` of the search with the names that `cached` or
`find` holds as an axiom as the leaves, each entry's leaves expanded through `cached` (`expand`).
When `forward` is the search from the roots that stops at the names of `cached`, a name of
`cached` is not searched past. `none` when a search back runs out of `fuel`. -/
def stoppedTable (find : Name → Option ConstantInfo) (cached : Std.HashMap Name (Array Name))
    (fuel : Nat) (forward : Std.HashSet Name × List (Name × Array Name)) :
    Option (Std.HashMap Name (Array Name)) :=
  (leafTable (fun m => cached.contains m || isAxiomIn find m) fuel forward).map fun leaves =>
    leaves.map fun _ found => expand find cached found.toList

/-- **With a correct table, `stoppedTable` of the search from `roots` that stops at the names of
the table holds each name of `roots`, and gives each name it holds exactly the axioms that name
reaches** (`ReachesAxiom`). -/
theorem stoppedTable_some {find : Name → Option ConstantInfo}
    {cached : Std.HashMap Name (Array Name)} {fuel : Nat} {roots : Array Name}
    {forward : Std.HashSet Name × List (Name × Array Name)}
    {table : Std.HashMap Name (Array Name)} (correct : CacheCorrect find cached)
    (hs : searchEdges (stopAt cached (successors find)) fuel roots.toList = some forward)
    (h : stoppedTable find cached fuel forward = some table) :
    (∀ n ∈ roots, ∃ axioms, table[n]? = some axioms) ∧
      ∀ n axioms, table[n]? = some axioms → ∀ a, a ∈ axioms ↔ ReachesAxiom find n a := by
  unfold stoppedTable at h
  cases hl : leafTable (fun m => cached.contains m || isAxiomIn find m) fuel forward with
  | none => simp [hl] at h
  | some leaves =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨holds, exact⟩ := leafTable_some hs hl
    refine ⟨fun n hn => ?_, fun n axioms hn => ?_⟩
    · obtain ⟨found, hf⟩ := holds n hn
      exact ⟨expand find cached found.toList, by simp [hf]⟩
    · simp only [Std.HashMap.getElem?_map'] at hn
      cases hr : leaves[n]? with
      | none => simp [hr] at hn
      | some found =>
        simp only [hr, Option.pmap_some, Option.some.injEq] at hn
        subst hn
        exact mem_expand correct
          (fun m hm => ((exact n found hr m).mp (Array.mem_toList_iff.mp hm)).1.mono stopAt_sub)
          (fun m hr' hleaf => Array.mem_toList_iff.mpr
            ((exact n found hr m).mpr ⟨hr', (Bool.or_eq_true _ _).mpr hleaf⟩))

/-! ## Axioms with hidden bodies

Under the module system, a module imported without `import all` gives the importer the exported
form of its constants: a theorem, and a definition whose body the module does not expose, are
axioms there. The search treats such a name as an axiom, so `axiomsThrough` replaces each hidden
name it reaches by the axioms that `hidden` records for it, the table of the module that holds the
body, and keeps every other axiom it reaches. -/

/-- The axioms `axioms`, each name that `hidden` records replaced by its record. -/
def throughHidden (hidden : Name → Option (Array Name)) (axioms : Array Name) : Array Name :=
  (axioms.toList.flatMap fun a => match hidden a with
    | some recorded => recorded.toList
    | none => [a]).toArray

/-- `throughHidden` of the axioms that `P` describes holds exactly those that `hidden` does not
record and the records of those it does. -/
theorem mem_throughHidden {hidden : Name → Option (Array Name)} {axioms : Array Name}
    {P : Name → Prop} (exact : ∀ a, a ∈ axioms ↔ P a) (a : Name) :
    a ∈ throughHidden hidden axioms ↔ (P a ∧ hidden a = none) ∨
      ∃ h recorded, P h ∧ hidden h = some recorded ∧ a ∈ recorded := by
  unfold throughHidden
  simp only [List.mem_toArray, List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, ha⟩
    have hp := (exact m).mp (Array.mem_toList_iff.mp hm)
    cases hh : hidden m with
    | some recorded =>
      rw [hh] at ha
      exact .inr ⟨m, recorded, hp, hh, Array.mem_toList_iff.mp ha⟩
    | none =>
      rw [hh, List.mem_singleton] at ha
      subst ha
      exact .inl ⟨hp, hh⟩
  · rintro (⟨hp, hh⟩ | ⟨m, recorded, hp, hh, ha⟩)
    · exact ⟨a, Array.mem_toList_iff.mpr ((exact a).mpr hp), by simp [hh]⟩
    · exact ⟨m, Array.mem_toList_iff.mpr ((exact m).mpr hp), by
        simp [hh, Array.mem_toList_iff.mpr ha]⟩

/-- The axioms `n` reaches in `find` (`axiomsWith` with no table), each name that `hidden` records
replaced by its record. `none` when the search runs out of `fuel`. -/
def axiomsThrough (find : Name → Option ConstantInfo) (hidden : Name → Option (Array Name))
    (fuel : Nat) (n : Name) : Option (Array Name) :=
  (axiomsWith find {} fuel n).map (throughHidden hidden)

/-- **`axiomsThrough` returns exactly the axioms that `n` reaches and `hidden` does not record,
with the records of those it does.** -/
theorem axiomsThrough_some {find : Name → Option ConstantInfo}
    {hidden : Name → Option (Array Name)} {fuel : Nat} {n : Name} {axioms : Array Name}
    (h : axiomsThrough find hidden fuel n = some axioms) :
    ∀ a, a ∈ axioms ↔ (ReachesAxiom find n a ∧ hidden a = none) ∨
      ∃ h recorded, ReachesAxiom find n h ∧ hidden h = some recorded ∧ a ∈ recorded := by
  unfold axiomsThrough at h
  cases hs : axiomsWith find {} fuel n with
  | none => simp [hs] at h
  | some reached =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst h
    exact mem_throughHidden (axiomsWith_some (fun _ _ hc => by simp at hc) hs)

/-! ## A table of the axioms of imported names

The editor checks each command of a file in an environment that extends the same imports, so the
axioms an imported name reaches are the same in each. `remember` keeps the entries that a table
search computed for imported names that reach only imported names, so that each later search stops
there. `MemoInv` states what such a table satisfies, `remember_inv` that `remember` keeps it,
`MemoInv.transfer` that it carries over to an environment that holds the same imported constants,
and `tableThrough_agree` that a search that stops at its names computes what the search with no
table computes. -/

/-- `cached` is a correct table for `find`, and each name it holds reaches only names that
`imported` accepts. -/
def MemoInv (find : Name → Option ConstantInfo) (imported : Name → Bool)
    (cached : Std.HashMap Name (Array Name)) : Prop :=
  CacheCorrect find cached ∧
    ∀ n, cached.contains n = true → ∀ x, Reach (successors find) n x → imported x = true

/-- The empty table satisfies `MemoInv`. -/
theorem memoInv_empty (find : Name → Option ConstantInfo) (imported : Name → Bool) :
    MemoInv find imported {} :=
  ⟨fun _ _ hc => by simp at hc, fun _ hc => by simp at hc⟩

/-- **`MemoInv` carries over to `find₂` and `imported₂` when each name `imported₁` accepts is
accepted by `imported₂`, and has in `find₂` the successors and the axiom kind it has in
`find₁`.** -/
theorem MemoInv.transfer {find₁ find₂ : Name → Option ConstantInfo}
    {imported₁ imported₂ : Name → Bool} {cached : Std.HashMap Name (Array Name)}
    (inv : MemoInv find₁ imported₁ cached)
    (agree : ∀ x, imported₁ x = true → imported₂ x = true ∧
      successors find₂ x = successors find₁ x ∧ isAxiomIn find₂ x = isAxiomIn find₁ x) :
    MemoInv find₂ imported₂ cached := by
  obtain ⟨correct, region⟩ := inv
  have forth : ∀ y x, Reach (successors find₁) y x →
      (∀ z, Reach (successors find₁) y z → imported₁ z = true) → Reach (successors find₂) y x := by
    intro y x h
    induction h with
    | refl => exact fun _ => .refl _
    | @step y m x hm _ ih =>
      intro hreg
      have hm₂ : m ∈ successors find₂ y := by
        rw [(agree y (hreg y (.refl y))).2.1]
        exact hm
      exact .step hm₂ (ih fun z hz => hreg z (.step hm hz))
  have back : ∀ y x, Reach (successors find₂) y x →
      (∀ z, Reach (successors find₁) y z → imported₁ z = true) → Reach (successors find₁) y x := by
    intro y x h
    induction h with
    | refl => exact fun _ => .refl _
    | @step y m x hm _ ih =>
      intro hreg
      have hm₁ : m ∈ successors find₁ y := by
        rw [← (agree y (hreg y (.refl y))).2.1]
        exact hm
      exact .step hm₁ (ih fun z hz => hreg z (.step hm₁ hz))
  have reach : ∀ n, cached.contains n = true → ∀ x,
      Reach (successors find₂) n x ↔ Reach (successors find₁) n x := fun n hn x =>
    ⟨fun h => back n x h (region n hn), fun h => forth n x h (region n hn)⟩
  refine ⟨fun n axioms hn a => ?_, fun n hn x hr =>
    (agree x (region n hn x ((reach n hn x).mp hr))).1⟩
  have hc : cached.contains n = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, hn]
    rfl
  rw [correct n axioms hn a]
  unfold ReachesAxiom
  constructor
  · rintro ⟨hr, hax⟩
    refine ⟨(reach n hc a).mpr hr, (isAxiomIn_iff find₂ a).mp ?_⟩
    rw [(agree a (region n hc a hr)).2.2]
    exact (isAxiomIn_iff find₁ a).mpr hax
  · rintro ⟨hr, hax⟩
    have hr₁ := (reach n hc a).mp hr
    refine ⟨hr₁, (isAxiomIn_iff find₁ a).mp ?_⟩
    rw [← (agree a (region n hc a hr₁)).2.2]
    exact (isAxiomIn_iff find₂ a).mpr hax

/-- `cached` with the entry of `table` for each name of the forward search `forward` that
`imported` accepts and that reaches, along the search, only names `imported` accepts: those that
the one search back along the recorded edges from all the names `imported` refuses does not reach.
`cached` itself when that search runs out of `fuel`. The names before each name are computed once,
not once for each name the search back expands. -/
def remember (imported : Name → Bool) (fuel : Nat)
    (forward : Std.HashSet Name × List (Name × Array Name))
    (table cached : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  let preds := predecessors forward.2
  match search (fun y => (preds.getD y []).toArray) fuel
      (forward.1.toList.filter fun m => !imported m) with
  | some outside =>
    (forward.1.toList.filterMap fun n =>
      if imported n && !outside.contains n then table[n]?.map (n, ·) else none).foldl
        (init := cached) fun kept entry => kept.insert entry.1 entry.2
  | none => cached

/-- Each entry of a fold of `insert` over `entries` is one of `entries` or of `init`. -/
private theorem foldl_insert_some :
    ∀ (entries : List (Name × Array Name)) (init : Std.HashMap Name (Array Name)) (n : Name)
      (axioms : Array Name),
      (entries.foldl (init := init) fun kept entry => kept.insert entry.1 entry.2)[n]? =
        some axioms → (n, axioms) ∈ entries ∨ init[n]? = some axioms := by
  intro entries
  induction entries with
  | nil => exact fun _ _ _ h => .inr h
  | cons entry rest ih =>
    intro init n axioms h
    simp only [List.foldl_cons] at h
    rcases ih _ n axioms h with hr | hi
    · exact .inl (List.mem_cons_of_mem _ hr)
    · rw [Std.HashMap.getElem?_insert] at hi
      split at hi
      · rename_i heq
        simp only [Option.some.injEq] at hi
        subst hi
        rw [← beq_iff_eq.mp heq]
        exact .inl List.mem_cons_self
      · exact .inr hi

/-- **`remember` keeps `MemoInv`:** after the search from `roots` that stops at the names of
`cached`, and its `stoppedTable`, each entry it adds is correct and reaches only accepted
names. -/
theorem remember_inv {find : Name → Option ConstantInfo} {imported : Name → Bool}
    {cached : Std.HashMap Name (Array Name)} {fuel : Nat} {roots : Array Name}
    {forward : Std.HashSet Name × List (Name × Array Name)}
    {table : Std.HashMap Name (Array Name)} (inv : MemoInv find imported cached)
    (hs : searchEdges (stopAt cached (successors find)) fuel roots.toList = some forward)
    (h : stoppedTable find cached fuel forward = some table) :
    MemoInv find imported (remember imported fuel forward table cached) := by
  obtain ⟨correct, region⟩ := inv
  obtain ⟨-, exact⟩ := stoppedTable_some correct hs h
  obtain ⟨seen, edges⟩ := forward
  obtain ⟨complete, sound, hasEdge, edgeOK⟩ := searchEdges_some hs
  let back := fun y => ((predecessors edges).getD y []).toArray
  have closed : ∀ x ∈ seen, ∀ y ∈ stopAt cached (successors find) x, y ∈ seen := by
    intro x hx y hy
    obtain ⟨s, hs', hr⟩ := sound x hx
    exact complete s hs' y (hr.tail hy)
  have before : ∀ x ∈ seen, ∀ y ∈ stopAt cached (successors find) x, x ∈ back y := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := hasEdge x hx
    simp only [back, List.mem_toArray, mem_predecessors]
    exact ⟨e, he, rfl, (edgeOK e he) ▸ hy⟩
  unfold remember
  dsimp only
  split
  · rename_i outside ho
    obtain ⟨found, -⟩ := search_some ho
    have added : ∀ n axioms, (n, axioms) ∈ (seen.toList.filterMap fun n =>
        if imported n && !outside.contains n then table[n]?.map (n, ·) else none) →
        table[n]? = some axioms ∧ ∀ x, Reach (successors find) n x → imported x = true := by
      intro n axioms hm
      obtain ⟨m, hmem, he⟩ := List.mem_filterMap.mp hm
      split at he
      · rename_i hcond
        obtain ⟨-, hout⟩ := Bool.and_eq_true_iff.mp hcond
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
        obtain ⟨entry, hentry, rfl, rfl⟩ := he
        refine ⟨hentry, fun x hr => ?_⟩
        rcases reach_stop (cached := cached) hr with ⟨c, hcc, -, hcx⟩ | ⟨hrx, -⟩
        · exact region c hcc x hcx
        · cases hx : imported x
          · have hseen := Std.HashSet.mem_toList.mp hmem
            obtain ⟨s, hs', hrs⟩ := sound _ hseen
            have hsrc : x ∈ seen.toList.filter fun m => !imported m :=
              List.mem_filter.mpr ⟨Std.HashSet.mem_toList.mpr (complete s hs' x (hrs.trans hrx)),
                by simp [hx]⟩
            have hin := found x hsrc _ (reach_back closed before hseen hrx)
            rw [Std.HashSet.mem_iff_contains] at hin
            rw [hin] at hout
            simp at hout
          · rfl
      · simp at he
    refine ⟨fun n axioms hn a => ?_, fun n hn x hr => ?_⟩
    · rcases foldl_insert_some _ _ n axioms hn with hm | hc
      · exact exact n axioms (added n axioms hm).1 a
      · exact correct n axioms hc a
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at hn
      obtain ⟨axioms, hn⟩ := Option.isSome_iff_exists.mp hn
      rcases foldl_insert_some _ _ n axioms hn with hm | hc
      · exact (added n axioms hm).2 x hr
      · have hcc : cached.contains n = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hc]
          rfl
        exact region n hcc x hr
  · exact ⟨correct, region⟩

/-- The table of `stoppedTable` for the search from the names `roots` that stops at the names of
`cached`, each entry's names that `hidden` records replaced by their records. `none` when a
search runs out of `fuel`. -/
def axiomTableThrough (find : Name → Option ConstantInfo) (hidden : Name → Option (Array Name))
    (cached : Std.HashMap Name (Array Name)) (fuel : Nat) (roots : Array Name) :
    Option (Std.HashMap Name (Array Name)) := do
  let forward ← searchEdges (stopAt cached (successors find)) fuel roots.toList
  let table ← stoppedTable find cached fuel forward
  return table.map fun _ => throughHidden hidden

/-- **With a correct table, `axiomTableThrough` holds each name of `roots`, and gives each name it
holds exactly the axioms that name reaches and `hidden` does not record, with the records of those
it does.** -/
theorem axiomTableThrough_some {find : Name → Option ConstantInfo}
    {hidden : Name → Option (Array Name)} {cached : Std.HashMap Name (Array Name)} {fuel : Nat}
    {roots : Array Name} {table : Std.HashMap Name (Array Name)}
    (correct : CacheCorrect find cached)
    (h : axiomTableThrough find hidden cached fuel roots = some table) :
    (∀ n ∈ roots, ∃ axioms, table[n]? = some axioms) ∧
      ∀ n axioms, table[n]? = some axioms → ∀ a, a ∈ axioms ↔
        (ReachesAxiom find n a ∧ hidden a = none) ∨
          ∃ h recorded, ReachesAxiom find n h ∧ hidden h = some recorded ∧ a ∈ recorded := by
  unfold axiomTableThrough at h
  cases hs : searchEdges (stopAt cached (successors find)) fuel roots.toList with
  | none => simp [hs] at h
  | some forward =>
    cases ht : stoppedTable find cached fuel forward with
    | none => simp [hs, ht] at h
    | some reached =>
      simp only [hs, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      obtain ⟨holds, exact⟩ := stoppedTable_some correct hs ht
      refine ⟨fun n hn => ?_, fun n axioms hn => ?_⟩
      · obtain ⟨axioms, ha⟩ := holds n hn
        exact ⟨throughHidden hidden axioms, by simp [ha]⟩
      · simp only [Std.HashMap.getElem?_map'] at hn
        cases hr : reached[n]? with
        | none => simp [hr] at hn
        | some entry =>
          simp only [hr, Option.pmap_some, Option.some.injEq] at hn
          subst hn
          exact mem_throughHidden (exact n entry hr)

/-- The table of `axiomTableThrough`, with `cached` and the entries its search computed for names
that `imported` accepts and that reach only such names (`remember`). `none` when a search runs
out of `fuel`. -/
def tableThrough (find : Name → Option ConstantInfo) (hidden : Name → Option (Array Name))
    (imported : Name → Bool) (cached : Std.HashMap Name (Array Name)) (fuel : Nat)
    (roots : Array Name) :
    Option (Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name)) := do
  let forward ← searchEdges (stopAt cached (successors find)) fuel roots.toList
  let table ← stoppedTable find cached fuel forward
  return (table.map fun _ => throughHidden hidden, remember imported fuel forward table cached)

/-- The table `tableThrough` returns is the table of `axiomTableThrough`. -/
theorem tableThrough_fst {find : Name → Option ConstantInfo}
    {hidden : Name → Option (Array Name)} {imported : Name → Bool}
    {cached : Std.HashMap Name (Array Name)} {fuel : Nat} {roots : Array Name}
    {table kept : Std.HashMap Name (Array Name)}
    (h : tableThrough find hidden imported cached fuel roots = some (table, kept)) :
    axiomTableThrough find hidden cached fuel roots = some table := by
  unfold tableThrough at h
  unfold axiomTableThrough
  cases hs : searchEdges (stopAt cached (successors find)) fuel roots.toList with
  | none => simp [hs] at h
  | some forward =>
    cases ht : stoppedTable find cached fuel forward with
    | none => simp [hs, ht] at h
    | some reached =>
      simp only [hs, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact h.1

/-- **With a table that `MemoInv` admits, `tableThrough` holds each name of `roots`, gives each
name it holds exactly the axioms that name reaches and `hidden` does not record, with the records
of those it does, and keeps `MemoInv` in the table it returns.** -/
theorem tableThrough_some {find : Name → Option ConstantInfo}
    {hidden : Name → Option (Array Name)} {imported : Name → Bool}
    {cached : Std.HashMap Name (Array Name)} {fuel : Nat} {roots : Array Name}
    {table kept : Std.HashMap Name (Array Name)} (inv : MemoInv find imported cached)
    (h : tableThrough find hidden imported cached fuel roots = some (table, kept)) :
    (∀ n ∈ roots, ∃ axioms, table[n]? = some axioms) ∧
      (∀ n axioms, table[n]? = some axioms → ∀ a, a ∈ axioms ↔
        (ReachesAxiom find n a ∧ hidden a = none) ∨
          ∃ h recorded, ReachesAxiom find n h ∧ hidden h = some recorded ∧ a ∈ recorded) ∧
      MemoInv find imported kept := by
  obtain ⟨holds, exact⟩ := axiomTableThrough_some inv.1 (tableThrough_fst h)
  refine ⟨holds, exact, ?_⟩
  unfold tableThrough at h
  cases hs : searchEdges (stopAt cached (successors find)) fuel roots.toList with
  | none => simp [hs] at h
  | some forward =>
    cases ht : stoppedTable find cached fuel forward with
    | none => simp [hs, ht] at h
    | some reached =>
      simp only [hs, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact remember_inv inv hs ht

/-- **With a table that `MemoInv` admits, `tableThrough` gives each name the axioms that
`axiomTableThrough` gives it with no table.** -/
theorem tableThrough_agree {find : Name → Option ConstantInfo}
    {hidden : Name → Option (Array Name)} {imported : Name → Bool}
    {cached : Std.HashMap Name (Array Name)} {fuel fuel' : Nat} {roots : Array Name}
    {table kept table' : Std.HashMap Name (Array Name)} (inv : MemoInv find imported cached)
    (h : tableThrough find hidden imported cached fuel roots = some (table, kept))
    (h' : axiomTableThrough find hidden {} fuel' roots = some table')
    {n : Name} {axioms axioms' : Array Name} (hn : table[n]? = some axioms)
    (hn' : table'[n]? = some axioms') (a : Name) : a ∈ axioms ↔ a ∈ axioms' :=
  ((tableThrough_some inv h).2.1 n axioms hn a).trans
    ((axiomTableThrough_some (memoInv_empty find imported).1 h').2 n axioms' hn' a).symm

/-! ## The axioms a name reaches in an environment -/

/-- A bound on the names a search in `env` expands: one for each constant of its modules and of
the current module, and `extra` more. Every name a constant of a kernel environment uses is a
constant of it. -/
def fuelFor (env : Environment) (extra : Nat) : Nat :=
  env.header.moduleData.foldl (fun total data => total + data.constants.size) 0 +
    env.constants.map₂.foldl (fun total _ _ => total + 1) 0 + extra

/-- The axioms that Lean's `collectAxioms` reports for `name` in `env`: for a name that an
imported module exported, those the module recorded when it was compiled. -/
def recordedAxioms (env : Environment) (name : Name) : Array Name :=
  letI : MonadEnv (StateM Environment) := ⟨get, modify⟩
  (collectAxioms name : StateM Environment (Array Name)).run' env

/-- The record of the axioms of `name` when it was declared as another kind than an axiom, which
is how the search meets a name that `env` holds as an axiom although it was declared otherwise:
the module system exported it without its body, and only the table of the module that holds the
body records what the body uses.

Assumes: in a module, Lean 4.35.0 exports a theorem, and a definition or an opaque constant whose
body is not exposed, as an axiom (`Lean/AddDecl.lean:112-125`); it records the declared kind of
each such name (`Lean/AddDecl.lean:146-148`), which `getOriginalConstKind?` reads
(`Lean/OriginalConstKind.lean:25-29`), and an importer that does not `import all` the module loads
its exported constants (`Lean/Environment.lean:2030-2034`). The record is the table that module
computed when it was compiled (`Lean/Util/CollectAxioms.lean:120-143`), a trusted input: the
importer has no body to search. -/
def hiddenAxioms (env : Environment) (name : Name) : Option (Array Name) :=
  match getOriginalConstKind? env name with
  | some .axiom | none => none
  | some _ => some (recordedAxioms env name)

/-- The axioms `name` reaches in the kernel environment of `env`, read by the checker's own search
(`axiomsThrough`, exact by `axiomsThrough_some`) instead of Lean's `collectAxioms`, whose cache
entry for a constant on a cycle it is still expanding is empty
(`Lean/Util/CollectAxioms.lean:45-53`), so that an inductive type reached through its constructor,
or a constructor reached through its type, can be recorded without the axioms of the rest of the
cycle, and the table a module writes shares that cache across its declarations
(`Lean/Util/CollectAxioms.lean:136-139`). A name whose body `env` hides reads its module's record
(`hiddenAxioms`). `none` when the search runs out of fuel. -/
def reachedAxioms (env : Environment) (name : Name) : Option (Array Name) :=
  axiomsThrough env.toKernelEnv.find? (hiddenAxioms env) (fuelFor env 1) name

/-- Whether `n` is a constant of the kernel environment of `env` that an imported module holds. -/
def importedIn (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isSome && (env.toKernelEnv.find? n).isSome

/-- The table of `reachedAxiomTable` for `names`, read by one search that stops at the names of
`cached` (`tableThrough`, exact by `tableThrough_some` when `MemoInv` admits `cached`, and equal
to `reachedAxiomTable` by `tableThrough_agree`), and `cached` with the entries this search
computed for the imported constants (`importedIn`). `none` when a search runs out of fuel. -/
def rememberedAxiomTable (env : Environment) (cached : Std.HashMap Name (Array Name))
    (names : Array Name) :
    Option (Std.HashMap Name (Array Name) × Std.HashMap Name (Array Name)) :=
  tableThrough env.toKernelEnv.find? (hiddenAxioms env) (importedIn env) cached (fuelFor env 1)
    names

/-- The axioms that each name reachable from `names` reaches in the kernel environment of `env`,
under that name, read as `reachedAxioms` reads them for one name, with one search for all of
`names` (`axiomTableThrough` with no table to stop at, exact by `axiomTableThrough_some`). `none`
when a search runs out of fuel. -/
def reachedAxiomTable (env : Environment) (names : Array Name) :
    Option (Std.HashMap Name (Array Name)) :=
  axiomTableThrough env.toKernelEnv.find? (hiddenAxioms env) {} (fuelFor env 1) names

end RegulaPolicy.KernelAxioms
