module

public import Lean.Environment
public import Lean.Util.FoldConsts
public import Std.Data.HashMap.Lemmas
public import Std.Data.HashSet.Lemmas

/-! # Axioms reached in a kernel environment

The axioms a declaration rests on, computed from the constants of a kernel environment alone: the
names its type and value reach, through the types and values of the constants they use, that the
environment holds as axioms (`ReachesAxiom`). Admission computes them in the kernel that replayed
the owned modules (`Admission.validate`), so the foundation rules decide on what that kernel
checked, never on the axiom table `exportedAxiomsExt` that Lean's `collectAxioms` reads first for
an imported name.

A search of a graph of names (`search`) underlies both computations here: `axiomTable`, one forward
search from every requested name and one backward search from each axiom found, for all the names
of their closure in one environment, and `axiomsWith`, a search from one name that stops at the
names of such a table. `axiomTable_some` and `axiomsWith_some` state that each returns exactly the
axioms `ReachesAxiom` relates to a name. Each search is bounded by its fuel: a search that runs out
returns `none`, and the caller refuses.

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

/-- The axioms that each name reachable from `roots` reaches in `find`, under that name: one forward
search from all of `roots`, then one search back from each axiom it finds, along the edges the
forward search recorded, so each constant's successors are computed once. The table holds every
name the forward search reached, so a later search can stop at any of them (`axiomsWith`).
`none` when a search runs out of `fuel`. -/
def axiomTable (find : Name → Option ConstantInfo) (fuel : Nat) (roots : Array Name) :
    Option (Std.HashMap Name (Array Name)) := do
  let (seen, edges) ← searchEdges (successors find) fuel roots.toList
  let preds := predecessors edges
  let found ← searchBack (fun y => (preds.getD y []).toArray) fuel
    (seen.toList.filter (isAxiomIn find))
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

/-- **`axiomTable` holds each name of `roots`, and gives each name it holds exactly the axioms that
name reaches** (`ReachesAxiom`). -/
theorem axiomTable_some {find : Name → Option ConstantInfo} {fuel : Nat} {roots : Array Name}
    {table : Std.HashMap Name (Array Name)} (h : axiomTable find fuel roots = some table) :
    (∀ n ∈ roots, ∃ axioms, table[n]? = some axioms) ∧
      ∀ n axioms, table[n]? = some axioms → ∀ a, a ∈ axioms ↔ ReachesAxiom find n a := by
  unfold axiomTable at h
  cases hs : searchEdges (successors find) fuel roots.toList with
  | none => simp [hs] at h
  | some forward =>
    obtain ⟨seen, edges⟩ := forward
    obtain ⟨complete, sound, hasEdge, edgeOK⟩ := searchEdges_some hs
    let back := fun y => ((predecessors edges).getD y []).toArray
    cases hb : searchBack back fuel (seen.toList.filter (isAxiomIn find)) with
    | none => simp [hs, hb, back] at h
    | some found =>
      simp only [hs, hb, back, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
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
        have after : ∀ x y, x ∈ back y → y ∈ successors find x := by
          intro x y hx
          simp only [back, List.mem_toArray, mem_predecessors] at hx
          obtain ⟨e, he, rfl, hy⟩ := hx
          rwa [edgeOK e he] at hy
        have before : ∀ x ∈ seen, ∀ y ∈ successors find x, x ∈ back y := by
          intro x hx y hy
          obtain ⟨e, he, rfl⟩ := hasEdge x hx
          simp only [back, List.mem_toArray, mem_predecessors]
          exact ⟨e, he, rfl, (edgeOK e he) ▸ hy⟩
        have closed : ∀ x ∈ seen, ∀ y ∈ successors find x, y ∈ seen := by
          intro x hx y hy
          obtain ⟨s, hs, hr⟩ := sound x hx
          exact complete s hs y (hr.tail hy)
        obtain ⟨searched, entries⟩ := searchBack_some hb
        simp only [reachedFrom, List.mem_toArray, List.mem_filterMap,
          Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists, ReachesAxiom]
        constructor
        · rintro ⟨b, reaching, hentry, hcontains, rfl⟩
          obtain ⟨haxiom, hsearch⟩ := entries _ hentry
          obtain ⟨-, hfound⟩ := search_some hsearch
          obtain ⟨s, hs, hr⟩ := hfound n (Std.HashSet.mem_iff_contains.mpr hcontains)
          rw [List.mem_singleton.mp hs] at hr
          simp only [List.mem_filter, isAxiomIn_iff] at haxiom
          exact ⟨reach_forward after hr, haxiom.2⟩
        · rintro ⟨hr, hax⟩
          have haxiom : a ∈ seen.toList.filter (isAxiomIn find) := by
            simp only [List.mem_filter, Std.HashSet.mem_toList, isAxiomIn_iff]
            obtain ⟨s, hs, hsr⟩ := sound n hseen
            exact ⟨complete s hs a (hsr.trans hr), hax⟩
          obtain ⟨reaching, hentry, hsearch⟩ := searched a haxiom
          have hback : Reach back a n := reach_back closed before hseen hr
          exact ⟨a, reaching, hentry,
            Std.HashSet.mem_iff_contains.mp ((search_some hsearch).1 a List.mem_cons_self n hback),
            rfl⟩
      · simp [hseen] at hn

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

/-- The axioms `n` reaches in `find`, read through the table `cached`: the search from `n` stops
at each name `cached` holds and takes that name's entry, and takes each other name it reaches
that `find` holds as an axiom. `none` when the search runs out of `fuel`. -/
def axiomsWith (find : Name → Option ConstantInfo) (cached : Std.HashMap Name (Array Name))
    (fuel : Nat) (n : Name) : Option (Array Name) :=
  (search (stopAt cached (successors find)) fuel [n]).map fun seen =>
    (seen.toList.flatMap fun m => match cached[m]? with
      | some axioms => axioms.toList
      | none => if isAxiomIn find m then [m] else []).toArray

/-- Reachability along a relation is reachability along any relation that has its steps. -/
theorem Reach.mono {next next' : Name → Array Name} (sub : ∀ x m, m ∈ next x → m ∈ next' x)
    {x y : Name} (h : Reach next x y) : Reach next' x y := by
  induction h with
  | refl => exact .refl _
  | step hm _ ih => exact .step (sub _ _ hm) ih

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
    have stopSub : ∀ x m, m ∈ stopAt cached (successors find) x → m ∈ successors find x := by
      intro x m hm
      unfold stopAt at hm
      split at hm
      · simp at hm
      · exact hm
    have reachOf : ∀ m ∈ seen, Reach (successors find) n m := by
      intro m hm
      obtain ⟨s, hs, hr⟩ := sound m hm
      rw [List.mem_singleton.mp hs] at hr
      exact hr.mono stopSub
    intro a
    simp only [List.mem_toArray, List.mem_flatMap, Std.HashSet.mem_toList]
    constructor
    · rintro ⟨m, hm, ha⟩
      cases hc : cached[m]? with
      | some entry =>
        rw [hc] at ha
        obtain ⟨hr, hax⟩ := (correct m entry hc a).mp (Array.mem_toList_iff.mp ha)
        exact ⟨(reachOf m hm).trans hr, hax⟩
      | none =>
        rw [hc] at ha
        by_cases hax : isAxiomIn find m = true
        · simp only [hax, ↓reduceIte, List.mem_singleton] at ha
          subst ha
          exact ⟨reachOf a hm, (isAxiomIn_iff find a).mp hax⟩
        · simp [hax] at ha
    · rintro ⟨hr, hax⟩
      rcases reach_stop (cached := cached) hr with ⟨c, hcc, hrc, hca⟩ | ⟨hra, hna⟩
      · have hsome : (cached[c]?).isSome = true := by
          rw [← Std.HashMap.contains_eq_isSome_getElem?]
          exact hcc
        obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hsome
        refine ⟨c, complete n List.mem_cons_self c hrc, ?_⟩
        rw [hentry]
        exact Array.mem_toList_iff.mpr ((correct c entry hentry a).mpr ⟨hca, hax⟩)
      · refine ⟨a, complete n List.mem_cons_self a hra, ?_⟩
        have hnone : cached[a]? = none := by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hna
          simpa using hna
        rw [hnone]
        simp [(isAxiomIn_iff find a).mpr hax]

/-- A bound on the names a search in `env` expands: one for each constant of its modules and of
the current module, and `extra` more. Every name a constant of a kernel environment uses is a
constant of it. -/
def fuelFor (env : Environment) (extra : Nat) : Nat :=
  env.header.moduleData.foldl (fun total data => total + data.constants.size) 0 +
    env.constants.map₂.foldl (fun total _ _ => total + 1) 0 + extra

end RegulaPolicy.KernelAxioms
