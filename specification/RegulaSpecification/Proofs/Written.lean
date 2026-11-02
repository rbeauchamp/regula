import RegulaSpecification.Effects

/-!
# What the run's own acts leave in the tree
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect

variable {L E : Type}

/-- What the acts of `t` leave at the path with the components `p`, from `held`. -/
def leavesFrom (t : List (Event L E)) (p : List String) (held : Option String) : Option String :=
  t.foldl (fun held e => e.leaves p held) held

theorem written_eq (t : List (Event L E)) (p : List String) : written t p = leavesFrom t p none := rfl

theorem leavesFrom_append (a b : List (Event L E)) (p : List String) (held : Option String) :
    leavesFrom (a ++ b) p held = leavesFrom b p (leavesFrom a p held) := by
  simp [leavesFrom, List.foldl_append]

theorem written_append (a b : List (Event L E)) (p : List String) :
    written (a ++ b) p = leavesFrom b p (written a p) :=
  leavesFrom_append a b p none

/-- What a list of writes leaves at the path with the components `p`, from `held`. -/
def writesOf (l : List (FilePath × String)) (p : List String) (held : Option String) : Option String :=
  l.foldl (fun held x => if parts x.1 = p then some x.2 else held) held

theorem writesOf_append (a b : List (FilePath × String)) (p : List String) (held : Option String) :
    writesOf (a ++ b) p held = writesOf b p (writesOf a p held) := by
  simp [writesOf, List.foldl_append]

theorem writesOf_agree {l : List (FilePath × String)} {p : List String} {v : String} {held : Option String}
    (hall : ∀ y ∈ l, parts y.1 = p → y.2 = v) (hsome : held = some v ∨ ∃ y ∈ l, parts y.1 = p) :
    writesOf l p held = some v := by
  induction l generalizing held with
  | nil =>
    rcases hsome with rfl | ⟨y, hy, -⟩
    · rfl
    · cases hy
  | cons a l ih =>
    have hrest : ∀ y ∈ l, parts y.1 = p → y.2 = v := fun y hy => hall y (List.mem_cons_of_mem _ hy)
    simp only [writesOf, List.foldl_cons]
    by_cases ha : parts a.1 = p
    · simp only [ha, ↓reduceIte, hall a (List.mem_cons_self ..) ha]
      exact ih hrest (.inl rfl)
    · simp only [ha, ↓reduceIte]
      refine ih hrest ?_
      rcases hsome with h | ⟨y, hy, hp⟩
      · exact .inl h
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd hp ha
        · exact .inr ⟨y, hy, hp⟩

theorem writesOf_mem {l : List (FilePath × String)} {p : List String} {v : String} {held : Option String}
    (h : writesOf l p held = some v) : held = some v ∨ ∃ x ∈ l, parts x.1 = p ∧ x.2 = v := by
  induction l generalizing held with
  | nil => exact .inl h
  | cons a l ih =>
    simp only [writesOf, List.foldl_cons] at h
    by_cases ha : parts a.1 = p
    · simp only [ha, ↓reduceIte] at h
      rcases ih h with he | ⟨x, hx, h1, h2⟩
      · exact .inr ⟨a, List.mem_cons_self .., ha, Option.some.inj he⟩
      · exact .inr ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩
    · simp only [ha, ↓reduceIte] at h
      rcases ih h with he | ⟨x, hx, h1, h2⟩
      · exact .inl he
      · exact .inr ⟨x, List.mem_cons_of_mem _ hx, h1, h2⟩

/-- The segment `t` acts on files exactly as the list `l` of writes does. -/
def LeavesAs (t : List (Event L E)) (l : List (FilePath × String)) : Prop :=
  ∀ p held, leavesFrom t p held = writesOf l p held

theorem LeavesAs.append {a b : List (Event L E)} {x y : List (FilePath × String)} (ha : LeavesAs a x) (hb : LeavesAs b y) :
    LeavesAs (a ++ b) (x ++ y) := by
  intro p held
  rw [leavesFrom_append, writesOf_append, ha, hb]

/-- An event that requests no write and no removal. What a Lake command does inside itself is not read here. -/
def Event.keepsFiles (e : Event L E) : Prop :=
  match e.op with
  | .writeFile .. | .removeDirAll _ => False
  | _ => True

theorem Event.leaves_of_keeps {e : Event L E} (h : e.keepsFiles) (p : List String) (held : Option String) :
    e.leaves p held = held := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | rfl | exact h.elim

theorem keeps_of_no_acts {e : Event L E} (h : e.acted? = none) : e.keepsFiles := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | trivial | cases h

theorem leavesAs_nil_of_keeps {t : List (Event L E)} (h : ∀ e ∈ t, e.keepsFiles) : LeavesAs t [] := by
  intro p held
  induction t generalizing held with
  | nil => rfl
  | cons e t ih =>
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [leavesFrom, List.foldl_cons]
    rw [Event.leaves_of_keeps (h e (List.mem_cons_self ..))]
    exact hrest held

theorem leavesAs_nil_of_no_act {t : List (Event L E)} (h : ∀ e ∈ t, e.acted? = none) : LeavesAs t [] := by
  refine leavesAs_nil_of_keeps fun e he => ?_
  have hne := h e he
  obtain ⟨o, r⟩ := e
  cases o <;> first | trivial | cases hne

theorem leavesAs_write {before : List (Event L E)} {path : FilePath} {text : String} {r : Except IO.Error Unit}
    (h : ∀ e ∈ before, ∃ d, e = (⟨.createDirAll d, .ok ()⟩ : Event L E)) :
    LeavesAs (before ++ [⟨.writeFile path text, r⟩]) [(path, text)] := by
  intro p held
  rw [leavesFrom_append]
  have hb : leavesFrom before p held = held := by
    clear r
    induction before generalizing held with
    | nil => rfl
    | cons e t ih =>
      obtain ⟨d, rfl⟩ := h e (List.mem_cons_self ..)
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) held
  rw [hb]
  rfl

/-- Each write that a segment asks is one of a list. -/
def WritesIn (t : List (Event L E)) (l : List (FilePath × String)) : Prop :=
  ∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ t → (path, text) ∈ l

theorem WritesIn.append {a b : List (Event L E)} {x y : List (FilePath × String)} (ha : WritesIn a x) (hb : WritesIn b y) :
    WritesIn (a ++ b) (x ++ y) := by
  intro path text r he
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (ha path text r he)
  · exact List.mem_append_right _ (hb path text r he)

theorem writesIn_nil_of_no_act {t : List (Event L E)} (h : ∀ e ∈ t, e.acted? = none) : WritesIn t [] := by
  intro path text r he
  cases h _ he

theorem writesIn_write {before : List (Event L E)} {path : FilePath} {text : String} {r : Except IO.Error Unit}
    (h : ∀ e ∈ before, ∃ d, e = (⟨.createDirAll d, .ok ()⟩ : Event L E)) :
    WritesIn (before ++ [⟨.writeFile path text, r⟩]) [(path, text)] := by
  intro p x r' he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨d, hd⟩ := h _ he
    cases congrArg Event.op hd
  · have hop := congrArg Event.op (List.mem_singleton.mp he)
    cases hop
    exact List.mem_singleton.mpr rfl

theorem LeavesAs.written {t : List (Event L E)} {l : List (FilePath × String)} (h : LeavesAs t l) (p : List String) :
    Effects.written t p = writesOf l p none :=
  h p none

theorem written_after_no_acts {a b : List (Event L E)} (ha : ∀ e ∈ a, e.acted? = none) (p : List String) :
    Effects.written (a ++ b) p = Effects.written b p := by
  rw [written_append]
  have h := leavesAs_nil_of_no_act ha p none
  rw [written_eq, h]
  rfl

theorem written_before_no_acts {a b : List (Event L E)} (hb : ∀ e ∈ b, e.acted? = none) (p : List String) :
    Effects.written (a ++ b) p = Effects.written a p := by
  rw [written_append]
  have h := leavesAs_nil_of_no_act hb p (Effects.written a p)
  rw [h]
  rfl

theorem written_last_write (a b : List (Event L E)) (path : FilePath) (text : String) (r : Except IO.Error Unit)
    (hb : LeavesAs b []) : Effects.written (a ++ ⟨.writeFile path text, r⟩ :: b) (parts path) = some text := by
  rw [written_append]
  have hs : leavesFrom (⟨.writeFile path text, r⟩ :: b) (parts path) (written a (parts path)) =
      leavesFrom b (parts path) (some text) := by
    simp [leavesFrom, Event.leaves]
  rw [hs, hb]
  rfl

end RegulaSpecification.Effects
