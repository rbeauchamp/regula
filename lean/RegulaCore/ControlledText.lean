/-! # The words and the sentences of prose

The writing guide (`docs/guides/writing.md`) limits the number of words of a sentence and the
number of sentences of a paragraph. This module defines what a word and a sentence are, for the
vocabulary of a project (`RegulaCore.Vocabulary`) and for the checks of Markdown prose. It is one
definition for each reader of prose, so a cell of the vocabulary and a paragraph of a document
are counted alike.

## The definition

The definition is four divisions, each stated as a relation between a text and its parts:

1. `Runs Joins`: the atoms of a text divided into tokens. A token is a maximal run of atoms in
   which each two atoms next to each other are joined (`Joins`).
2. `Folded` for quotation marks: the tokens from a quotation mark that has a later one to the
   next quotation mark are one quotation.
3. `Folded` for parentheses: the items from an opening parenthesis whose next parenthesis is a
   closing one to that closing parenthesis are one group.
4. `Runs Flows`: the parts outside the groups, and the items of each group apart (`spread`),
   divided after each end of a sentence (`Part.Ends`, `Part.Starts`).

`Divided` puts the four together. A sentence is a run of the last division that has a word
(`Worded`), and its number of words is the number of its slots that are words (`Part.Word`).

## The functions

`runs`, `fold` and `divide` compute the divisions. Each relation holds of one result only, the
one its function computes: `runs_iff`, `folded_iff` and `divided_iff`. A specification is stated
with the relations, and a check runs the functions.

Two theorems say what a token of letters is. A token that has a letter, a digit, a hyphen or an
apostrophe has only such characters (`Runs.wordy`), and each letter, each digit, each piece of
code and each counted character outside ASCII is in a token that is a word (`Runs.counted`).

## What the definition is not

No theorem here says that a sentence of this definition is a sentence for a reader, or that a
word here is a word of a dictionary. The writing guide gives the cases where the two differ.
-/

namespace Regula.Controlled

/-! ## Maximal runs -/

/-- `parts` is `text` divided into its maximal runs for `R`: the parts in order are the text, no
part is empty, two elements next to each other in a part are related by `R`, and the last
element of a part is not related to the first element of the next part. -/
structure Runs {α : Type} (R : α → α → Prop) (text : List α) (parts : List (List α)) :
    Prop where
  /-- The parts in order are the text. -/
  flatten : parts.flatten = text
  /-- No part is empty. -/
  nonempty : ∀ part ∈ parts, part ≠ []
  /-- Two elements next to each other in a part are related. -/
  joined : ∀ part ∈ parts, ∀ before a b after, part = before ++ a :: b :: after → R a b
  /-- The last element of a part is not related to the first element of the next part. -/
  apart : ∀ before first second after, parts = before ++ first :: second :: after →
    ∀ a b, first.getLast? = some a → second.head? = some b → ¬R a b

/-- `text` divided into its maximal runs for `R`. -/
def runs {α : Type} (R : α → α → Prop) [DecidableRel R] : List α → List (List α)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest =>
    if R a b then
      match runs R (b :: rest) with
      | run :: more => (a :: run) :: more
      | [] => [[a]]
    else [a] :: runs R (b :: rest)

section Runs

variable {α : Type} {R : α → α → Prop}

/-- A division that starts with an element starts with a part that starts with it. -/
theorem Runs.head {a : α} {text : List α} {parts : List (List α)} (h : Runs R (a :: text) parts) :
    ∃ run more, parts = (a :: run) :: more := by
  cases parts with
  | nil => exact absurd h.flatten (by simp)
  | cons part more =>
    cases part with
    | nil => exact absurd rfl (h.nonempty [] (List.mem_cons_self ..))
    | cons c run =>
      have hflat := h.flatten
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hflat
      exact ⟨run, more, by rw [hflat.1]⟩

/-- A division without its first part divides the text after that part. -/
theorem Runs.tail {part text : List α} {parts : List (List α)}
    (h : Runs R (part ++ text) (part :: parts)) : Runs R text parts where
  flatten := by simpa using h.flatten
  nonempty := fun p hp => h.nonempty p (List.mem_cons_of_mem _ hp)
  joined := fun p hp => h.joined p (List.mem_cons_of_mem _ hp)
  apart := fun before first second after hsplit =>
    h.apart (part :: before) first second after (by rw [hsplit, List.cons_append])

/-- An element that is related to the next one goes into the part of the next one. -/
theorem Runs.join {a b : α} {rest run : List α} {more : List (List α)} (hab : R a b)
    (h : Runs R (b :: rest) ((b :: run) :: more)) :
    Runs R (a :: b :: rest) ((a :: b :: run) :: more) where
  flatten := by simpa using h.flatten
  nonempty := by
    intro part hpart
    rcases List.mem_cons.mp hpart with rfl | hpart
    · simp
    · exact h.nonempty part (List.mem_cons_of_mem _ hpart)
  joined := by
    intro part hpart before x y after hsplit
    rcases List.mem_cons.mp hpart with rfl | hpart
    · cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, rfl, -⟩ := hsplit
        exact hab
      | cons c before =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        exact h.joined _ (List.mem_cons_self ..) before x y after hsplit.2
    · exact h.joined part (List.mem_cons_of_mem _ hpart) before x y after hsplit
  apart := by
    intro before first second after hsplit x y hx hy
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      rw [List.getLast?_cons_cons] at hx
      exact h.apart [] (b :: run) second after rfl x y hx hy
    | cons c before =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      exact h.apart ((b :: run) :: before) first second after rfl x y hx hy

/-- An element that is not related to the next one is a part of its own. -/
theorem Runs.cut {a b : α} {rest run : List α} {more : List (List α)} (hab : ¬R a b)
    (h : Runs R (b :: rest) ((b :: run) :: more)) :
    Runs R (a :: b :: rest) ([a] :: (b :: run) :: more) where
  flatten := by simpa using h.flatten
  nonempty := by
    intro part hpart
    rcases List.mem_cons.mp hpart with rfl | hpart
    · simp
    · exact h.nonempty part hpart
  joined := by
    intro part hpart before x y after hsplit
    rcases List.mem_cons.mp hpart with rfl | hpart
    · cases before <;> simp at hsplit
    · exact h.joined part hpart before x y after hsplit
  apart := by
    intro before first second after hsplit x y hx hy
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl, -⟩ := hsplit
      simp only [List.getLast?_singleton, Option.some.injEq, List.head?_cons] at hx hy
      subst hx hy
      exact hab
    | cons c before =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      exact h.apart before first second after hsplit.2 x y hx hy

/-- The first element of a part with two elements or more is related to the second, and the
division without that first element divides the text without it. -/
theorem Runs.of_join {a b : α} {rest run : List α} {more : List (List α)}
    (h : Runs R (a :: b :: rest) ((a :: b :: run) :: more)) :
    R a b ∧ Runs R (b :: rest) ((b :: run) :: more) := by
  refine ⟨h.joined _ (List.mem_cons_self ..) [] a b run rfl, ?_, ?_, ?_, ?_⟩
  · simpa using h.flatten
  · intro part hpart
    rcases List.mem_cons.mp hpart with rfl | hpart
    · simp
    · exact h.nonempty part (List.mem_cons_of_mem _ hpart)
  · intro part hpart before x y after hsplit
    rcases List.mem_cons.mp hpart with rfl | hpart
    · exact h.joined _ (List.mem_cons_self ..) (a :: before) x y after (by rw [hsplit]; rfl)
    · exact h.joined part (List.mem_cons_of_mem _ hpart) before x y after hsplit
  · intro before first second after hsplit x y hx hy
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      exact h.apart [] (a :: b :: run) second after rfl x y
        (by rw [List.getLast?_cons_cons]; exact hx) hy
    | cons c before =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      exact h.apart ((a :: b :: run) :: before) first second after rfl x y hx hy

/-- The computed division starts with a part that starts with the first element. -/
theorem runs_cons [DecidableRel R] (a : α) (text : List α) :
    ∃ run more, runs R (a :: text) = (a :: run) :: more := by
  cases text with
  | nil => exact ⟨[], [], rfl⟩
  | cons b rest =>
    by_cases hab : R a b
    · cases hrest : runs R (b :: rest) with
      | nil => exact ⟨[], [], by simp [runs, hab, hrest]⟩
      | cons run more => exact ⟨run, more, by simp [runs, hab, hrest]⟩
    · exact ⟨[], runs R (b :: rest), by simp [runs, hab]⟩

/-- The computed division is the division into maximal runs. -/
theorem runs_spec [DecidableRel R] : ∀ text : List α, Runs R text (runs R text)
  | [] => ⟨rfl, by simp [runs], by simp [runs], by simp [runs]⟩
  | [a] => by
    refine ⟨rfl, by simp [runs], ?_, ?_⟩
    · intro part hpart before x y after hsplit
      simp only [runs, List.mem_singleton] at hpart
      subst hpart
      cases before <;> simp at hsplit
    · intro before first second after hsplit
      cases before <;> simp [runs] at hsplit
  | a :: b :: rest => by
    have ih := runs_spec (b :: rest)
    obtain ⟨run, more, hrest⟩ := runs_cons (R := R) b rest
    rw [hrest] at ih
    by_cases hab : R a b
    · have : runs R (a :: b :: rest) = (a :: b :: run) :: more := by simp [runs, hab, hrest]
      rw [this]
      exact ih.join hab
    · have : runs R (a :: b :: rest) = [a] :: (b :: run) :: more := by simp [runs, hab, hrest]
      rw [this]
      exact ih.cut hab

/-- A division into maximal runs is the computed one. -/
theorem Runs.eq_runs [DecidableRel R] :
    ∀ (text : List α) (parts : List (List α)), Runs R text parts → parts = runs R text
  | [], parts, h => by
    cases parts with
    | nil => rfl
    | cons part more =>
      have hflat := h.flatten
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hflat
      exact absurd hflat.1 (h.nonempty part (List.mem_cons_self ..))
  | [a], parts, h => by
    obtain ⟨run, more, rfl⟩ := h.head
    have hflat := h.flatten
    simp only [List.flatten_cons, List.cons_append, List.cons.injEq, true_and,
      List.append_eq_nil_iff] at hflat
    obtain ⟨rfl, hmore⟩ := hflat
    cases more with
    | nil => rfl
    | cons part more =>
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hmore
      exact absurd hmore.1 (h.nonempty part (by simp))
  | a :: b :: rest, parts, h => by
    obtain ⟨run, more, rfl⟩ := h.head
    cases run with
    | nil =>
      have htail : Runs R (b :: rest) more := Runs.tail (part := [a]) h
      obtain ⟨run, more, rfl⟩ := htail.head
      have hab : ¬R a b := h.apart [] [a] (b :: run) more rfl a b rfl rfl
      have := Runs.eq_runs (b :: rest) _ htail
      simp [runs, hab, ← this]
    | cons c run =>
      have hflat := h.flatten
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq, true_and] at hflat
      obtain ⟨rfl, -⟩ := hflat
      obtain ⟨hab, htail⟩ := h.of_join
      have := Runs.eq_runs (c :: rest) _ htail
      simp [runs, hab, ← this]

/-- The division into maximal runs holds of one result only: the computed one. -/
theorem runs_iff [DecidableRel R] (text : List α) (parts : List (List α)) :
    Runs R text parts ↔ parts = runs R text :=
  ⟨Runs.eq_runs text parts, fun h => h ▸ runs_spec text⟩

/-- Elements next to each other that are all related agree on a property that two related
elements have together. -/
theorem uniform_of_joined {P : α → Prop} (hR : ∀ a b, R a b → (P a ↔ P b)) :
    ∀ part : List α, (∀ before a b after, part = before ++ a :: b :: after → R a b) →
      ∀ a ∈ part, ∀ b ∈ part, (P a ↔ P b)
  | [], _ => by simp
  | [c], _ => by
    intro a ha b hb
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]
  | c :: d :: rest, hjoined => by
    have hcd := hR c d (hjoined [] c d rest rfl)
    have ih := uniform_of_joined hR (d :: rest) fun before a b after hsplit =>
      hjoined (c :: before) a b after (by rw [hsplit]; rfl)
    have key : ∀ x ∈ c :: d :: rest, (P x ↔ P d) := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hcd
      · exact ih x hx d (List.mem_cons_self ..)
    intro a ha b hb
    exact (key a ha).trans (key b hb).symm

/-- The elements of one part of a division agree on a property that two related elements have
together: all of them have it, or none. -/
theorem Runs.uniform {P : α → Prop} (hR : ∀ a b, R a b → (P a ↔ P b)) {text : List α}
    {parts : List (List α)} (h : Runs R text parts) :
    ∀ part ∈ parts, ∀ a ∈ part, ∀ b ∈ part, (P a ↔ P b) :=
  fun part hpart => uniform_of_joined hR part (h.joined part hpart)

end Runs

/-! ## Folds -/

/-- One element, or the elements from one that opens to the one that closes it. -/
inductive Fold (α : Type) where
  /-- One element. -/
  | one (item : α)
  /-- The element that opens, the elements between, and the element that closes. -/
  | many (first : α) (inside : List α) (last : α)
  deriving DecidableEq, Repr

/-- `folds` is `text` with each closed sequence as one fold: an element that opens, then
elements that neither open nor close, then an element that closes. Each element that starts no
such sequence is alone, and the text after a fold is read in the same way. -/
inductive Folded {α : Type} (Opens Closes : α → Prop) : List α → List (Fold α) → Prop
  /-- The empty text has no fold. -/
  | nil : Folded Opens Closes [] []
  /-- An element is alone when it does not open, or when the first later element that opens or
  closes does not close. -/
  | one {item : α} {rest : List α} {folds : List (Fold α)} :
    (Opens item → ∀ inside last after, rest = inside ++ last :: after →
      (∀ x ∈ inside, ¬Opens x ∧ ¬Closes x) → ¬Closes last) →
    Folded Opens Closes rest folds → Folded Opens Closes (item :: rest) (.one item :: folds)
  /-- An element that opens, elements that neither open nor close, and an element that closes
  are one fold. -/
  | many {first : α} {inside : List α} {last : α} {after : List α} {folds : List (Fold α)} :
    Opens first → (∀ x ∈ inside, ¬Opens x ∧ ¬Closes x) → Closes last →
    Folded Opens Closes after folds →
    Folded Opens Closes (first :: (inside ++ last :: after)) (.many first inside last :: folds)

/-- The elements of `text` before the first one that opens or closes, and that one. -/
def ahead {α : Type} (Opens Closes : α → Prop) [DecidablePred Opens] [DecidablePred Closes] :
    List α → Option (List α × α)
  | [] => none
  | x :: rest =>
    if Opens x ∨ Closes x then some ([], x)
    else (ahead Opens Closes rest).map fun found => (x :: found.1, found.2)

/-- The folds of `text`. With `skip`, the text is read from after its first element that opens or
closes: the rest of a fold that is in progress. -/
def foldFrom {α : Type} (Opens Closes : α → Prop) [DecidablePred Opens] [DecidablePred Closes] :
    Bool → List α → List (Fold α)
  | _, [] => []
  | true, x :: rest =>
    if Opens x ∨ Closes x then foldFrom Opens Closes false rest
    else foldFrom Opens Closes true rest
  | false, item :: rest =>
    match (if Opens item then ahead Opens Closes rest else none) with
    | some (inside, last) =>
      if Closes last then .many item inside last :: foldFrom Opens Closes true rest
      else .one item :: foldFrom Opens Closes false rest
    | none => .one item :: foldFrom Opens Closes false rest

/-- `text` with each closed sequence as one fold. -/
def fold {α : Type} (Opens Closes : α → Prop) [DecidablePred Opens] [DecidablePred Closes]
    (text : List α) : List (Fold α) :=
  foldFrom Opens Closes false text

section Fold

variable {α : Type} {Opens Closes : α → Prop} [DecidablePred Opens] [DecidablePred Closes]

/-- `ahead` finds exactly the first element that opens or closes, with the elements before
it. -/
theorem ahead_eq_some (text inside : List α) (last : α) :
    ahead Opens Closes text = some (inside, last) ↔
      ∃ after, text = inside ++ last :: after ∧ (∀ x ∈ inside, ¬Opens x ∧ ¬Closes x) ∧
        (Opens last ∨ Closes last) := by
  induction text generalizing inside with
  | nil => simp [ahead]
  | cons x rest ih =>
    by_cases hx : Opens x ∨ Closes x
    · simp only [ahead, hx, ite_true, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rest, rfl, by simp, hx⟩
      · rintro ⟨after, hsplit, hinside, -⟩
        cases inside with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          exact ⟨rfl, hsplit.1⟩
        | cons y inside =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, -⟩ := hsplit
          have := hinside x (List.mem_cons_self ..)
          exact absurd hx (by simp [this.1, this.2])
    · simp only [ahead, hx, ite_false, Option.map_eq_some_iff]
      constructor
      · rintro ⟨found, hfound, hpair⟩
        cases found with
        | mk found last' =>
          simp only [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          obtain ⟨after, rfl, hinside, hlast⟩ := (ih found).mp hfound
          refine ⟨after, rfl, ?_, hlast⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact not_or.mp hx
          · exact hinside y hy
      · rintro ⟨after, hsplit, hinside, hlast⟩
        cases inside with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, -⟩ := hsplit
          exact absurd hlast hx
        | cons y inside =>
          simp only [List.cons_append, List.cons.injEq] at hsplit
          obtain ⟨rfl, rfl⟩ := hsplit
          exact ⟨(inside, last), (ih inside).mpr ⟨after, rfl,
            fun z hz => hinside z (List.mem_cons_of_mem _ hz), hlast⟩, rfl⟩

/-- The rest of a fold in progress is read to its closing element, and then the text after it
is read from the start. -/
theorem foldFrom_skip {inside : List α} {last : α} (after : List α)
    (hinside : ∀ x ∈ inside, ¬Opens x ∧ ¬Closes x) (hlast : Opens last ∨ Closes last) :
    foldFrom Opens Closes true (inside ++ last :: after) = foldFrom Opens Closes false after := by
  induction inside with
  | nil => simp [foldFrom, hlast]
  | cons x inside ih =>
    have hx := hinside x (List.mem_cons_self ..)
    simp only [List.cons_append, foldFrom, hx.1, hx.2, or_self, ite_false]
    exact ih fun y hy => hinside y (List.mem_cons_of_mem _ hy)

/-- The folds of a text are the computed ones. -/
theorem Folded.eq_fold {text : List α} {folds : List (Fold α)}
    (h : Folded Opens Closes text folds) : folds = fold Opens Closes text := by
  induction h with
  | nil => rfl
  | @one item rest folds halone _ ih =>
    rw [ih]
    by_cases hitem : Opens item
    · cases hahead : ahead Opens Closes rest with
      | none => simp [fold, foldFrom, hitem, hahead]
      | some found =>
        cases found with
        | mk inside last =>
          obtain ⟨after, hsplit, hinside, -⟩ := (ahead_eq_some rest inside last).mp hahead
          have hlast := halone hitem inside last after hsplit hinside
          simp [fold, foldFrom, hitem, hahead, hlast]
    · simp [fold, foldFrom, hitem]
  | @many first inside last after folds hfirst hinside hlast _ ih =>
    rw [ih]
    have hahead : ahead Opens Closes (inside ++ last :: after) = some (inside, last) :=
      (ahead_eq_some _ inside last).mpr ⟨after, rfl, hinside, .inr hlast⟩
    simp [fold, foldFrom, hfirst, hahead, hlast, foldFrom_skip after hinside (.inr hlast)]

/-- The computed folds are the folds of the text. -/
theorem folded_fold (text : List α) : Folded Opens Closes text (fold Opens Closes text) := by
  suffices h : ∀ n (text : List α), text.length ≤ n →
      Folded Opens Closes text (foldFrom Opens Closes false text) from h _ text (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro text hlength
    have : text = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlength)
    subst this
    exact .nil
  | succ n ih =>
    intro text hlength
    cases text with
    | nil => exact .nil
    | cons item rest =>
      have hrest : rest.length ≤ n := by simpa using hlength
      by_cases hitem : Opens item
      · cases hahead : ahead Opens Closes rest with
        | none =>
          have : foldFrom Opens Closes false (item :: rest) =
              .one item :: foldFrom Opens Closes false rest := by
            simp [foldFrom, hitem, hahead]
          rw [this]
          refine .one (fun _ inside last after hsplit hinside hlast => ?_) (ih rest hrest)
          have := (ahead_eq_some rest inside last).mpr ⟨after, hsplit, hinside, .inr hlast⟩
          rw [hahead] at this
          cases this
        | some found =>
          cases found with
          | mk inside last =>
            obtain ⟨after, hsplit, hinside, hbracket⟩ :=
              (ahead_eq_some rest inside last).mp hahead
            by_cases hlast : Closes last
            · have : foldFrom Opens Closes false (item :: rest) =
                  .many item inside last :: foldFrom Opens Closes false after := by
                simp only [foldFrom, hitem, ite_true, hahead, hlast]
                rw [hsplit, foldFrom_skip after hinside hbracket]
              rw [this, hsplit]
              refine .many hitem hinside hlast (ih after ?_)
              have : after.length ≤ rest.length := by
                rw [hsplit]
                simp only [List.length_append, List.length_cons]
                omega
              omega
            · have : foldFrom Opens Closes false (item :: rest) =
                  .one item :: foldFrom Opens Closes false rest := by
                simp [foldFrom, hitem, hahead, hlast]
              rw [this]
              refine .one (fun _ inside' last' after' hsplit' hinside' hlast' => ?_)
                (ih rest hrest)
              have := (ahead_eq_some rest inside' last').mpr
                ⟨after', hsplit', hinside', .inr hlast'⟩
              rw [hahead] at this
              cases this
              exact hlast hlast'
      · have : foldFrom Opens Closes false (item :: rest) =
            .one item :: foldFrom Opens Closes false rest := by
          simp [foldFrom, hitem]
        rw [this]
        exact .one (fun h => absurd h hitem) (ih rest hrest)

/-- The folds of a text are one result only: the computed one. -/
theorem folded_iff (text : List α) (folds : List (Fold α)) :
    Folded Opens Closes text folds ↔ folds = fold Opens Closes text :=
  ⟨Folded.eq_fold, fun h => h ▸ folded_fold text⟩

end Fold

/-! ## Atoms and their roles -/

/-- One character of prose (`some`), or one piece of code (`none`), with the place of its piece:
the number of located pieces of the document before it. -/
structure Atom where
  /-- The place of the piece the character or the code comes from. -/
  anchor : Nat
  /-- The character, or `none` for code. -/
  char : Option Char
  deriving DecidableEq, Repr

/-- The atom of a character of a text that has no pieces. -/
def Atom.plain (c : Char) : Atom := ⟨0, some c⟩

/-- What an atom is for the division of prose. -/
inductive Role where
  /-- An ASCII uppercase letter. -/
  | upper
  /-- An ASCII lowercase letter. -/
  | lower
  /-- An ASCII digit. -/
  | digit
  /-- A hyphen (`-`) or an apostrophe (`'`). -/
  | joiner
  /-- A space character (`Spacing`). -/
  | space
  /-- A period, a question mark or an exclamation mark. -/
  | stop
  /-- A double quotation mark: `"`, `“` or `”`. -/
  | quote
  /-- An opening parenthesis. -/
  | opening
  /-- A closing parenthesis. -/
  | closing
  /-- A piece of code. -/
  | code
  /-- A character outside ASCII that is not a known space or mark. It is a word of its own, so
  that no text has fewer words here than a reader counts. -/
  | symbol
  /-- Any other character. -/
  | mark
  deriving DecidableEq, Repr

/-- `c` is a space character: ASCII white space, or one of the space characters outside ASCII
that are known here (U+00A0, U+1680, U+2000 to U+200A, U+2028, U+2029, U+202F, U+205F and
U+3000). The class is a proposition, so a statement that uses it names no test of this module,
and a function decides it with its `Decidable` instance. -/
def Spacing (c : Char) : Prop :=
  c.isWhitespace = true ∨ c.val = 0xA0 ∨ c.val = 0x1680 ∨ (0x2000 ≤ c.val ∧ c.val ≤ 0x200A) ∨
    c.val = 0x2028 ∨ c.val = 0x2029 ∨ c.val = 0x202F ∨ c.val = 0x205F ∨ c.val = 0x3000

instance (c : Char) : Decidable (Spacing c) := by
  unfold Spacing
  infer_instance

/-- The role of a character. The known marks outside ASCII are `‘`, `’`, `–`, `—` and `…`. -/
def roleOf (c : Char) : Role :=
  if c.isUpper then .upper
  else if c.isLower then .lower
  else if c.isDigit then .digit
  else if c = '-' ∨ c = '\'' then .joiner
  else if Spacing c then .space
  else if c = '.' ∨ c = '?' ∨ c = '!' then .stop
  else if c = '"' ∨ c = '“' ∨ c = '”' then .quote
  else if c = '(' then .opening
  else if c = ')' then .closing
  else if c.val < 128 ∨ c = '‘' ∨ c = '’' ∨ c = '–' ∨ c = '—' ∨ c = '…' then .mark
  else .symbol

/-- The role of an atom. -/
def Atom.role (atom : Atom) : Role :=
  match atom.char with
  | none => .code
  | some c => roleOf c

/-- A role of a character of a word: a letter, a digit, a hyphen or an apostrophe. -/
abbrev Role.Wordy (role : Role) : Prop :=
  role = .upper ∨ role = .lower ∨ role = .digit ∨ role = .joiner

/-- A role that makes its token a word: a letter, a digit, a piece of code, or a character
outside ASCII that is not a known space or mark. -/
abbrev Role.Counted (role : Role) : Prop :=
  role = .upper ∨ role = .lower ∨ role = .digit ∨ role = .code ∨ role = .symbol

/-! ## Tokens, quotations and groups -/

/-- Two atoms next to each other are in one token: two characters of a word, two space
characters, two pieces of code, or a period, a question mark or an exclamation mark and a space
character after it. -/
abbrev Joins (a b : Atom) : Prop :=
  (a.role.Wordy ∧ b.role.Wordy) ∨ (a.role = .space ∧ b.role = .space) ∨
    (a.role = .code ∧ b.role = .code) ∨ (a.role = .stop ∧ b.role = .space)

/-- A token: a maximal run of joined atoms. -/
abbrev Token := List Atom

/-- A token that has a letter, a digit, a hyphen or an apostrophe has only such characters. Thus
a token with a letter or a digit is a maximal run of ASCII letters, digits, hyphens and
apostrophes. -/
theorem Runs.wordy {atoms : List Atom} {tokens : List Token} (h : Runs Joins atoms tokens) :
    ∀ token ∈ tokens, ∀ atom ∈ token, atom.role.Wordy → ∀ other ∈ token, other.role.Wordy := by
  intro token htoken atom hatom hwordy other hother
  refine (h.uniform (P := fun a => a.role.Wordy) ?_ token htoken atom hatom other hother).mp hwordy
  rintro a b (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) <;> simp [Role.Wordy, ha, hb]

/-- A token, or a quotation: the tokens from a quotation mark to the next one. -/
abbrev Item := Fold Token

/-- An item, or a group: the items from an opening parenthesis to its closing parenthesis. -/
abbrev Part := Fold Item

/-- The token has an atom with the role. -/
abbrev Token.Has (role : Role) (token : Token) : Prop := ∃ atom ∈ token, atom.role = role

/-- The token of an item that is no quotation. -/
def Item.token? : Item → Option Token
  | .one token => some token
  | .many .. => none

/-- The item is a token that has an atom with the role. A quotation has none: its marks and
its text are not read. -/
abbrev Item.Has (role : Role) (item : Item) : Prop := ∃ token ∈ item.token?, token.Has role

/-- The token of a part that is no quotation and no group. -/
def Part.token? : Part → Option Token
  | .one (.one token) => some token
  | _ => none

/-- The part is one word: a token with a letter, a digit, a piece of code or a character outside
ASCII that is not a known space or mark; a quotation; or a group. -/
abbrev Part.Word (part : Part) : Prop :=
  ∀ token ∈ part.token?, ∃ atom ∈ token, atom.role.Counted

/-- The part can end a sentence: a token with a period, a question mark or an exclamation mark,
and a space character after it. -/
abbrev Part.Ends (part : Part) : Prop :=
  ∃ token ∈ part.token?, token.Has .stop ∧ token.Has .space

/-- The part can start a sentence: a token that starts with an ASCII uppercase letter, a digit,
a piece of code or an opening parenthesis; a quotation; or a group. -/
abbrev Part.Starts (part : Part) : Prop :=
  ∀ token ∈ part.token?,
    ∃ role ∈ [Role.upper, .digit, .code, .opening], token.head?.map Atom.role = some role

/-! ## Sentences -/

/-- The parts outside the groups in order, and then the items of each group in order, with a
`none` before each group: the regions in which sentences are read. A group is one part of the
region around it, and its items are a region of their own. -/
def spread (parts : List Part) : List (Option Part) :=
  parts.map some ++ parts.flatMap fun
    | .one _ => []
    | .many _ inside _ => none :: inside.map fun item => some (.one item)

/-- Two slots next to each other are in one sentence: two parts of one region, unless the first
can end a sentence and the second can start one. -/
abbrev Flows (a b : Option Part) : Prop := ∃ p ∈ a, ∃ q ∈ b, ¬(p.Ends ∧ q.Starts)

instance : DecidableRel Flows := fun _ _ => inferInstance

/-- The slot is a word. -/
abbrev Slot.Word (slot : Option Part) : Prop := ∃ part ∈ slot, part.Word

/-- The run has a word: it is a sentence. -/
abbrev Worded (run : List (Option Part)) : Prop := ∃ slot ∈ run, Slot.Word slot

/-- The number of words of a run. -/
def wordCount (run : List (Option Part)) : Nat := run.countP fun slot => decide (Slot.Word slot)

/-- `cut` is the division of `atoms` into the runs that sentences are: the atoms divided into
tokens, the tokens folded into quotations, the items folded into groups, and the regions divided
after each end of a sentence. -/
def Divided (atoms : List Atom) (cut : List (List (Option Part))) : Prop :=
  ∃ tokens items parts, Runs Joins atoms tokens ∧
    Folded (Token.Has .quote) (Token.Has .quote) tokens items ∧
    Folded (Item.Has .opening) (Item.Has .closing) items parts ∧
    Runs Flows (spread parts) cut

/-- Each atom with a counted role is in a token that is a word: no letter, no digit, no piece of
code and no character outside ASCII that is not a known space or mark is outside the words of
the tokens. -/
theorem Runs.counted {atoms : List Atom} {tokens : List Token} (h : Runs Joins atoms tokens) :
    ∀ atom ∈ atoms, atom.role.Counted →
      ∃ token ∈ tokens, atom ∈ token ∧ Part.Word (.one (.one token)) := by
  intro atom hatom hcounted
  rw [← h.flatten] at hatom
  obtain ⟨token, htoken, hmem⟩ := List.mem_flatten.mp hatom
  refine ⟨token, htoken, hmem, fun other hother => ?_⟩
  cases hother
  exact ⟨atom, hmem, hcounted⟩

/-- The division of `atoms` into the runs that sentences are. -/
def divide (atoms : List Atom) : List (List (Option Part)) :=
  runs Flows (spread (fold (Item.Has .opening) (Item.Has .closing)
    (fold (Token.Has .quote) (Token.Has .quote) (runs Joins atoms))))

/-- The division into sentences holds of one result only: the computed one. -/
theorem divided_iff (atoms : List Atom) (cut : List (List (Option Part))) :
    Divided atoms cut ↔ cut = divide atoms := by
  constructor
  · rintro ⟨tokens, items, parts, htokens, hitems, hparts, hcut⟩
    rw [runs_iff] at htokens hcut
    rw [folded_iff] at hitems hparts
    rw [hcut, hparts, hitems, htokens, divide]
  · rintro rfl
    exact ⟨_, _, _, runs_spec _, folded_fold _, folded_fold _, runs_spec _⟩

end Regula.Controlled
