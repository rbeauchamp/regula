/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Preparation
import RegulaSpecification.Proofs.Owed
import RegulaSpecification.Proofs.Written

/-!
# What a full verdict's admission is about

These theorems read the record alone, so they hold of every program that meets it. `FullRun.at_consumer` states that at each
Lake command and each load for the rules, the state of the tree that the run's own acts left is the state the admission judged,
with no later act of the run changing it. `Evidence.judged` states that each text standing in the tree is one the run judged.
`uncheckedCopy_fails` makes the trace of an audit of an earlier revision fail the record, for every text the run did not judge,
and `judgedCopy_stands` is its neighbour: the same copy of a text that stands keeps the evidence. `rewritten_stands` states the
other direction: a run may write a text, read again and write another, because only what stands is what the evidence is about.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open Lean.Parser (mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-- Whether a request consumes the tree's files by a call of Lake or Lean that this trace does not look into. -/
def Event.consumesTree (e : Event L E) : Bool :=
  e.isBuild || e.isImportForRules

/-- An event that only reports or that the rules phase may ask does not write or remove. -/
theorem keeps_of_no_mutation {e : Event L E} (h : match e.op with
    | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ => False
    | _ => True) : e.keepsFiles := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | trivial | exact h.elim

/-- An event that is not in a prefix of a list comes after all of that prefix. -/
theorem prefix_of_not_mem {A B pre post : List (Event L E)} {e : Event L E} (h : A ++ B = pre ++ e :: post) (he : e ∉ A) :
    ∃ mid, pre = A ++ mid ∧ B = mid ++ e :: post := by
  induction A generalizing pre with
  | nil => exact ⟨pre, rfl, h⟩
  | cons a A ih =>
    cases pre with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) he
    | cons x pre' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨mid, rfl, hb⟩ := ih h' (fun hx => he (List.mem_cons_of_mem _ hx))
      exact ⟨mid, rfl, hb⟩

/-- What comes before an event that is not in a suffix of a list lies in the rest. -/
theorem mem_of_before {G R mid post : List (Event L E)} {e : Event L E} (h : G ++ R = mid ++ e :: post) (he : e ∉ R) :
    ∀ x ∈ mid, x ∈ G := by
  induction G generalizing mid with
  | nil =>
    simp only [List.nil_append] at h
    exact absurd (by rw [h]; simp) he
  | cons g G ih =>
    cases mid with
    | nil => intro x hx; cases hx
    | cons m mid' =>
      simp only [List.cons_append, List.cons.injEq] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [h.1]
      · exact List.mem_cons_of_mem _ (ih h.2 x hx)

/-- At each Lake command and each load for the rules of a full run, the reading was admitted on `Evidence` of what the tree holds
right then, and nothing the run asked of the reading failed. So the state the admission judged is the state that command consumes:
nothing the run does between the reading and that command writes or removes a file. This is about the run's own requests: what a
trusted call does inside itself and what another process does are not events of the trace. -/
theorem FullRun.at_consumer {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post)
    (he : e.consumesTree = true) :
    ∃ (tree : FilePath) (tRead : List (Event L E)) (r : Reading), Inside r ∧
      Evidence tRead dir tree (written pre) r ∧ (∀ x ∈ tRead, ¬ x.failed) := by
  have hsay {x : Event L E} (hs : x.isOnlySaying = true) : x.consumesTree = false := by
    obtain ⟨o, r⟩ := x
    cases o <;> first | rfl | cases hs
  rcases h with ⟨err, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, resp, last, rfl, hrd, hlast, o, report, hdec, hnf, hstop, hadm, -, -, -, -, -, -⟩
  · -- No tree: nothing consumes one.
    exfalso
    have hmem : e ∈ ⟨.createTempDir, .error err⟩ :: rest := by simp [ht]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases he
    · rw [hsay (hs e hmem)] at he
      cases he
  · have hnotRead : e ∉ (⟨.createTempDir, .ok tree⟩ :: tRead : List (Event L E)) := fun hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · cases he
      · have := hrd e hx
        simp [Event.consumesTree, this.1, this.2] at he
    have hnotLast : e ∉ (⟨.removeDirAll tree, resp⟩ :: last : List (Event L E)) := fun hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · cases he
      · rw [hsay (hlast e hx)] at he
        cases he
    have ht' : (⟨.createTempDir, .ok tree⟩ :: tRead) ++ (tGate ++ ⟨.removeDirAll tree, resp⟩ :: last) = pre ++ e :: post := by
      simpa [List.append_assoc] using ht
    obtain ⟨mid, hpre, hrest⟩ := prefix_of_not_mem ht' hnotRead
    by_cases ho : o = .admitted
    · subst ho
      obtain ⟨r, hi, hev⟩ := hdec.1 rfl
      obtain ⟨sysroot, tBuild, tRules, -, rfl, hb⟩ := hadm rfl
      have hgatePart := mem_of_before hrest hnotLast
      have hmid : ∀ x ∈ mid, x.keepsFiles := fun x hx => keeps_of_no_mutation (hb.no_mutation x (hgatePart x hx))
      have hstands : (written pre : List String → Option String) = written tRead := by
        funext q
        rw [hpre, written_append, leavesAs_nil_of_keeps hmid]
        rfl
      rw [hstands]
      exact ⟨tree, tRead, r, hi, hev, hnf rfl⟩
    · rw [(hstop ho).1, List.nil_append] at hrest
      exact (hnotLast (by rw [hrest]; simp)).elim

/-- Each text that the state of `Evidence` holds is one the run judged: the text of `lakefile.toml` that Lake's parser read, the
pinned text, or a text that a file of the reading was parsed from. -/
theorem Evidence.judged {T : List (Event L E)} {dir treeDir : FilePath} {held : List String → Option String} {r : Reading}
    (h : Evidence T dir treeDir held r) {q : List String} {text : String} (hq : held q = some text) :
    (∃ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ T) ∨ text = leanToolchain ∨
      ∃ f ∈ r.files, ∃ project tree path imports mods, parts path = q ∧ ReadText T project tree f path imports mods text := by
  obtain ⟨project, tree, -, -, -, -, -, -, ⟨t0, -, table, -, -, -, -, h5, h6, -, -⟩, hpin, -, -, -, root, -, modules, -, -, -, -, -, -,
    -, -, -, headers, -, -, -, -, -, -, honly⟩ := h.places
  rcases honly q text hq with rfl | rfl | ⟨f, hf, path, i, md, -, h1, h2⟩
  · have : t0 = text := Option.some.inj (h6.symm.trans hq)
    subst this
    exact .inl ⟨table, h5⟩
  · exact .inr (.inl (Option.some.inj (hq.symm.trans hpin)))
  · exact .inr (.inr ⟨f, hf, project, tree, path, i, md, h1, h2⟩)

/-- Two names with one file: the state of `Evidence` holds one text there, and each name's file of the reading was parsed from
that text, under the imports and the environment of that name. -/
theorem Evidence.two_names {T : List (Event L E)} {dir treeDir : FilePath} {held : List String → Option String} {r : Reading}
    (h : Evidence T dir treeDir held r) :
    ∃ (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) (headers : List (Name × Array Lean.Import)),
      ∀ m path m' path', Compiled headers root modules m path → Compiled headers root modules m' path' → parts path = parts path' →
        ∃ text, (∃ f ∈ r.files, f.module = m ∧ ∃ imports mods, ReadText T project tree f path imports mods text) ∧
          ∃ f ∈ r.files, f.module = m' ∧ ∃ imports mods, ReadText T project tree f path' imports mods text := by
  obtain ⟨project, tree, -, -, -, -, -, -, -, -, -, -, -, root, -, modules, -, -, -, -, -, -, -, -, -, headers, -, -, -, hc, -, -, -⟩ :=
    h.places
  refine ⟨project, tree, root, modules, headers, fun m path m' path' h1 h2 hp => ?_⟩
  obtain ⟨-, f, hf, hm, i, md, t1, -, g1, s1⟩ := hc m path h1
  obtain ⟨-, f', hf', hm', i', md', t2, -, g2, s2⟩ := hc m' path' h2
  have : t1 = t2 := Option.some.inj (s1.symm.trans (hp ▸ s2))
  subst this
  exact ⟨t1, ⟨f, hf, hm, i, md, g1⟩, f', hf', hm', i', md', g2⟩

/-- The trace of an audit of an earlier revision: after the reading, read a file of the project again, and copy what that read gave
over the file in the tree. -/
def uncheckedCopy (source path parent : FilePath) (text : String) : List (Event L E) :=
  [⟨.readFile source, .ok text⟩, ⟨.createDirAll parent, .ok ()⟩, ⟨.writeFile path text, .ok ()⟩]

/-- That trace fails the record, for every text the run did not judge, every path and every reading: the state it leaves holds that
text, and `Evidence` says that every text standing was judged. The module-copy grammar alone admits this trace, and `Evidence` of
the state does not. So an earlier good reading gives no authority for what a later write replaced. -/
theorem uncheckedCopy_fails {T : List (Event L E)} {dir treeDir source path parent : FilePath} {text : String} {r : Reading}
    (hpin : text ≠ leanToolchain)
    (hnotToml : ∀ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text)
    (hnotFile : ∀ name x, (⟨.parseHeader (mkInputContext text name), .ok x⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text) :
    ¬ Evidence (T ++ uncheckedCopy source path parent text) dir treeDir
      (written (T ++ uncheckedCopy source path parent text)) r := by
  intro hev
  have hq : written (T ++ uncheckedCopy (L := L) (E := E) source path parent text) (parts path) = some text := by
    have := written_last_write (T ++ [⟨.readFile source, .ok text⟩, ⟨.createDirAll parent, .ok ()⟩]) ([] : List (Event L E)) path text (.ok ())
      (fun _ _ => rfl)
    simpa [uncheckedCopy, List.append_assoc] using this
  rcases Evidence.judged hev hq with ⟨table, hm⟩ | h | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4, _⟩
  · exact hnotToml table hm
  · exact hpin h
  · exact hnotFile _ _ (h4.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- The neighbour of `uncheckedCopy_fails`: a read and a copy of the text that already stands there change nothing the evidence is
about. So what `uncheckedCopy_fails` refuses is the unjudged text, and not the shape of the trace. -/
theorem judgedCopy_stands {T : List (Event L E)} {dir treeDir source path parent : FilePath} {text : String} {r : Reading}
    (hev : Evidence T dir treeDir (written T) r) (hq : written T (parts path) = some text) :
    Evidence (T ++ uncheckedCopy source path parent text) dir treeDir
      (written (T ++ uncheckedCopy source path parent text)) r := by
  have hsame : (written (T ++ uncheckedCopy (L := L) (E := E) source path parent text) : List String → Option String) = written T := by
    funext q
    rw [written_append]
    simp only [uncheckedCopy, leavesFrom, List.foldl_cons, List.foldl_nil, Event.leaves]
    by_cases hp : parts path = q
    · subst hp
      simp [hq]
    · simp [hp]
  rw [hsame]
  exact Evidence.mono (List.sublist_append_left _ _) hev

/-- A run may write a text, read again and write another: what stands is the last. So `Evidence` of the state is about the later
text, and the earlier one gives neither authority nor obstacle. -/
theorem rewritten_stands (a b c : List (Event L E)) (path : FilePath) (x y : String) (r₁ r₂ : Except IO.Error Unit)
    (hc : LeavesAs c []) :
    written (a ++ ⟨.writeFile path x, r₁⟩ :: b ++ ⟨.writeFile path y, r₂⟩ :: c) (parts path) = some y := by
  have := written_last_write (a ++ ⟨.writeFile path x, r₁⟩ :: b) c path y r₂ hc
  simpa [List.append_assoc] using this

end RegulaSpecification.Effects
