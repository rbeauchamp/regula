/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderOnly
import RegulaSpecification.Proofs.Standing

/-!
# Exact segments of preparation

The copy relation is about all responses of the actual `writeInTree`, including failed attempts.
Append lemmas compose exact segments without inserting an act between their events. Earlier-read
witnesses are extended only by appending the segment that has already run.
-/

namespace RegulaSpecification.Effects
open Lean (Name)
open System (FilePath)
open Regula.Effect Regula.Reader Regula.Language RegulaSpecification.Language
variable {L E α β : Type}

theorem quiet_nil : Quiet (L := L) (E := E) [] := by simp [Quiet]

theorem Quiet.append {a b : List (Event L E)} (ha : Quiet a) (hb : Quiet b) : Quiet (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem quiet_realPath (path : FilePath) : OnlyAIn QuietOp (realPath path : Attempt L E _) :=
  onlyA_attempt (only_call trivial)

theorem quiet_readExact (project path : FilePath) : OnlyAIn QuietOp (readExact project path : Attempt L E _) := by
  rw [readExact]
  refine onlyA_seq (quiet_realPath _) fun real => ?_
  split
  · exact onlyA_attempt (only_call trivial)
  · exact onlyA_throw _

theorem quiet_defaultModules (root : Root L) (targets : List Name) :
    OnlyAIn QuietOp (defaultModules root targets : Attempt L E _) := by
  induction targets with
  | nil => exact onlyA_pure _
  | cons target targets ih =>
    refine onlyA_seq ?_ fun _ => onlyA_seq ih fun _ => onlyA_pure _
    rw [modulesOfTarget]
    split
    · exact onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => onlyA_pure _
    · split <;> exact onlyA_pure _

theorem quiet_realPaths (paths : List FilePath) : OnlyAIn QuietOp (realPaths paths : Attempt L E _) := by
  induction paths with
  | nil => exact onlyA_pure _
  | cons path paths ih =>
    exact onlyA_seq (quiet_realPath _) fun _ => onlyA_seq ih fun _ => onlyA_pure _

/-- The attempted copy's exact acts, regardless of success. -/
theorem writeInTree_preparation {tree path : FilePath} {text : String} {t : List (Event L E)}
    {b : Except String Unit} (h : Runs (writeInTree tree path text : Attempt L E Unit).run t b) :
    CopyStep tree path text t b.isOk := by
  rw [writeInTree] at h
  split at h
  · rename_i hin
    have hpath := (inTree_iff tree path).mp hin
    obtain ⟨a, b', result, rfl, ha, hb⟩ := runs_attempt_bind_iff.mp h
    rw [makeParent] at ha
    cases hp : path.parent with
    | none =>
      simp only [hp] at ha
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp ha
      obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hb
      obtain rfl := runs_call_iff.mp hc
      cases r <;> exact .noParent hpath hp
    | some parent =>
      simp only [hp] at ha
      split at ha
      · rename_i hparent
        obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp ha
        obtain rfl := runs_call_iff.mp hc
        cases r with
        | error error =>
          obtain ⟨rfl, rfl⟩ := hb
          simpa [Except.isOk, Except.toBool] using (CopyStep.parentFailed (L := L) (E := E) (text := text) (error := error)
            hpath hp ((inTree_iff tree parent).mp hparent))
        | ok u =>
          obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hb
          obtain rfl := runs_call_iff.mp hc
          cases u
          cases r <;> exact .parentWritten hpath hp ((inTree_iff tree parent).mp hparent)
      · rename_i hparent
        obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp ha
        obtain ⟨rfl, rfl⟩ := hb
        refine .outside (.inr ⟨parent, hp, ?_⟩)
        intro rel hr
        exact hparent ((inTree_iff tree parent).mpr ⟨rel, hr⟩)
  · rename_i hout
    obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h
    refine .outside (.inl ?_)
    intro rel hr
    exact hout ((inTree_iff tree path).mpr ⟨rel, hr⟩)

theorem ModuleCopies.append {project tree : FilePath} {root : Root L} {modules}
    {prior a b : List (Event L E)} (ha : ModuleCopies project tree root modules prior a)
    (hb : ModuleCopies project tree root modules (prior ++ a) b) :
    ModuleCopies project tree root modules prior (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | @observe prior e rest he ht ih =>
    exact .observe he (ih (by simpa [List.append_assoc] using hb))
  | @copy prior m path text step rest complete hn hp hs hc ht ih =>
    simpa [List.append_assoc] using ModuleCopies.copy hn hp hs hc
      (ih (by simpa [List.append_assoc] using hb))

theorem ModuleCopies.observations {project tree : FilePath} {root : Root L} {modules}
    (prior : List (Event L E)) {t : List (Event L E)} (h : ∀ e ∈ t, QuietOp e.op ∨ ParserSearchOp e.op) :
    ModuleCopies project tree root modules prior t := by
  induction t generalizing prior with
  | nil => exact .nil
  | cons e t ih =>
    exact .observe (h e (by simp)) (ih _ fun x hx => h x (by simp [hx]))

/-- A source read is only observation. -/
theorem quiet_readSource (project tree path : FilePath) : OnlyAIn QuietOp (readSource project tree path : Attempt L E _) := by
  rw [readSource, readForTree]
  refine onlyA_seq ?_ fun _ => onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => onlyA_pure _
  split
  · exact onlyA_throw _
  · split
    · exact quiet_readExact _ _
    · exact onlyA_throw _

theorem observing_toolchainOLean (dirs : List FilePath) (m : Name) :
    OnlyAIn (fun o => QuietOp o ∨ ParserSearchOp o) (toolchainOLean dirs m : Attempt L E _) := by
  rw [toolchainOLean]
  refine onlyA_seq (onlyA_attempt (only_call (.inr trivial))) fun olean => ?_
  refine onlyA_seq ((quiet_realPath olean).mono fun _ h => .inl h) fun real => ?_
  split
  · exact onlyA_pure _
  · exact onlyA_throw _

/-- The walk reads and acts on nothing. What it gives is what later copies need: each source's name is needed, by the
imports that the prefix read, and its text is what the prefix read of its file. -/
theorem walk_preparation (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (dirs : List FilePath) (fuel : Nat) (todo : List Name) (w : Walk)
    {prior t : List (Event L E)} {out : Walk}
    (hn : ∀ m ∈ todo, Named prior project tree root modules m)
    (h : Runs (walk project tree root modules dirs fuel todo w : Prog L E Walk) t out)
    (hw : ∀ x ∈ w.sources, Named prior project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText prior project tree x.2.path x.2.text) :
    (∀ e ∈ t, QuietOp e.op ∨ ParserSearchOp e.op) ∧
    ∀ x ∈ out.sources, Named (prior ++ t) project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText (prior ++ t) project tree x.2.path x.2.text := by
  have mono {a b : List (Event L E)} (hs : a.Sublist b) {x : Name × Source}
      (hx : Named a project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
        SourceText a project tree x.2.path x.2.text) :
      Named b project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
        SourceText b project tree x.2.path x.2.text :=
    ⟨Named.mono hs hx.1, hx.2.1, SourceText.mono hs hx.2.2⟩
  induction fuel generalizing todo w prior t out with
  | zero =>
    cases todo <;> obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h <;>
      exact ⟨fun e he => (by cases he), fun x hx => mono (List.sublist_append_left _ _) (hw x hx)⟩
  | succ fuel ih =>
    cases todo with
    | nil =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      exact ⟨fun e he => (by cases he), fun x hx => mono (List.sublist_append_left _ _) (hw x hx)⟩
    | cons m rest =>
      rw [walk] at h
      have hm := hn m (by simp)
      have hr : ∀ n ∈ rest, Named prior project tree root modules n := fun n h => hn n (by simp [h])
      split at h
      · exact ih rest _ hr h hw
      · split at h
        · exact ih rest _ hr h hw
        · split at h
          · exact ih rest _ hr h hw
          · cases hf : fileOf root modules m with
            | some path =>
              simp only [hf] at h
              obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_seq_iff.mp h
              have hq : ∀ e ∈ first, QuietOp e.op ∨ ParserSearchOp e.op :=
                fun e he => .inl (quiet_readSource _ _ _ _ _ hfirst e he)
              have hr' : ∀ n ∈ rest, Named (prior ++ first) project tree root modules n :=
                fun n h => Named.mono (List.sublist_append_left _ _) (hr n h)
              have hw' : ∀ x ∈ w.sources, Named (prior ++ first) project tree root modules x.1 ∧
                  FileOfModule root modules x.1 x.2.path ∧ SourceText (prior ++ first) project tree x.2.path x.2.text :=
                fun x hx => mono (List.sublist_append_left _ _) (hw x hx)
              cases response with
              | error error =>
                obtain ⟨g1, g2⟩ := ih rest _ hr' hlast hw'
                refine ⟨fun e he => ?_, fun x hx => by simpa [List.append_assoc] using g2 x hx⟩
                rcases List.mem_append.mp he with he | he
                · exact hq e he
                · exact g1 e he
              | ok source =>
                have hs := (readSource_spec hfirst).1 source rfl
                have hm' := Named.mono (List.sublist_append_left prior first) hm
                have hh := headerOf_read hf (hs.mono (List.sublist_append_right prior first))
                have hnew : ∀ x ∈ ({ w with reached := m :: w.reached, sources := (m, source) :: w.sources } : Walk).sources,
                    Named (prior ++ first) project tree root modules x.1 ∧
                    FileOfModule root modules x.1 x.2.path ∧ SourceText (prior ++ first) project tree x.2.path x.2.text := by
                  intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · obtain ⟨rel, real, text, hrel, -, -, hpath, ht, -, hsub⟩ := hs
                    subst hpath
                    refine ⟨hm', fileOf_mem hf, rel, hrel, ?_⟩
                    rw [ht]
                    exact List.mem_append_right _ (hsub.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                  · exact hw' x hx
                obtain ⟨g1, g2⟩ := ih _ _ (fun n hmem => by
                    rcases List.mem_append.mp hmem with hmem | hmem
                    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
                      exact .imported hm' hh (Array.mem_toList_iff.mp hi)
                    · exact hr' n hmem) hlast hnew
                refine ⟨fun e he => ?_, fun x hx => by simpa [List.append_assoc] using g2 x hx⟩
                rcases List.mem_append.mp he with he | he
                · exact hq e he
                · exact g1 e he
            | none =>
              simp only [hf] at h
              obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_seq_iff.mp h
              have hq := observing_toolchainOLean dirs m _ _ hfirst
              have hr' : ∀ n ∈ rest, Named (prior ++ first) project tree root modules n :=
                fun n h => Named.mono (List.sublist_append_left _ _) (hr n h)
              have hw' : ∀ x ∈ w.sources, Named (prior ++ first) project tree root modules x.1 ∧
                  FileOfModule root modules x.1 x.2.path ∧ SourceText (prior ++ first) project tree x.2.path x.2.text :=
                fun x hx => mono (List.sublist_append_left _ _) (hw x hx)
              cases response <;>
                (obtain ⟨g1, g2⟩ := ih rest _ hr' hlast hw'
                 refine ⟨fun e he => ?_, fun x hx => by simpa [List.append_assoc] using g2 x hx⟩
                 rcases List.mem_append.mp he with he | he
                 · exact hq e he
                 · exact g1 e he)

/-- The acts of `writeSources` fit `ModuleCopies`, each step using what the prefix read. -/
theorem writeSources_preparation {project tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    {srcs : List (Name × Source)} {prior t : List (Event L E)} {b : Except String Unit}
    (hs : ∀ x ∈ srcs, Named prior project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText prior project tree x.2.path x.2.text)
    (h : Runs (writeSources tree srcs : Attempt L E Unit).run t b) :
    ModuleCopies project tree root modules prior t := by
  induction srcs generalizing prior t b with
  | nil =>
    rw [writeSources] at h
    obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp h
    exact .nil
  | cons x rest ih =>
    obtain ⟨m, s⟩ := x
    rw [writeSources] at h
    obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨hn, hf, hst⟩ := hs (m, s) (List.mem_cons_self ..)
    refine .copy hn hf hst (writeInTree_preparation hfirst) ?_
    cases response with
    | error error =>
      obtain ⟨rfl, -⟩ := hlast
      exact .nil
    | ok u =>
      refine ih (fun y hy => ?_) hlast
      obtain ⟨g1, g2, g3⟩ := hs y (List.mem_cons_of_mem _ hy)
      exact ⟨Named.mono (List.sublist_append_left _ _) g1, g2, SourceText.mono (List.sublist_append_left _ _) g3⟩

/-- The module-copy grammar alone admits the trace of `uncheckedCopy_fails`, for every text, when `path` is a needed name's file with
its parent in the tree. So what refuses that trace is `Evidence` of what it leaves, and not the grammar. -/
theorem moduleCopies_admits_uncheckedCopy {project tree path parent : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    {prior body : List (Event L E)} {m : Name} {rel : List String} (text : String)
    (hc : ModuleCopies project tree root modules prior body)
    (hn : Named (prior ++ body) project tree root modules m)
    (hf : FileOfModule root modules m path)
    (hr : TreeRelative (parts tree) (parts path) rel)
    (hp : path.parent = some parent)
    (hparent : ∃ rel, TreeRelative (parts tree) (parts parent) rel) :
    ModuleCopies project tree root modules prior (body ++ uncheckedCopy (under project rel) path parent text) := by
  apply ModuleCopies.append hc
  apply ModuleCopies.observe (Or.inl (show QuietOp (.readFile (under project rel) : Op L E) from trivial))
  apply ModuleCopies.copy (Named.mono (List.sublist_append_left _ _) hn) hf
    (text := text) (complete := true) (rest := [])
    (step := [⟨.createDirAll parent, .ok ()⟩, ⟨.writeFile path text, .ok ()⟩])
  · exact ⟨rel, hr, by simp⟩
  · exact CopyStep.parentWritten ⟨rel, hr⟩ hp hparent
  · exact ModuleCopies.nil

theorem quiet_parseAll (input) (env : E) (state) (messages) (fuel : Nat) :
    OnlyIn QuietOp (parseAll input env state messages fuel : Prog L E _) := by
  induction fuel generalizing state messages with
  | zero => exact only_pure _
  | succ fuel ih =>
    rw [parseAll]
    refine only_seq (only_call trivial) fun ⟨stx, state', messages'⟩ => ?_
    dsimp only
    split
    · exact only_pure _
    · exact only_seq (ih state' messages') fun _ => only_pure _

theorem observing_parseFiles (sources : List (Name × Source)) (toolchain : List Name)
    (todo : List (Name × Source)) (cache : ParserCache E) :
    OnlyAIn (fun o => QuietOp o ∨ ParserSearchOp o) (parseFiles sources toolchain cache todo : Attempt L E _) := by
  induction todo generalizing cache with
  | nil => exact onlyA_pure _
  | cons x todo ih =>
    obtain ⟨m, source⟩ := x
    refine onlyA_seq ?_ fun ⟨file, cache'⟩ => onlyA_seq (ih cache') fun _ => onlyA_pure _
    rw [parseFile]
    refine onlyA_seq ?_ fun ⟨⟨env, scopedNames⟩, cache'⟩ => ?_
    · rw [environmentFor]
      split
      · exact onlyA_pure _
      · exact onlyA_seq (onlyA_attempt (only_call (.inr trivial))) fun _ => onlyA_pure _
    · exact onlyA_seq (onlyA_lift ((quiet_parseAll _ _ _ _ _).mono fun _ h => .inl h))
        fun _ => onlyA_pure _

end RegulaSpecification.Effects
