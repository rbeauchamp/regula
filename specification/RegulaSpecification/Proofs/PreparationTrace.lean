/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderOnly

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

/-- A source read either makes no act, or makes exactly one copy with the source response preceding it.
The remainder, including a failed header parse, is observational. -/
theorem readSource_preparation {project tree path : FilePath} {t : List (Event L E)}
    {b : Except String Source} (h : Runs (readSource project tree path : Attempt L E Source).run t b) :
    Quiet t ∨ ∃ before text step after complete,
      t = before ++ step ++ after ∧ Quiet before ∧ SourceText before project tree path text ∧
      CopyStep tree path text step complete ∧ Quiet after := by
  rw [readSource] at h
  obtain ⟨a, after, result, rfl, ha, hb⟩ := runs_attempt_bind_iff.mp h
  have hafter : Quiet after := by
    cases result with
    | error error => obtain ⟨rfl, -⟩ := hb; exact quiet_nil
    | ok text =>
      exact (onlyA_seq (onlyA_attempt (only_call (P := QuietOp)
        (o := .parseHeader (Lean.Parser.mkInputContext text path.toString)) trivial))
        fun _ => onlyA_pure _) _ _ hb
  rw [copyToTree] at ha
  split at ha
  · obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp ha
    exact .inl (by simpa using hafter)
  · rename_i rel hrel
    obtain ⟨before, rest, r, rfl, hr, ht⟩ := runs_attempt_bind_iff.mp ha
    have hbefore : Quiet before := quiet_readExact _ _ _ _ hr
    cases r with
    | error error =>
      obtain ⟨rfl, rfl⟩ := ht
      exact .inl (by simpa using hbefore.append hafter)
    | ok text =>
      obtain ⟨step, tail, r, rfl, hs, hend⟩ := runs_attempt_bind_iff.mp ht
      have hstep := writeInTree_preparation hs
      have htail : tail = [] := by
        cases r with
        | error error => exact hend.1
        | ok u => exact (runs_attempt_pure_iff.mp hend).1
      subst htail
      obtain ⟨real, he, -⟩ := (readExact_spec hr).1 text rfl
      refine .inr ⟨before, text, step, after, r.isOk, by simp, hbefore,
        ⟨rel, (treeRelative_iff _ _ _).mp hrel, ?_⟩, hstep, hafter⟩
      simp [he, under, joinParts]

/-- The source step may follow earlier named imports; it never obtains its text from a later read. -/
theorem readSource_module {project tree path : FilePath} {root : Root L} {modules m}
    {prior t : List (Event L E)} {b : Except String Source}
    (hn : Named prior project tree root modules m) (hp : FileOfModule root modules m path)
    (h : Runs (readSource project tree path : Attempt L E Source).run t b) :
    ModuleCopies project tree root modules prior t := by
  rcases readSource_preparation h with hq | ⟨before, text, step, after, complete, rfl, hb, hs, hc, ha⟩
  · exact .observations _ fun e he => .inl (hq e he)
  · rw [List.append_assoc]
    apply ModuleCopies.append (.observations _ fun e he => .inl (hb e he))
    exact .copy (Named.mono (List.sublist_append_left _ _) hn) hp
      (SourceText.mono (List.sublist_append_right _ _) hs) hc
      (.observations _ fun e he => .inl (ha e he))

theorem observing_toolchainOLean (dirs : List FilePath) (m : Name) :
    OnlyAIn (fun o => QuietOp o ∨ ParserSearchOp o) (toolchainOLean dirs m : Attempt L E _) := by
  rw [toolchainOLean]
  refine onlyA_seq (onlyA_attempt (only_call (.inr trivial))) fun olean => ?_
  refine onlyA_seq ((quiet_realPath olean).mono fun _ h => .inl h) fun real => ?_
  split
  · exact onlyA_pure _
  · exact onlyA_throw _

/-- Every step of the walk is a copy of a name already directed by the prefix. Failed steps keep the
same obligation for the later names; successful headers extend it only after their parse event. -/
theorem walk_preparation (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (dirs : List FilePath) (fuel : Nat) (todo : List Name) (w : Walk)
    {prior t : List (Event L E)} {out : Walk}
    (hn : ∀ m ∈ todo, Named prior project tree root modules m)
    (h : Runs (walk project tree root modules dirs fuel todo w : Prog L E Walk) t out) :
    ModuleCopies project tree root modules prior t := by
  induction fuel generalizing todo w prior t out with
  | zero =>
    cases todo <;> obtain ⟨rfl, -⟩ := runs_pure_iff.mp h <;> exact .nil
  | succ fuel ih =>
    cases todo with
    | nil => obtain ⟨rfl, -⟩ := runs_pure_iff.mp h; exact .nil
    | cons m rest =>
      rw [walk] at h
      have hm := hn m (by simp)
      have hr : ∀ n ∈ rest, Named prior project tree root modules n := fun n h => hn n (by simp [h])
      split at h
      · exact ih rest w hr h
      · split at h
        · exact ih rest _ hr h
        · split at h
          · exact ih rest _ hr h
          · cases hf : fileOf root modules m with
            | some path =>
              simp only [hf] at h
              obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_seq_iff.mp h
              apply ModuleCopies.append (readSource_module hm (fileOf_mem hf) hfirst)
              have hm' := Named.mono (List.sublist_append_left prior first) hm
              have hr' : ∀ n ∈ rest, Named (prior ++ first) project tree root modules n :=
                fun n h => Named.mono (List.sublist_append_left _ _) (hr n h)
              cases response with
              | error error => exact ih rest _ hr' hlast
              | ok source =>
                have hs := (readSource_spec hfirst).1 source rfl
                have hh := headerOf_read hf (hs.mono (List.sublist_append_right prior first))
                refine ih _ _ ?_ hlast
                intro n hmem
                rcases List.mem_append.mp hmem with hmem | hmem
                · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
                  exact .imported hm' hh (Array.mem_toList_iff.mp hi)
                · exact hr' n hmem
            | none =>
              simp only [hf] at h
              obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_seq_iff.mp h
              apply ModuleCopies.append (.observations _ (observing_toolchainOLean dirs m _ _ hfirst))
              have hr' : ∀ n ∈ rest, Named (prior ++ first) project tree root modules n :=
                fun n h => Named.mono (List.sublist_append_left _ _) (hr n h)
              cases response <;> exact ih rest _ hr' hlast

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
