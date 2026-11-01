/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Filesystem
import RegulaSpecification.Proofs.Program

/-!
# Exclusive installation and the consumer's actual contents

The writer theorem reads the actual IO definition. It does not assume that different path components denote
different files. The filesystem primitives, compiler and absence of external mutation remain trusted boundaries.
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect

private theorem io_bind_apply {α β : Type} (x : IO α) (f : α → IO β) (w : World) :
    (x >>= f) w = match x w with
      | .ok a w' => f a w'
      | .error e w' => .error e w' := by
  show EST.bind x f w = _
  cases hx : x w <;> simp [EST.bind, hx]

private theorem io_lift_apply {α : Type} (x : BaseIO α) (w : World) :
    (liftM x : IO α) w = .ok (x w).val (x w).state := rfl

private theorem io_pure_apply {α : Type} (a : α) (w : World) :
    (pure a : IO α) w = .ok a w := by
  show EST.pure a w = _
  rfl

private theorem io_throw_apply {α : Type} (e : IO.Error) (w : World) :
    (throw e : IO α) w = .error e w := by
  show EST.throw e w = _
  rfl

/-- Success of the actual writer means that either a fresh exclusive handle was written and flushed, or exclusive
creation reported an existing file and its read gave precisely the requested text. These are sequential worlds, not
independent witnesses of calls. -/
theorem writePreserving_io (path : FilePath) (text : String) (w w' : World) :
    writePreserving path text w = .ok () w' ↔
      (∃ h w₁ w₂, IO.FS.Handle.mk path .writeNew w = .ok h w₁ ∧
        h.putStr text w₁ = .ok () w₂ ∧ h.flush w₂ = .ok () w') ∨
      (∃ name code detail w₁,
        IO.FS.Handle.mk path .writeNew w = .error (.alreadyExists name code detail) w₁ ∧
        IO.FS.readFile path w₁ = .ok text w') := by
  cases hopen : IO.FS.Handle.mk path .writeNew w with
  | ok h w₁ =>
    simp only [writePreserving, io_bind_apply, io_lift_apply, EIO.toBaseIO, hopen]
    cases hput : h.putStr text w₁ with
    | ok u w₂ =>
      cases u
      simp [hput, eq_comm, and_assoc]
    | error e w₂ =>
      simp [hput, eq_comm, and_assoc]
  | error error w₁ =>
    simp only [writePreserving, io_bind_apply, io_lift_apply, EIO.toBaseIO, hopen]
    cases error <;> try simp [eq_comm, and_assoc, io_throw_apply]
    rename_i name code detail
    simp only [io_bind_apply]
    cases hread : IO.FS.readFile path w₁ with
    | error error w₂ =>
      simp [eq_comm]
    | ok existing w₂ =>
      by_cases heq : existing = text
      · subst heq
        simp [io_pure_apply]
      · simp [Ne.symm heq, io_throw_apply]

/-- Every successful call of the actual writer installs its text and preserves all earlier contents, including any
alias of its destination. This follows from the primitive laws, not from an assumed contract for Regula's writer. -/
theorem writePreserving_correct {contents : World → Contents} {paths : FilePath → Prop} (fs : FilePrimitives contents paths)
    {path : FilePath} {text : String} {w w' : World}
    (hp : paths path) (h : writePreserving path text w = .ok () w') : Installed path text (contents w) (contents w') := by
  rcases (writePreserving_io path text w w').mp h with ⟨handle, w₁, w₂, hopen, hput, hflush⟩ |
    ⟨name, code, detail, w₁, hopen, hread⟩
  · exact fs.fresh path text w handle w₁ w₂ w' hp hopen hput hflush
  · obtain ⟨htext, hkeep⟩ := fs.read path w₁ text w' hp hread
    exact ⟨htext, fun q old hq => hkeep q old (fs.failedOpen path w _ w₁ hp hopen q old hq)⟩

/-- The table's actual write row has the preservation contract. -/
theorem table_write_correct {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L)
    {contents : World → Contents} {paths : FilePath → Prop} (fs : FilePrimitives contents paths)
    {path : FilePath} {text : String} {w w' : World}
    (hp : paths path)
    (h : table enable lake (.writeFile path text) w = ⟨.ok (), w'⟩) :
    Installed path text (contents w) (contents w') := by
  cases hw : writePreserving path text w with
  | error error w₁ =>
    have hv := congrArg ST.Out.val h
    simp [table, EIO.toBaseIO, hw] at hv
  | ok u w₁ =>
    cases u
    have he : w₁ = w' := by simpa [table, EIO.toBaseIO, hw] using congrArg ST.Out.state h
    subst he
    exact writePreserving_correct fs hp hw

/-- Interpretation gives an execution with the actual successive worlds, in addition to the response trace. -/
theorem interpret_execution {L E α : Type} (table : (o : Op L E) → BaseIO (Resp o))
    (p : Prog L E α) (w : World) :
    Execution table w (traceFrom table p w) (Prog.interpret table p w).state := by
  induction p generalizing w with
  | done a => exact .nil w
  | ask o next ih =>
    exact .step (by cases table o w; rfl) (ih (table o w).val (table o w).state)

/-- Splitting an execution preserves the world at the boundary, rather than inventing separate response worlds. -/
theorem Execution.append {L E : Type} {table : (o : Op L E) → BaseIO (Resp o)}
    {a b : List (Event L E)} {w w' : World} (h : Execution table w (a ++ b) w') :
    ∃ middle, Execution table w a middle ∧ Execution table middle b w' := by
  induction a generalizing w with
  | nil => exact ⟨w, .nil w, h⟩
  | cons e a ih =>
    cases h with
    | step hs ht =>
      obtain ⟨middle, h₁, h₂⟩ := ih ht
      exact ⟨middle, .step hs h₁, h₂⟩

/-- The trusted non-writing calls at the occurrences and worlds of this execution preserve the copied input paths.
This excludes the writer, whose preservation is proved above, and cleanup. It constrains neither an arbitrary Lake
command nor an unrelated world, and permits Lake to change its build products outside the input scope. -/
def KeepsInputs {L : Type} (contents : World → Contents) (scope : List String → Prop)
    (enable : BaseIO Unit) (lake : LakeCalls L) (start : World) (t : List (Event L Lean.Environment)) : Prop :=
  ∀ before e after w, t = before ++ e :: after → Execution (table enable lake) start before w → e.keepsFiles →
    ∀ q text, scope q → contents w q = some text → contents (table enable lake e.op w).state q = some text

/-- On a segment with successful writes and no removal, the actual table preserves the correspondence between every
requested input text and filesystem contents. No distinct-path or distinct-file premise is used. -/
theorem execution_contents {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L)
    {contents : World → Contents} {paths : FilePath → Prop} (fs : FilePrimitives contents paths) {scope : List String → Prop}
    {t : List (Event L Lean.Environment)} {w w' : World} (hx : Execution (table enable lake) w t w')
    (keep : KeepsInputs contents scope enable lake w t)
    (hn : ∀ e ∈ t, NotRemoving e.op)
    (hs : ∀ path text response, (⟨.writeFile path text, response⟩ : Event L Lean.Environment) ∈ t → response = .ok ())
    (hp : ∀ path text response, (⟨.writeFile path text, response⟩ : Event L Lean.Environment) ∈ t → paths path)
    (held : Contents)
    (ha : ∀ q text, scope q → held q = some text → contents w q = some text) :
    ∀ q text, scope q → leavesFrom t q (held q) = some text → contents w' q = some text := by
  induction hx generalizing held with
  | nil w => exact ha
  | @step w w₁ w₂ o response rest hstep hrest ih =>
    have hsingle : ∀ q text, scope q →
        (⟨o, response⟩ : Event L Lean.Environment).leaves q (held q) = some text → contents w₁ q = some text := by
      intro q text hscope htext
      by_cases hk : (⟨o, response⟩ : Event L Lean.Environment).keepsFiles
      · rw [Event.leaves_of_keeps hk] at htext
        have hkeep := keep [] ⟨o, response⟩ rest w rfl (.nil w) hk q text hscope (ha q text hscope htext)
        simpa [hstep] using hkeep
      · cases o <;> try exact (hk trivial).elim
        case removeDirAll path => exact (hn _ (List.mem_cons_self ..)).elim
        case writeFile path value =>
          have hr := hs path value response (List.mem_cons_self ..)
          subst hr
          obtain ⟨hnew, hpres⟩ := table_write_correct enable lake fs (hp path value _ (List.mem_cons_self ..)) hstep
          by_cases hp : parts path = q
          · simp only [Event.leaves, hp, ↓reduceIte, Option.some.injEq] at htext
            subst htext
            simpa [hp] using hnew
          · simp only [Event.leaves, hp, ↓reduceIte] at htext
            exact hpres q text (ha q text hscope htext)
    have krest : KeepsInputs contents scope enable lake w₁ rest := by
      intro before e after middle ht hx hk q text hscope hcontents
      exact keep (⟨o, response⟩ :: before) e after middle (by simp [ht]) (.step hstep hx) hk q text hscope hcontents
    exact ih krest (fun e he => hn e (List.mem_cons_of_mem _ he))
      (fun path text r he => hs path text r (List.mem_cons_of_mem _ he))
      (fun path text r he => hp path text r (List.mem_cons_of_mem _ he))
      (fun q => (⟨o, response⟩ : Event L Lean.Environment).leaves q (held q)) hsingle

/-- Before a consumer in a full run, every requested write succeeded and no removal was attempted. These obligations
come from the reader and full-run record, not from assumptions about filesystem responses. -/
theorem FullRun.consumer_prefix {L E : Type} {t : List (Event L E)} {dir : FilePath}
    {profile : Regula.Closed.Profile} {code : UInt32} (h : FullRun t dir profile code)
    {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post) (he : e.consumesTree = true) :
    (∀ x ∈ pre, NotRemoving x.op) ∧
    (∀ path text response, (⟨.writeFile path text, response⟩ : Event L E) ∈ pre → response = .ok ()) := by
  constructor
  · intro x hx
    cases hop : x.op <;> try trivial
    case removeDirAll path =>
      obtain ⟨o, response⟩ := x
      simp only at hop
      subst hop
      obtain ⟨before, after, hpre⟩ := List.mem_iff_append.mp hx
      have horder := h.after_removal_saying before path response (after ++ e :: post)
        (by simpa [hpre, List.append_assoc] using ht) e (by simp)
      obtain ⟨op, r⟩ := e
      cases op <;> cases horder <;> cases he
  · intro path text response hx
    obtain ⟨tree, tRead, mid, r, hpre, hkeep, -, -, hnf⟩ := h.at_consumer ht he
    rw [hpre] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with hx | hx
      · cases congrArg Event.op hx
      · cases response with
        | ok u => cases u; rfl
        | error err => exact (hnf _ hx ⟨err, rfl⟩).elim
    · exact (hkeep _ hx).elim

/-- At every full-run consumer, the path-keyed admission agrees with the filesystem view reached by the actual table.
The scope for the external preservation premise is exactly the texts in that admission, not an independently chosen set.
Physical aliases are allowed: there is no premise that different path keys are different files. -/
theorem FullRun.filesystem_at_consumer {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L)
    {contents : World → Contents}
    {t : List (Event L Lean.Environment)} {dir : FilePath} {profile : Regula.Closed.Profile} {code : UInt32}
    (h : FullRun t dir profile code) {pre post : List (Event L Lean.Environment)} {e : Event L Lean.Environment}
    (ht : t = pre ++ e :: post) (he : e.consumesTree = true)
    (fs : FilePrimitives contents (fun path => ∃ text response,
      (⟨.writeFile path text, response⟩ : Event L Lean.Environment) ∈ pre))
    {w w' : World} (hx : Execution (table enable lake) w t w')
    (keep : KeepsInputs contents (fun q => ∃ text, written pre q = some text) enable lake w pre) :
    ∃ atConsumer, Execution (table enable lake) w pre atConsumer ∧
      ∀ q text, written pre q = some text → contents atConsumer q = some text := by
  rw [ht] at hx
  obtain ⟨atConsumer, hxpre, -⟩ := hx.append
  obtain ⟨hn, hs⟩ := h.consumer_prefix ht he
  refine ⟨atConsumer, hxpre, fun q text htext => ?_⟩
  exact execution_contents enable lake fs hxpre keep hn hs (fun path text r hm => ⟨text, r, hm⟩) (fun _ => none)
    (by intro q text _ hnone; cases hnone) q text ⟨text, htext⟩ htext

/-- The interpreted full gate inherits the filesystem correspondence, through its actual reader, writer and effect
table. This is conditional only on the named primitive laws and preservation by the other trusted calls. -/
theorem runFull_filesystem_at_consumer {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L)
    {contents : World → Contents}
    (profile : Regula.Closed.Profile) (dir : FilePath) (w : World)
    {pre post : List (Event L Lean.Environment)} {e : Event L Lean.Environment}
    (ht : traceFrom (table enable lake) (Regula.Shell.runFull profile dir) w = pre ++ e :: post)
    (he : e.consumesTree = true)
    (fs : FilePrimitives contents (fun path => ∃ text response,
      (⟨.writeFile path text, response⟩ : Event L Lean.Environment) ∈ pre))
    (keep : KeepsInputs contents (fun q => ∃ text, written pre q = some text) enable lake w pre) :
    ∃ atConsumer tree tRead mid r,
      Execution (table enable lake) w pre atConsumer ∧
      pre = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ mid ∧ RegulaSpecification.Language.Inside r ∧
      Evidence tRead dir tree (written pre) r ∧
      ∀ q text, written pre q = some text → contents atConsumer q = some text := by
  have hfull := runFull_spec (interpret_runs (table enable lake) (Regula.Shell.runFull profile dir) w)
  obtain ⟨atConsumer, hx, hcontents⟩ := hfull.filesystem_at_consumer enable lake ht he fs
    (interpret_execution (table enable lake) (Regula.Shell.runFull profile dir) w) keep
  obtain ⟨tree, tRead, mid, r, hpre, -, hi, hev, -⟩ := hfull.at_consumer ht he
  exact ⟨atConsumer, tree, tRead, mid, r, hx, hpre, hi, hev, hcontents⟩

/-- If the filesystem view identifies two destination observations, their admitted texts must agree. In particular,
two names for one physical file cannot carry different admitted texts under the consumer correspondence. -/
theorem filesystem_alias_texts {held actual : Contents}
    (corresponds : ∀ q text, held q = some text → actual q = some text)
    {p q : List String} {x y : String} (hp : held p = some x) (hq : held q = some y)
    (alias : actual p = actual q) : x = y :=
  Option.some.inj ((corresponds p x hp).symm.trans (alias.trans (corresponds q y hq)))

end RegulaSpecification.Effects
