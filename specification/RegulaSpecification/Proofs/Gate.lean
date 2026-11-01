/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.DiagnosticsGate
import Regula.Shell

/-!
# The local gate, at `IO`

The gate program is the merge gate, and a defect in it that let a broken change pass would be serious. `runSteps_io`,
`runIn_zero` and `runLocal_zero` prove, of the definitions at `IO`, from any state of the world, that it gives 0 only when it
wrote each file of `checkerFiles` to the checker's directory joined with that file, with the bytes it read, and for each step
of `localSteps` there are worlds in which it gave 0, with that directory as the checker and the working directory as the project. `BaseIO` and `IO` are state monads in Lean's own definition (`Init/System/ST.lean`), so
no assumption about the order of effects is needed for this. `localSteps_eq`, `localSteps_full`, `runStep_spawns` and
`stepRequest_eq` state what each step asks the operating system to start, and what it does with that request stays trusted. A defect that only stops the gate visibly, such as a failed
copy or removal, which `IO` turns into a nonzero exit, is accepted risk.
-/

namespace RegulaSpecification.GateProgram

open Regula.DiagnosticsGate

/-- A step of `IO`'s bind on success, by its definition. -/
theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {a : α}
    (h : x w = .ok a w₁) : (x >>= f) w = f a w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

/-- A step of `IO`'s bind on failure, by its definition. -/
theorem io_bind_error {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {e : IO.Error}
    (h : x w = .error e w₁) : (x >>= f) w = .error e w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

/-- A step of `IO`'s `finally` that gives a result: the body gave that result, and the finalizer succeeded. -/
theorem finally_ok {α β : Type} {x : IO α} {f : IO β} {w w' : Void IO.RealWorld} {a : α}
    (h : (tryFinally x f) w = .ok a w') : ∃ w₁, x w = .ok a w₁ ∧ ∃ b, f w₁ = .ok b w' := by
  have hu : (tryFinally' x (fun _ => f) : IO (α × β)) w =
      (MonadFinally.tryFinally' (m := EST IO.Error IO.RealWorld) x (fun _ => f)) w := rfl
  have ht : (tryFinally x f) w =
      ((tryFinally' x (fun _ => f) : IO (α × β)) >>= fun p => pure p.1) w := rfl
  rw [ht] at h
  cases hx : x w with
  | error e w₁ =>
    cases hf : f w₁ with
    | error e' w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e' w₂ := by
        rw [hu]
        unfold MonadFinally.tryFinally'
        simp only [instMonadFinallyEST]
        simp [hx, hf]
      rw [io_bind_error hk] at h
      cases h
    | ok b w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e w₂ := by
        rw [hu]
        unfold MonadFinally.tryFinally'
        simp only [instMonadFinallyEST]
        simp [hx, hf]
      rw [io_bind_error hk] at h
      cases h
  | ok a₀ w₁ =>
    cases hf : f w₁ with
    | error e' w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e' w₂ := by
        rw [hu]
        unfold MonadFinally.tryFinally'
        simp only [instMonadFinallyEST]
        simp [hx, hf]
      rw [io_bind_error hk] at h
      cases h
    | ok b w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .ok (a₀, b) w₂ := by
        rw [hu]
        unfold MonadFinally.tryFinally'
        simp only [instMonadFinallyEST]
        simp [hx, hf]
      rw [io_bind_ok hk] at h
      obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj h
      exact ⟨w₁, rfl, b, hf⟩

/-- `runSteps` at `IO`: on a run that reports no step, for each step there are worlds in which it gives 0. -/
theorem runSteps_io (run : Step → IO UInt32) (steps : List Step) (w w' : Void IO.RealWorld)
    (h : runSteps run steps w = .ok none w') :
    ∀ s ∈ steps, ∃ w₁ w₂, run s w₁ = .ok 0 w₂ := by
  induction steps generalizing w with
  | nil => simp
  | cons step rest ih =>
    intro s hs
    rw [runSteps] at h
    cases hrun : run step w with
    | error e w₁ =>
      rw [io_bind_error hrun] at h
      cases h
    | ok code w₁ =>
      rw [io_bind_ok hrun] at h
      split at h
      · rename_i hc
        have hzero : code = 0 := by simpa using hc
        subst hzero
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨w, w₁, hrun⟩
        · exact ih w₁ h s hs
      · cases h

/-- `runIn` gives 0 only when, for each step, there are worlds in which it gives 0. -/
theorem runIn_zero (target root : String) (w w' : Void IO.RealWorld)
    (h : runIn target root w = .ok 0 w') :
    ∀ s ∈ localSteps target root, ∃ w₁ w₂, runStep s w₁ = .ok 0 w₂ := by
  unfold runIn at h
  cases hr : runSteps runStep (localSteps target root) w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok r w₁ =>
    rw [io_bind_ok hr] at h
    cases hs : sayResult (localSteps target root) r w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok u w₂ =>
      rw [io_bind_ok hs] at h
      have hc : exitOf r = 0 := EST.Out.ok.inj h |>.1
      have hn := (exitOf_eq_zero_iff r).mp hc
      subst hn
      exact runSteps_io _ _ _ _ hr

/-- `regularFiles` holds each path that its test found no directory, and no other, in some worlds. -/
theorem regularFiles_io (paths : List System.FilePath) (w w' : Void IO.RealWorld) (files : List System.FilePath)
    (h : regularFiles paths w = .ok files w') :
    (∀ p ∈ files, p ∈ paths ∧ ∃ w₁ w₂, (p.isDir : IO Bool) w₁ = .ok false w₂) ∧
      ∀ p ∈ paths, p ∈ files ∨ ∃ w₁ w₂, (p.isDir : IO Bool) w₁ = .ok true w₂ := by
  induction paths generalizing w w' files with
  | nil =>
    rw [regularFiles] at h
    obtain ⟨rfl, -⟩ := EST.Out.ok.inj h
    simp
  | cons q rest ih =>
    rw [regularFiles] at h
    cases hq : (q.isDir : IO Bool) w with
    | error e w₁ =>
      rw [io_bind_error hq] at h
      cases h
    | ok d w₁ =>
      rw [io_bind_ok hq] at h
      cases hr : regularFiles rest w₁ with
      | error e w₂ =>
        rw [io_bind_error hr] at h
        cases h
      | ok others w₂ =>
        rw [io_bind_ok hr] at h
        obtain ⟨hf, -⟩ := EST.Out.ok.inj h
        obtain ⟨i1, i2⟩ := ih w₁ w₂ others hr
        subst hf
        cases d with
        | true =>
          refine ⟨fun p hp => ?_, fun p hp => ?_⟩
          · obtain ⟨a, b⟩ := i1 p (by simpa using hp)
            exact ⟨List.mem_cons_of_mem _ a, b⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact .inr ⟨w, w₁, hq⟩
            · rcases i2 p hp with x | x
              · exact .inl (by simpa using x)
              · exact .inr x
        | false =>
          refine ⟨fun p hp => ?_, fun p hp => ?_⟩
          · have hp' : p = q ∨ p ∈ others := by simpa using hp
            rcases hp' with rfl | hp'
            · exact ⟨List.mem_cons_self .., w, w₁, hq⟩
            · obtain ⟨a, b⟩ := i1 p hp'
              exact ⟨List.mem_cons_of_mem _ a, b⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact .inl (by simp)
            · rcases i2 p hp with x | x
              · exact .inl (by simp [x])
              · exact .inr x

/-- What `checkerFiles` gives: the three files of the configuration, and each path below `lean` that `walkDir` listed and that
is no directory, and no other path. -/
theorem checkerFiles_io (w w' : Void IO.RealWorld) (files : List System.FilePath) (h : checkerFiles w = .ok files w') :
    ∃ sources others w₁, System.FilePath.walkDir "lean" (fun _ => pure true) w = .ok sources w₁ ∧
      regularFiles sources.toList w₁ = .ok others w' ∧
      files = ["lakefile.toml", "lake-manifest.json", "lean-toolchain"].map System.FilePath.mk ++ others := by
  unfold checkerFiles at h
  cases hw : System.FilePath.walkDir "lean" (fun _ => pure true) w with
  | error e w₁ =>
    rw [io_bind_error hw] at h
    cases h
  | ok sources w₁ =>
    rw [io_bind_ok hw] at h
    cases hr : regularFiles sources.toList w₁ with
    | error e w₂ =>
      rw [io_bind_error hr] at h
      cases h
    | ok others w₂ =>
      rw [io_bind_ok hr] at h
      obtain ⟨hf, hw'⟩ := EST.Out.ok.inj h
      subst hw'
      exact ⟨sources, others, w₁, rfl, hr, hf.symm⟩

/-- A copy of one file that succeeds wrote to `target / file` the bytes that its read of `file` gave. This says nothing of where
`target / file` lies: `/` gives `file` itself for an absolute `file` (`FilePath.join`, `Init/System/FilePath.lean:126-130` at
v4.35.0), so such a copy writes to the file it read, and a relative `file` with `..` can leave `target`. `join_relative` states `/`
for a relative `file`, and `checkerFiles_io` states which files the gate passes. -/
theorem copyFile_io (target file : System.FilePath) (w w' : Void IO.RealWorld) (h : copyFile target file w = .ok () w') :
    ∃ bytes w₁ w₂, IO.FS.readBinFile file w₁ = .ok bytes w₂ ∧
      IO.FS.writeBinFile (target / file) bytes w₂ = .ok () w' := by
  unfold copyFile at h
  have hrest : ∀ w₀ : Void IO.RealWorld, ((do IO.FS.writeBinFile (target / file) (← IO.FS.readBinFile file)) : IO Unit) w₀ =
      .ok () w' → ∃ bytes w₁ w₂, IO.FS.readBinFile file w₁ = .ok bytes w₂ ∧
        IO.FS.writeBinFile (target / file) bytes w₂ = .ok () w' := by
    intro w₀ h₀
    cases hr : IO.FS.readBinFile file w₀ with
    | error e w₁ =>
      rw [io_bind_error hr] at h₀
      cases h₀
    | ok bytes w₁ =>
      rw [io_bind_ok hr] at h₀
      exact ⟨bytes, w₀, w₁, hr, h₀⟩
  cases hp : (target / file).parent with
  | none =>
    simp only [hp] at h
    exact hrest w h
  | some dir =>
    simp only [hp] at h
    cases hm : IO.FS.createDirAll dir w with
    | error e w₁ =>
      rw [io_bind_error hm] at h
      cases h
    | ok u w₁ =>
      rw [io_bind_ok hm] at h
      exact hrest w₁ h

/-- For a `file` that is not absolute, `target / file` is the text of `target`, a separator and the text of `file`. A `file` with
`..` can name a path outside `target`, so this is no statement of containment. -/
theorem join_relative (target file : System.FilePath) (h : file.isAbsolute = false) :
    target / file = System.FilePath.mk (target.toString ++ System.FilePath.pathSeparator.toString ++ file.toString) := by
  show System.FilePath.join target file = _
  simp [System.FilePath.join, h]

/-- A copy of a list of files that succeeds copied each. -/
theorem copyAll_io (target : System.FilePath) (files : List System.FilePath) (w w' : Void IO.RealWorld)
    (h : copyAll target files w = .ok () w') :
    ∀ file ∈ files, ∃ bytes w₁ w₂ w₃, IO.FS.readBinFile file w₁ = .ok bytes w₂ ∧
      IO.FS.writeBinFile (target / file) bytes w₂ = .ok () w₃ := by
  induction files generalizing w with
  | nil => simp
  | cons f rest ih =>
    intro file hf
    rw [copyAll] at h
    cases hc : copyFile target f w with
    | error e w₁ =>
      rw [io_bind_error hc] at h
      cases h
    | ok u w₁ =>
      rw [io_bind_ok hc] at h
      rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨bytes, a, b, h1, h2⟩ := copyFile_io target file w w₁ hc
        exact ⟨bytes, a, b, w₁, h1, h2⟩
      · exact ih w₁ h file hf

/-- `copyChecker` takes the files that `checkerFiles` gives, and for each, the bytes that a read of it gave are what a write to `target / file` took. -/
theorem copyChecker_io (target : System.FilePath) (w w' : Void IO.RealWorld) (h : copyChecker target w = .ok () w') :
    ∃ files w₁, checkerFiles w = .ok files w₁ ∧
      ∀ file ∈ files, ∃ bytes w₂ w₃ w₄, IO.FS.readBinFile file w₂ = .ok bytes w₃ ∧
        IO.FS.writeBinFile (target / file) bytes w₃ = .ok () w₄ := by
  unfold copyChecker at h
  cases hc : checkerFiles w with
  | error e w₁ =>
    rw [io_bind_error hc] at h
    cases h
  | ok files w₁ =>
    rw [io_bind_ok hc] at h
    exact ⟨files, w₁, rfl, copyAll_io target files w₁ w' h⟩

/-- What the whole gate establishes, at `IO`, from any state of the world: `runLocal` gives 0 only when it made its directory,
wrote to it joined with each file that `checkerFiles` gives the bytes it read of that file, and, with that directory as the
checker and the working directory as the project, for each step of `localSteps` there are worlds in which it gave 0. That a step
builds what was written and checks this checkout rests on what `localSteps` names, the file system and Lake, which this does not state. -/
theorem runLocal_zero (w w' : Void IO.RealWorld) (h : runLocal w = .ok 0 w') :
    ∃ target root w₁ w₂ w₃ w₄, IO.FS.createTempDir w = .ok target w₁ ∧ copyChecker target w₁ = .ok () w₂ ∧
      IO.currentDir w₂ = .ok root w₃ ∧ runIn target.toString root.toString w₃ = .ok 0 w₄ ∧
      ∀ s ∈ localSteps target.toString root.toString, ∃ a b, runStep s a = .ok 0 b := by
  unfold runLocal at h
  cases ht : IO.FS.createTempDir w with
  | error e w₁ =>
    rw [io_bind_error ht] at h
    cases h
  | ok target w₁ =>
    rw [io_bind_ok ht] at h
    have hfin := finally_ok h
    obtain ⟨w₂, hbody, -⟩ := hfin
    cases hc : copyChecker target w₁ with
    | error e w₃ =>
      rw [io_bind_error hc] at hbody
      cases hbody
    | ok u w₃ =>
      rw [io_bind_ok hc] at hbody
      cases hd : IO.currentDir w₃ with
      | error e w₄ =>
        rw [io_bind_error hd] at hbody
        cases hbody
      | ok root w₄ =>
        rw [io_bind_ok hd] at hbody
        exact ⟨target, root, w₁, w₃, w₄, w₂, rfl, hc, hd, hbody, runIn_zero _ _ _ _ hbody⟩

/-- The command line of the gate: it gives 0 only for the one argument `local`, on a run of `runLocal` that gave 0. -/
theorem main_zero (args : List String) (w w' : Void IO.RealWorld) (h : _root_.main args w = .ok 0 w') :
    args = ["local"] ∧ runLocal w = .ok 0 w' := by
  unfold _root_.main at h
  split at h
  · exact ⟨rfl, h⟩
  · exfalso
    cases he : IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean local" w with
    | error e w₁ =>
      rw [io_bind_error he] at h
      cases h
    | ok u w₁ =>
      rw [io_bind_ok he] at h
      have := (EST.Out.ok.inj h).1
      exact absurd this (by decide)

/-- The variable that the gate sets is the one that the checker reads. -/
theorem fullVariable_eq : fullVariable = Regula.Shell.fullVariable := rfl

/-- The steps of `localSteps`, in order, with each one's arguments, directory and project of the full gate. -/
theorem localSteps_eq (checker root : String) :
    localSteps checker root =
      [⟨["clean"], "specification", none⟩,
        ⟨["build", "lint"], checker, none⟩,
        ⟨["exe", "lint", "standard-logical"], checker, some root⟩,
        ⟨["build", "--wfail"], ".", none⟩,
        ⟨["build", "--wfail", "Regula", "lint"], ".", none⟩,
        ⟨["lint"], ".", none⟩,
        ⟨["build", "--wfail"], "specification", none⟩,
        ⟨["check", "--inadvisably-no-sandbox"], "specification", none⟩,
        ⟨["lint"], "specification", none⟩] := rfl

/-- Only the step that runs `lake exe lint standard-logical` names a project, and that project is `root`. -/
theorem localSteps_full (checker root : String) :
    ∀ s ∈ localSteps checker root,
      s.full = if s.arguments = ["exe", "lint", "standard-logical"] then some root else none := by
  simp [localSteps]

/-- What `runStep` does for any `step`, with no premise about how the call ends: it announces the step, starts the process that
`stepRequest` describes and waits for it. What the operating system and `lake` then do with the request is trusted. -/
theorem runStep_spawns (step : Step) :
    runStep step = (do
      announce step
      let child ← IO.Process.spawn (stepRequest step)
      child.wait) :=
  rfl

/-- The request for a step: `lake` with the step's arguments, in the step's directory, in an environment that removes the Lean
search paths, turns off Lake's artifact cache and binds `fullVariable` to the step's `full`, so `none` removes a value that the
gate inherited (`IO.Process.SpawnArgs.env`). -/
theorem stepRequest_eq (step : Step) :
    (stepRequest step).cmd = "lake" ∧
      (stepRequest step).args = step.arguments.toArray ∧
      (stepRequest step).cwd = some (System.FilePath.mk step.dir) ∧
      (stepRequest step).env =
        #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false"),
          (fullVariable, step.full)] :=
  ⟨rfl, rfl, rfl, rfl⟩

end RegulaSpecification.GateProgram
