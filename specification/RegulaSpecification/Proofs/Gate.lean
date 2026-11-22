module

public import Regula.DiagnosticsGate
public import Regula.Shell
import all Init.System.FilePath
import all Init.System.IO
import all Init.System.ST
import all Regula.DiagnosticsGate

@[expose] public section

namespace RegulaSpecification.GateProgram

open Regula.DiagnosticsGate

theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {a : α}
    (h : x w = .ok a w₁) : (x >>= f) w = f a w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

theorem io_bind_error {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {e : IO.Error}
    (h : x w = .error e w₁) : (x >>= f) w = .error e w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

theorem io_tryCatch_ok {α : Type} {x : IO α} {h : IO.Error → IO α} {w w₁ : Void IO.RealWorld} {a : α}
    (hx : x w = .ok a w₁) : (tryCatch x h) w = .ok a w₁ := by
  show EST.tryCatch x h w = _
  simp [EST.tryCatch, hx]

theorem io_tryCatch_error {α : Type} {x : IO α} {h : IO.Error → IO α} {w w₁ : Void IO.RealWorld} {e : IO.Error}
    (hx : x w = .error e w₁) : (tryCatch x h) w = h e w₁ := by
  show EST.tryCatch x h w = _
  simp [EST.tryCatch, hx]

theorem io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β) (g : β → IO γ)
    (w : Void IO.RealWorld) :
    ((x >>= f) >>= g) w = (x >>= fun a => f a >>= g) w := by
  show EST.bind (EST.bind x f) g w = EST.bind x (fun a => EST.bind (f a) g) w
  cases hx : x w <;> simp [EST.bind, hx]

theorem io_bind_tryCatch_error {α β : Type} {x : IO α} {h : IO.Error → IO α} {f : α → IO β}
    {w w₁ : Void IO.RealWorld} {e : IO.Error} (hx : x w = .error e w₁) :
    ((tryCatch x h) >>= f) w = ((h e) >>= f) w₁ := by
  show EST.bind (EST.tryCatch x h) f w = EST.bind (h e) f w₁
  simp [EST.bind, EST.tryCatch, hx]

theorem io_bind_throw {α β : Type} (e : IO.Error) (f : α → IO β) (w : Void IO.RealWorld) :
    ((throw e : IO α) >>= f) w = .error e w := by
  rfl

inductive FinallyOutcome {α β : Type} (x : IO α) (f : IO β) (w : Void IO.RealWorld) :
    EST.Out IO.Error IO.RealWorld α → Prop where
  | okOk (a : α) (b : β) (w₁ w₂ : Void IO.RealWorld) :
      x w = .ok a w₁ → f w₁ = .ok b w₂ → FinallyOutcome x f w (.ok a w₂)
  | okError (a : α) (e' : IO.Error) (w₁ w₂ : Void IO.RealWorld) :
      x w = .ok a w₁ → f w₁ = .error e' w₂ → FinallyOutcome x f w (.error e' w₂)
  | errorOk (e : IO.Error) (b : β) (w₁ w₂ : Void IO.RealWorld) :
      x w = .error e w₁ → f w₁ = .ok b w₂ → FinallyOutcome x f w (.error e w₂)
  | errorError (e e' : IO.Error) (w₁ w₂ : Void IO.RealWorld) :
      x w = .error e w₁ → f w₁ = .error e' w₂ → FinallyOutcome x f w (.error e' w₂)

theorem finally_spec {α β : Type} (x : IO α) (f : IO β) (w : Void IO.RealWorld) :
    FinallyOutcome x f w ((tryFinally x f) w) := by
  have hu : (tryFinally' x (fun _ => f) : IO (α × β)) w =
      (MonadFinally.tryFinally' (m := EST IO.Error IO.RealWorld) x (fun _ => f)) w := rfl
  have ht : (tryFinally x f) w =
      ((tryFinally' x (fun _ => f) : IO (α × β)) >>= fun p => pure p.1) w := rfl
  rw [ht]
  cases hx : x w with
  | error e w₁ =>
    cases hf : f w₁ with
    | error e' w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e' w₂ := by
        rw [hu]; unfold MonadFinally.tryFinally'; simp only [instMonadFinallyEST]; simp [hx, hf]
      rw [io_bind_error hk]
      exact .errorError e e' w₁ w₂ hx hf
    | ok b w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e w₂ := by
        rw [hu]; unfold MonadFinally.tryFinally'; simp only [instMonadFinallyEST]; simp [hx, hf]
      rw [io_bind_error hk]
      exact .errorOk e b w₁ w₂ hx hf
  | ok a₀ w₁ =>
    cases hf : f w₁ with
    | error e' w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .error e' w₂ := by
        rw [hu]; unfold MonadFinally.tryFinally'; simp only [instMonadFinallyEST]; simp [hx, hf]
      rw [io_bind_error hk]
      exact .okError a₀ e' w₁ w₂ hx hf
    | ok b w₂ =>
      have hk : (tryFinally' x (fun _ => f) : IO (α × β)) w = .ok (a₀, b) w₂ := by
        rw [hu]; unfold MonadFinally.tryFinally'; simp only [instMonadFinallyEST]; simp [hx, hf]
      rw [io_bind_ok hk]
      exact .okOk a₀ b w₁ w₂ hx hf

theorem finally_ok {α β : Type} {x : IO α} {f : IO β} {w w' : Void IO.RealWorld} {a : α}
    (h : (tryFinally x f) w = .ok a w') : ∃ w₁, x w = .ok a w₁ ∧ ∃ b, f w₁ = .ok b w' := by
  have hs := finally_spec x f w
  rw [h] at hs
  cases hs with
  | okOk a₀ b w₁ w₂ hx hf => exact ⟨w₁, hx, b, hf⟩

def stepRequest (step : Step) : IO.Process.SpawnArgs where
  cmd := "lake"
  args := step.arguments.toArray
  cwd := some (System.FilePath.mk step.dir)
  stdin := .null
  env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false"), ("REGULA_FULL", step.full)]

def StepRan (step : Step) (code : UInt32) (w w' : Void IO.RealWorld) : Prop :=
  ∃ w₁ w₂, ∃ child : IO.Process.Child (stepRequest step).toStdioConfig,
    announce step w = .ok () w₁ ∧ IO.Process.spawn (stepRequest step) w₁ = .ok child w₂ ∧ child.wait w₂ = .ok code w'

theorem runStep_ran (step : Step) (code : UInt32) (w w' : Void IO.RealWorld) (h : runStep step w = .ok code w') :
    StepRan step code w w' := by
  unfold runStep at h
  cases ha : announce step w with
  | error e w₁ =>
    rw [io_bind_error ha] at h
    cases h
  | ok u w₁ =>
    cases u
    rw [io_bind_ok ha] at h
    change ((IO.Process.spawn (stepRequest step)) >>= IO.Process.Child.wait) w₁ = .ok code w' at h
    cases hs : IO.Process.spawn (stepRequest step) w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok child w₂ =>
      rw [io_bind_ok hs] at h
      exact ⟨w₁, w₂, child, ha, hs, h⟩

inductive StepsAllZero : List Step → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w : Void IO.RealWorld) : StepsAllZero [] w w
  | cons {step : Step} {rest : List Step} {w w₁ w₂ : Void IO.RealWorld} :
      StepRan step 0 w w₁ → StepsAllZero rest w₁ w₂ → StepsAllZero (step :: rest) w w₂

theorem StepsAllZero.mem {steps : List Step} {w w' : Void IO.RealWorld}
    (h : StepsAllZero steps w w') : ∀ s ∈ steps, ∃ w₁ w₂, StepRan s 0 w₁ w₂ := by
  induction h with
  | nil _ => simp
  | cons hstep _ ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨_, _, hstep⟩
    · exact ih s hs

inductive StepsOutcome (steps : List Step) (w : Void IO.RealWorld) :
    EST.Out IO.Error IO.RealWorld (Option (Step × UInt32)) → Prop where
  | allZero (w' : Void IO.RealWorld) :
      StepsAllZero steps w w' →
      StepsOutcome steps w (.ok none w')
  | failed (pre post : List Step) (step : Step) (code : UInt32) (w₁ w' : Void IO.RealWorld) :
      steps = pre ++ step :: post →
      StepsAllZero pre w w₁ →
      StepRan step code w₁ w' →
      code ≠ 0 →
      StepsOutcome steps w (.ok (some (step, code)) w')
  | errored (pre post : List Step) (step : Step) (e : IO.Error) (w₁ w' : Void IO.RealWorld) :
      steps = pre ++ step :: post →
      StepsAllZero pre w w₁ →
      runStep step w₁ = .error e w' →
      StepsOutcome steps w (.error e w')

theorem runSteps_outcome (steps : List Step) (w : Void IO.RealWorld) :
    StepsOutcome steps w (runSteps runStep steps w) := by
  induction steps generalizing w with
  | nil =>
    rw [runSteps.eq_def]
    exact .allZero w (.nil w)
  | cons step rest ih =>
    rw [runSteps.eq_def]
    dsimp only
    cases hrun : runStep step w with
    | error e w₁ =>
      rw [io_bind_error hrun]
      exact .errored [] rest step e w w₁ rfl (.nil w) hrun
    | ok code w₁ =>
      rw [io_bind_ok hrun]
      have hran := runStep_ran step code w w₁ hrun
      by_cases hzero : code = 0
      · subst hzero
        have hbeq : ((0 : UInt32) == 0) = true := rfl
        simp only [hbeq, ↓reduceIte]
        have hih := ih w₁
        generalize hrestEq : runSteps runStep rest w₁ = restRes at hih ⊢
        cases hih with
        | allZero w' hrest =>
          exact .allZero w' (.cons hran hrest)
        | failed pre post s c w₂ w' heq hpre hs hc =>
          exact .failed (step :: pre) post s c w₂ w' (by simp [heq]) (.cons hran hpre) hs hc
        | errored pre post s e w₂ w' heq hpre hs =>
          exact .errored (step :: pre) post s e w₂ w' (by simp [heq]) (.cons hran hpre) hs
      · have hbeq : (code == 0) = false := by simp [hzero]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        exact .failed [] rest step code w w₁ rfl (.nil w) hran hzero

theorem runSteps_allZero (steps : List Step) (w w' : Void IO.RealWorld)
    (h : runSteps runStep steps w = .ok none w') : StepsAllZero steps w w' := by
  have ho := runSteps_outcome steps w
  rw [h] at ho
  cases ho with
  | allZero _ hall => exact hall

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

def expectedSha256Spec : NoCommentsTarget → String
  | .darwinArm64 => "4c610e1b0f0f93f54e89f33acb13c5120ed4e7ecfc3bb5db85e562aba637fe2a"
  | .linuxX86_64 => "f1a5d5cee2214515f9d36d3bb7245beee3856c06a85f6593ac0b23c4a0c6941e"

def sha256RequestSpec : NoCommentsTarget → System.FilePath → IO.Process.SpawnArgs
  | .darwinArm64, path =>
    { cmd := "shasum", args := #["-a", "256", "--", path.toString], stdin := .null }
  | .linuxX86_64, path =>
    { cmd := "sha256sum", args := #["--", path.toString], stdin := .null }

theorem target_sha256_eq (target : NoCommentsTarget) :
    target.sha256 = expectedSha256Spec target := by
  cases target <;> rfl

theorem sha256Request_eq (target : NoCommentsTarget) (path : System.FilePath) :
    sha256Request target path = sha256RequestSpec target path := by
  cases target <;> rfl

def Sha256OutputMatches (digest stdout : String) : Prop :=
  ∃ name : String,
    name ≠ "" ∧ '\n' ∉ name.toList ∧
    (stdout = digest ++ "  " ++ name ++ "\n" ∨
     stdout = "\\" ++ digest ++ "  " ++ name ++ "\n")

theorem isSingleFileLine_iff (cs : List Char) :
    isSingleFileLine cs = true ↔
      ∃ name : String, name ≠ "" ∧ '\n' ∉ name.toList ∧ cs = name.toList ++ ['\n'] := by
  unfold isSingleFileLine
  cases hr : cs.reverse with
  | nil =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro name _ _ hcs
    have hrev := congrArg List.reverse hcs
    simp [hr] at hrev
  | cons c rname =>
    by_cases hc : c = '\n'
    · subst hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      constructor
      · rintro ⟨hne, hmem⟩
        have hnotmem : '\n' ∉ rname := by
          intro hm
          have ht : rname.contains '\n' = true := List.contains_iff_mem.mpr hm
          rw [ht] at hmem
          cases hmem
        refine ⟨String.ofList rname.reverse, ?_, ?_, ?_⟩
        · intro heq
          have hl := congrArg String.toList heq
          simp at hl
          exact hne hl
        · simpa using hnotmem
        · have hrev := congrArg List.reverse hr
          simpa using hrev
      · rintro ⟨name, hne, hmem, hcs⟩
        have hrev : cs.reverse = '\n' :: name.toList.reverse := by
          rw [hcs]
          simp
        rw [hr] at hrev
        obtain ⟨-, rfl⟩ := List.cons.inj hrev
        refine ⟨?_, ?_⟩
        · intro hemp
          have hl : name.toList = [] := by simpa using hemp
          exact hne (String.toList_inj.mp hl)
        · cases hct : name.toList.reverse.contains '\n' with
          | false => rfl
          | true =>
            have hm : '\n' ∈ name.toList := by simpa using List.contains_iff_mem.mp hct
            exact absurd hm hmem
    · split
      · rename_i r heq
        exact absurd (List.cons.inj heq).1 hc
      · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro name _ _ hcs
        have hrev : cs.reverse = '\n' :: name.toList.reverse := by
          rw [hcs]
          simp
        rw [hr] at hrev
        exact hc (List.cons.inj hrev).1

theorem prefix_singleFileLine_iff (pref s : String) :
    (pref.toList.isPrefixOf s.toList && isSingleFileLine (s.toList.drop pref.toList.length)) = true ↔
      ∃ name : String, name ≠ "" ∧ '\n' ∉ name.toList ∧ s = pref ++ name ++ "\n" := by
  simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix, isSingleFileLine_iff]
  constructor
  · rintro ⟨⟨t, ht⟩, name, hne, hmem, hdrop⟩
    rw [← ht, List.drop_left] at hdrop
    subst hdrop
    refine ⟨name, hne, hmem, ?_⟩
    apply String.toList_inj.mp
    rw [← ht]
    simp [List.append_assoc]
  · rintro ⟨name, hne, hmem, rfl⟩
    refine ⟨⟨name.toList ++ ['\n'], ?_⟩, name, hne, hmem, ?_⟩
    · simp [List.append_assoc]
    · have hlist : (pref ++ name ++ "\n").toList = pref.toList ++ (name.toList ++ ['\n']) := by
        simp [List.append_assoc]
      rw [hlist, List.drop_left]

theorem sha256Matches_iff (expected : String) (out : IO.Process.Output) :
    sha256Matches expected out = true ↔
      out.exitCode = 0 ∧ Sha256OutputMatches expected out.stdout := by
  unfold sha256Matches
  dsimp only
  have hbs : ('\\' :: (expected ++ "  ").toList) = ("\\" ++ expected ++ "  ").toList := by
    simp [String.toList_append]
  have hlen : (expected ++ "  ").toList.length + 1 = ("\\" ++ expected ++ "  ").toList.length := by
    rw [← hbs]
    simp
  rw [hbs, hlen, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    prefix_singleFileLine_iff, prefix_singleFileLine_iff]
  unfold Sha256OutputMatches
  constructor
  · rintro ⟨hcode, ⟨name, hne, hmem, hs⟩ | ⟨name, hne, hmem, hs⟩⟩
    · exact ⟨hcode, name, hne, hmem, .inl hs⟩
    · exact ⟨hcode, name, hne, hmem, .inr hs⟩
  · rintro ⟨hcode, name, hne, hmem, hs | hs⟩
    · exact ⟨hcode, .inl ⟨name, hne, hmem, hs⟩⟩
    · exact ⟨hcode, .inr ⟨name, hne, hmem, hs⟩⟩

def Sha256Verified (target : NoCommentsTarget) (path : System.FilePath)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ out : IO.Process.Output,
    (IO.Process.output (sha256RequestSpec target path) : IO IO.Process.Output) w = .ok out w' ∧
    out.exitCode = 0 ∧
    Sha256OutputMatches (expectedSha256Spec target) out.stdout

inductive VerifySha256Outcome (target : NoCommentsTarget) (path : System.FilePath)
    (w : Void IO.RealWorld) : EST.Out IO.Error IO.RealWorld Unit → Prop where
  | verified (w' : Void IO.RealWorld) :
      Sha256Verified target path w w' →
      VerifySha256Outcome target path w (.ok () w')
  | outputError (e : IO.Error) (w' : Void IO.RealWorld) :
      (IO.Process.output (sha256RequestSpec target path) : IO IO.Process.Output) w = .error e w' →
      VerifySha256Outcome target path w (.error e w')
  | mismatch (out : IO.Process.Output) (e : IO.Error) (w' : Void IO.RealWorld) :
      (IO.Process.output (sha256RequestSpec target path) : IO IO.Process.Output) w = .ok out w' →
      ¬ (out.exitCode = 0 ∧ Sha256OutputMatches (expectedSha256Spec target) out.stdout) →
      VerifySha256Outcome target path w (.error e w')

theorem verifySha256_outcome (target : NoCommentsTarget) (path : System.FilePath)
    (w : Void IO.RealWorld) :
    VerifySha256Outcome target path w (verifySha256 target path w) := by
  unfold verifySha256
  rw [sha256Request_eq, target_sha256_eq]
  cases ho : (IO.Process.output (sha256RequestSpec target path) : IO IO.Process.Output) w with
  | error e w₁ =>
    rw [io_bind_error ho]
    exact .outputError e w₁ ho
  | ok out w₁ =>
    rw [io_bind_ok ho]
    cases hm : sha256Matches (expectedSha256Spec target) out with
    | true =>
      simp only [↓reduceIte]
      obtain ⟨hcode, hmatch⟩ := (sha256Matches_iff (expectedSha256Spec target) out).mp hm
      exact .verified w₁ ⟨out, ho, hcode, hmatch⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ (out.exitCode = 0 ∧ Sha256OutputMatches (expectedSha256Spec target) out.stdout) := by
        intro h
        have ht := (sha256Matches_iff (expectedSha256Spec target) out).mpr h
        rw [hm] at ht
        cases ht
      exact .mismatch out _ w₁ ho hnot

theorem verifySha256_ok (target : NoCommentsTarget) (path : System.FilePath)
    (w w' : Void IO.RealWorld) (h : verifySha256 target path w = .ok () w') :
    Sha256Verified target path w w' := by
  have ho := verifySha256_outcome target path w
  rw [h] at ho
  cases ho with
  | verified _ hv => exact hv

theorem samePath_iff (a b : System.FilePath) :
    samePath a b = true ↔ a.isAbsolute = b.isAbsolute ∧ pathParts a = pathParts b := by
  simp [samePath]

theorem symlinkType?_some (p : System.FilePath) (t : IO.FS.FileType) (w w' : Void IO.RealWorld)
    (h : symlinkType? p w = .ok (some t) w') :
    ∃ m : IO.FS.Metadata, p.symlinkMetadata w = .ok m w' ∧ m.type = t := by
  unfold symlinkType? at h
  cases hm : p.symlinkMetadata w with
  | ok m w₁ =>
    have hbody : (do let m ← p.symlinkMetadata; pure (some m.type) : IO (Option IO.FS.FileType)) w =
        .ok (some m.type) w₁ := by
      rw [io_bind_ok hm]
      rfl
    rw [io_tryCatch_ok hbody] at h
    obtain ⟨ht, rfl⟩ := EST.Out.ok.inj h
    exact ⟨m, rfl, Option.some.inj ht⟩
  | error e w₁ =>
    have hbody : (do let m ← p.symlinkMetadata; pure (some m.type) : IO (Option IO.FS.FileType)) w =
        .error e w₁ := by
      rw [io_bind_error hm]
    rw [io_tryCatch_error hbody] at h
    cases e <;> cases h

theorem symlinkType?_none (p : System.FilePath) (w w' : Void IO.RealWorld)
    (h : symlinkType? p w = .ok none w') :
    ∃ name code details, p.symlinkMetadata w = .error (.noFileOrDirectory name code details) w' := by
  unfold symlinkType? at h
  cases hm : p.symlinkMetadata w with
  | ok m w₁ =>
    have hbody : (do let m ← p.symlinkMetadata; pure (some m.type) : IO (Option IO.FS.FileType)) w =
        .ok (some m.type) w₁ := by
      rw [io_bind_ok hm]
      rfl
    rw [io_tryCatch_ok hbody] at h
    cases h
  | error e w₁ =>
    have hbody : (do let m ← p.symlinkMetadata; pure (some m.type) : IO (Option IO.FS.FileType)) w =
        .error e w₁ := by
      rw [io_bind_error hm]
    rw [io_tryCatch_error hbody] at h
    cases e with
    | noFileOrDirectory name code details =>
      obtain ⟨_, rfl⟩ := EST.Out.ok.inj h
      exact ⟨name, code, details, rfl⟩
    | _ => cases h

theorem requireExactRealPath_ok (label : String) (p real : System.FilePath)
    (w w' : Void IO.RealWorld) (h : requireExactRealPath label p w = .ok real w') :
    IO.FS.realPath p w = .ok real w' ∧
      real.isAbsolute = p.isAbsolute ∧ pathParts real = pathParts p := by
  unfold requireExactRealPath at h
  cases hr : IO.FS.realPath p w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok r w₁ =>
    rw [io_bind_ok hr] at h
    cases hs : samePath r p with
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    | true =>
      simp only [hs, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj h
      obtain ⟨habs, hparts⟩ := (samePath_iff r p).mp hs
      exact ⟨rfl, habs, hparts⟩

def SubdirEstablished (parent : System.FilePath) (name : String) (real : System.FilePath)
    (w w' : Void IO.RealWorld) : Prop :=
  ∃ w₁,
    ((∃ m : IO.FS.Metadata, (parent / name).symlinkMetadata w = .ok m w₁ ∧ m.type = .dir) ∨
     (∃ path code details w₀,
        (parent / name).symlinkMetadata w = .error (.noFileOrDirectory path code details) w₀ ∧
        (IO.FS.createDir (parent / name) w₀ = .ok () w₁ ∨
         ∃ e w₂ m, IO.FS.createDir (parent / name) w₀ = .error e w₂ ∧
           (parent / name).symlinkMetadata w₂ = .ok m w₁ ∧ m.type = .dir))) ∧
    IO.FS.realPath (parent / name) w₁ = .ok real w' ∧
    real.isAbsolute = (parent / name).isAbsolute ∧
    pathParts real = pathParts (parent / name)

theorem ensureSubdir_ok (parent : System.FilePath) (name : String) (real : System.FilePath)
    (w w' : Void IO.RealWorld) (h : ensureSubdir parent name w = .ok real w') :
    SubdirEstablished parent name real w w' := by
  unfold ensureSubdir at h
  cases ht : symlinkType? (parent / name) w with
  | error e w₁ =>
    rw [io_bind_error ht] at h
    cases h
  | ok ot w₁ =>
    rw [io_bind_ok ht] at h
    cases ot with
    | some t =>
      cases t with
      | dir =>
        obtain ⟨m, hm, hmt⟩ := symlinkType?_some _ _ _ _ ht
        obtain ⟨hr, habs, hparts⟩ := requireExactRealPath_ok _ _ _ _ _ h
        exact ⟨w₁, .inl ⟨m, hm, hmt⟩, hr, habs, hparts⟩
      | file | symlink | other => cases h
    | none =>
      dsimp only at h
      obtain ⟨path, code, details, hno⟩ := symlinkType?_none _ _ _ ht
      cases hc : IO.FS.createDir (parent / name) w₁ with
      | ok u w₂ =>
        cases u
        rw [io_bind_ok (io_tryCatch_ok hc)] at h
        obtain ⟨hr, habs, hparts⟩ := requireExactRealPath_ok _ _ _ _ _ h
        exact ⟨w₂, .inr ⟨path, code, details, w₁, hno, .inl hc⟩, hr, habs, hparts⟩
      | error e w₂ =>
        rw [io_bind_tryCatch_error hc, io_bind_assoc] at h
        cases ht2 : symlinkType? (parent / name) w₂ with
        | error e2 w₃ =>
          rw [io_bind_error ht2] at h
          cases h
        | ok ot2 w₃ =>
          rw [io_bind_ok ht2] at h
          cases ot2 with
          | some t2 =>
            cases t2 with
            | dir =>
              dsimp only at h
              have hpure : (pure () : IO Unit) w₃ = .ok () w₃ := rfl
              rw [io_bind_ok hpure] at h
              obtain ⟨m, hm, hmt⟩ := symlinkType?_some _ _ _ _ ht2
              obtain ⟨hr, habs, hparts⟩ := requireExactRealPath_ok _ _ _ _ _ h
              exact ⟨w₃, .inr ⟨path, code, details, w₁, hno, .inr ⟨e, w₂, m, hc, hm, hmt⟩⟩, hr, habs, hparts⟩
            | file | symlink | other =>
              dsimp only at h
              have hthrow : (throw e : IO Unit) w₃ = .error e w₃ := rfl
              rw [io_bind_error hthrow] at h
              cases h
          | none =>
            dsimp only at h
            have hthrow : (throw e : IO Unit) w₃ = .error e w₃ := rfl
            rw [io_bind_error hthrow] at h
            cases h

def CacheDirEstablished (dir : System.FilePath) (w w' : Void IO.RealWorld) : Prop :=
  ∃ root d1 d2 w₁ w₂ w₃,
    IO.FS.realPath "." w = .ok root w₁ ∧
    SubdirEstablished root ".cache" d1 w₁ w₂ ∧
    SubdirEstablished d1 "no-comments" d2 w₂ w₃ ∧
    SubdirEstablished d2 "v0.2.0" dir w₃ w'

theorem ensureNoCommentsCacheDir_ok (dir : System.FilePath) (w w' : Void IO.RealWorld)
    (h : ensureNoCommentsCacheDir w = .ok dir w') :
    CacheDirEstablished dir w w' := by
  unfold ensureNoCommentsCacheDir at h
  cases hr : IO.FS.realPath "." w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok root w₁ =>
    rw [io_bind_ok hr] at h
    cases h1 : ensureSubdir root ".cache" w₁ with
    | error e w₂ =>
      rw [io_bind_error h1] at h
      cases h
    | ok d1 w₂ =>
      rw [io_bind_ok h1] at h
      cases h2 : ensureSubdir d1 "no-comments" w₂ with
      | error e w₃ =>
        rw [io_bind_error h2] at h
        cases h
      | ok d2 w₃ =>
        rw [io_bind_ok h2] at h
        exact ⟨root, d1, d2, w₁, w₂, w₃, hr,
          ensureSubdir_ok _ _ _ _ _ h1,
          ensureSubdir_ok _ _ _ _ _ h2,
          ensureSubdir_ok _ _ _ _ _ h⟩

def stageCurlRequest (target : NoCommentsTarget) (tmpPath : System.FilePath) : IO.Process.SpawnArgs where
  cmd := "curl"
  args := #["-fsSL", "--retry", "3", "--retry-delay", "2", "-o", tmpPath.toString, target.url]
  stdin := .null

def StageDownloaded (target : NoCommentsTarget) (tmpPath : System.FilePath)
    (w w₄ : Void IO.RealWorld) : Prop :=
  ∃ stream out w₁ w₂ w₃,
    IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .ok () w₁ ∧
    (IO.getStdout : IO IO.FS.Stream) w₁ = .ok stream w₂ ∧
    stream.flush w₂ = .ok () w₃ ∧
    (IO.Process.output (stageCurlRequest target tmpPath) : IO IO.Process.Output) w₃ = .ok out w₄ ∧
    out.exitCode = 0

def StagePreFailed (target : NoCommentsTarget) (tmpPath : System.FilePath) (e : IO.Error)
    (w w' : Void IO.RealWorld) : Prop :=
  IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .error e w' ∨
  (∃ w₁, IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .ok () w₁ ∧
    (IO.getStdout : IO IO.FS.Stream) w₁ = .error e w') ∨
  (∃ stream w₁ w₂,
    IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .ok () w₁ ∧
    (IO.getStdout : IO IO.FS.Stream) w₁ = .ok stream w₂ ∧
    stream.flush w₂ = .error e w') ∨
  (∃ stream w₁ w₂ w₃,
    IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .ok () w₁ ∧
    (IO.getStdout : IO IO.FS.Stream) w₁ = .ok stream w₂ ∧
    stream.flush w₂ = .ok () w₃ ∧
    (IO.Process.output (stageCurlRequest target tmpPath) : IO IO.Process.Output) w₃ = .error e w') ∨
  (∃ stream out w₁ w₂ w₃,
    IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w = .ok () w₁ ∧
    (IO.getStdout : IO IO.FS.Stream) w₁ = .ok stream w₂ ∧
    stream.flush w₂ = .ok () w₃ ∧
    (IO.Process.output (stageCurlRequest target tmpPath) : IO IO.Process.Output) w₃ = .ok out w' ∧
    out.exitCode ≠ 0)

inductive StageOutcome (target : NoCommentsTarget) (cachePath tmpPath : System.FilePath)
    (w : Void IO.RealWorld) : EST.Out IO.Error IO.RealWorld Unit → Prop where
  | downloadFailed (e : IO.Error) (w' : Void IO.RealWorld) :
      StagePreFailed target tmpPath e w w' →
      StageOutcome target cachePath tmpPath w (.error e w')
  | metadataError (e : IO.Error) (w₄ w₅ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .error e w₅ →
      StageOutcome target cachePath tmpPath w (.error e w₅)
  | notRegularFile (meta_ : IO.FS.Metadata) (e : IO.Error) (w₄ w₅ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type ≠ .file →
      StageOutcome target cachePath tmpPath w (.error e w₅)
  | realPathError (meta_ : IO.FS.Metadata) (e : IO.Error) (w₄ w₅ w₆ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .error e w₆ →
      StageOutcome target cachePath tmpPath w (.error e w₆)
  | outsideCache (meta_ : IO.FS.Metadata) (realTmp : System.FilePath) (e : IO.Error)
      (w₄ w₅ w₆ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      ¬ (realTmp.isAbsolute = tmpPath.isAbsolute ∧ pathParts realTmp = pathParts tmpPath) →
      StageOutcome target cachePath tmpPath w (.error e w₆)
  | sha256OutputError (meta_ : IO.FS.Metadata) (realTmp : System.FilePath) (e : IO.Error)
      (w₄ w₅ w₆ w₇ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      realTmp.isAbsolute = tmpPath.isAbsolute →
      pathParts realTmp = pathParts tmpPath →
      (IO.Process.output (sha256RequestSpec target realTmp) : IO IO.Process.Output) w₆ = .error e w₇ →
      StageOutcome target cachePath tmpPath w (.error e w₇)
  | sha256Mismatch (meta_ : IO.FS.Metadata) (realTmp : System.FilePath) (out : IO.Process.Output)
      (e : IO.Error) (w₄ w₅ w₆ w₇ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      realTmp.isAbsolute = tmpPath.isAbsolute →
      pathParts realTmp = pathParts tmpPath →
      (IO.Process.output (sha256RequestSpec target realTmp) : IO IO.Process.Output) w₆ = .ok out w₇ →
      ¬ (out.exitCode = 0 ∧ Sha256OutputMatches (expectedSha256Spec target) out.stdout) →
      StageOutcome target cachePath tmpPath w (.error e w₇)
  | chmodError (meta_ : IO.FS.Metadata) (realTmp : System.FilePath) (e : IO.Error)
      (w₄ w₅ w₆ w₇ w₈ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      realTmp.isAbsolute = tmpPath.isAbsolute →
      pathParts realTmp = pathParts tmpPath →
      Sha256Verified target realTmp w₆ w₇ →
      IO.setAccessRights realTmp executableRight w₇ = .error e w₈ →
      StageOutcome target cachePath tmpPath w (.error e w₈)
  | renameError (meta_ : IO.FS.Metadata) (realTmp : System.FilePath) (e : IO.Error)
      (w₄ w₅ w₆ w₇ w₈ w₉ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      realTmp.isAbsolute = tmpPath.isAbsolute →
      pathParts realTmp = pathParts tmpPath →
      Sha256Verified target realTmp w₆ w₇ →
      IO.setAccessRights realTmp executableRight w₇ = .ok () w₈ →
      IO.FS.rename realTmp cachePath w₈ = .error e w₉ →
      StageOutcome target cachePath tmpPath w (.error e w₉)
  | published (meta_ : IO.FS.Metadata) (realTmp : System.FilePath)
      (w₄ w₅ w₆ w₇ w₈ w₉ : Void IO.RealWorld) :
      StageDownloaded target tmpPath w w₄ →
      tmpPath.symlinkMetadata w₄ = .ok meta_ w₅ →
      meta_.type = .file →
      IO.FS.realPath tmpPath w₅ = .ok realTmp w₆ →
      realTmp.isAbsolute = tmpPath.isAbsolute →
      pathParts realTmp = pathParts tmpPath →
      Sha256Verified target realTmp w₆ w₇ →
      IO.setAccessRights realTmp executableRight w₇ = .ok () w₈ →
      IO.FS.rename realTmp cachePath w₈ = .ok () w₉ →
      StageOutcome target cachePath tmpPath w (.ok () w₉)

theorem stageNoComments_outcome (target : NoCommentsTarget) (cachePath tmpPath : System.FilePath)
    (w : Void IO.RealWorld) :
    StageOutcome target cachePath tmpPath w (stageNoComments target cachePath tmpPath w) := by
  unfold stageNoComments
  cases hp : IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})" w with
  | error e w₁ =>
    rw [io_bind_error hp]
    exact .downloadFailed e w₁ (.inl hp)
  | ok u w₁ =>
    cases u
    rw [io_bind_ok hp]
    cases hg : (IO.getStdout : IO IO.FS.Stream) w₁ with
    | error e w₂ =>
      rw [io_bind_error hg]
      exact .downloadFailed e w₂ (.inr (.inl ⟨w₁, hp, hg⟩))
    | ok stream w₂ =>
      rw [io_bind_ok hg]
      cases hf : stream.flush w₂ with
      | error e w₃ =>
        rw [io_bind_error hf]
        exact .downloadFailed e w₃ (.inr (.inr (.inl ⟨stream, w₁, w₂, hp, hg, hf⟩)))
      | ok u w₃ =>
        cases u
        rw [io_bind_ok hf]
        change StageOutcome target cachePath tmpPath w
          ((IO.Process.output (stageCurlRequest target tmpPath) >>= _) w₃)
        cases hc : (IO.Process.output (stageCurlRequest target tmpPath) : IO IO.Process.Output) w₃ with
        | error e w₄ =>
          rw [io_bind_error hc]
          exact .downloadFailed e w₄ (.inr (.inr (.inr (.inl ⟨stream, w₁, w₂, w₃, hp, hg, hf, hc⟩))))
        | ok out w₄ =>
          rw [io_bind_ok hc]
          by_cases hcode : out.exitCode = 0
          · have hne : (out.exitCode != 0) = false := by simp [hcode]
            simp only [hne, Bool.false_eq_true, ↓reduceIte]
            have hdl : StageDownloaded target tmpPath w w₄ := ⟨stream, out, w₁, w₂, w₃, hp, hg, hf, hc, hcode⟩
            cases hm : tmpPath.symlinkMetadata w₄ with
            | error e w₅ =>
              rw [io_bind_error hm]
              exact .metadataError e w₄ w₅ hdl hm
            | ok meta_ w₅ =>
              rw [io_bind_ok hm]
              cases htype : meta_.type with
              | dir =>
                have hne : (IO.FS.FileType.dir != IO.FS.FileType.file) = true := rfl
                simp only [hne, ↓reduceIte]
                exact .notRegularFile meta_ _ w₄ w₅ hdl hm (by simp [htype])
              | symlink =>
                have hne : (IO.FS.FileType.symlink != IO.FS.FileType.file) = true := rfl
                simp only [hne, ↓reduceIte]
                exact .notRegularFile meta_ _ w₄ w₅ hdl hm (by simp [htype])
              | other =>
                have hne : (IO.FS.FileType.other != IO.FS.FileType.file) = true := rfl
                simp only [hne, ↓reduceIte]
                exact .notRegularFile meta_ _ w₄ w₅ hdl hm (by simp [htype])
              | file =>
                have hfile : (IO.FS.FileType.file != IO.FS.FileType.file) = false := rfl
                simp only [hfile, Bool.false_eq_true, ↓reduceIte]
                unfold requireExactRealPath
                rw [io_bind_assoc]
                cases hreal : IO.FS.realPath tmpPath w₅ with
                | error e w₆ =>
                  rw [io_bind_error hreal]
                  exact .realPathError meta_ e w₄ w₅ w₆ hdl hm htype hreal
                | ok realTmp w₆ =>
                  rw [io_bind_ok hreal]
                  cases hsame : samePath realTmp tmpPath with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [io_bind_throw]
                    have hnot : ¬ (realTmp.isAbsolute = tmpPath.isAbsolute ∧ pathParts realTmp = pathParts tmpPath) := by
                      intro hs
                      have ht := (samePath_iff realTmp tmpPath).mpr hs
                      rw [hsame] at ht
                      cases ht
                    exact .outsideCache meta_ realTmp _ w₄ w₅ w₆ hdl hm htype hreal hnot
                  | true =>
                    simp only [↓reduceIte]
                    obtain ⟨habs, hparts⟩ := (samePath_iff realTmp tmpPath).mp hsame
                    have hpure : (pure realTmp : IO System.FilePath) w₆ = .ok realTmp w₆ := rfl
                    rw [io_bind_ok hpure]
                    have hv := verifySha256_outcome target realTmp w₆
                    cases hveq : verifySha256 target realTmp w₆ with
                    | error e w₇ =>
                      rw [io_bind_error hveq]
                      rw [hveq] at hv
                      cases hv with
                      | outputError _ _ ho =>
                        exact .sha256OutputError meta_ realTmp e w₄ w₅ w₆ w₇ hdl hm htype hreal habs hparts ho
                      | mismatch hout _ _ ho hnot =>
                        exact .sha256Mismatch meta_ realTmp hout e w₄ w₅ w₆ w₇ hdl hm htype hreal habs hparts ho hnot
                    | ok u w₇ =>
                      cases u
                      rw [io_bind_ok hveq]
                      rw [hveq] at hv
                      cases hv with
                      | verified _ hsha =>
                        cases hch : IO.setAccessRights realTmp executableRight w₇ with
                        | error e w₈ =>
                          rw [io_bind_error hch]
                          exact .chmodError meta_ realTmp e w₄ w₅ w₆ w₇ w₈ hdl hm htype hreal habs hparts hsha hch
                        | ok u w₈ =>
                          cases u
                          rw [io_bind_ok hch]
                          cases hren : IO.FS.rename realTmp cachePath w₈ with
                          | error e w₉ =>
                            exact .renameError meta_ realTmp e w₄ w₅ w₆ w₇ w₈ w₉ hdl hm htype hreal habs hparts hsha hch hren
                          | ok u w₉ =>
                            cases u
                            exact .published meta_ realTmp w₄ w₅ w₆ w₇ w₈ w₉ hdl hm htype hreal habs hparts hsha hch hren
          · have hne : (out.exitCode != 0) = true := by simp [hcode]
            simp only [hne, ↓reduceIte]
            exact .downloadFailed _ w₄ (.inr (.inr (.inr (.inr ⟨stream, out, w₁, w₂, w₃, hp, hg, hf, hc, hcode⟩))))

theorem stageNoComments_ok (target : NoCommentsTarget) (cachePath tmpPath : System.FilePath)
    (w w' : Void IO.RealWorld) (h : stageNoComments target cachePath tmpPath w = .ok () w') :
    ∃ realTmp meta_ w₁ w₂ w₃ w₄ w₅,
      tmpPath.symlinkMetadata w₁ = .ok meta_ w₂ ∧
      meta_.type = .file ∧
      IO.FS.realPath tmpPath w₂ = .ok realTmp w₃ ∧
      realTmp.isAbsolute = tmpPath.isAbsolute ∧
      pathParts realTmp = pathParts tmpPath ∧
      Sha256Verified target realTmp w₃ w₄ ∧
      IO.setAccessRights realTmp executableRight w₄ = .ok () w₅ ∧
      IO.FS.rename realTmp cachePath w₅ = .ok () w' := by
  have ho := stageNoComments_outcome target cachePath tmpPath w
  rw [h] at ho
  cases ho with
  | published meta_ realTmp w₄ w₅ w₆ w₇ w₈ _ _ hm htype hreal habs hparts hsha hch hren =>
    exact ⟨realTmp, meta_, w₄, w₅, w₆, w₇, w₈, hm, htype, hreal, habs, hparts, hsha, hch, hren⟩

theorem downloadNoComments_ok (target : NoCommentsTarget) (cacheDir outPath : System.FilePath)
    (w w' : Void IO.RealWorld) (h : downloadNoComments target cacheDir w = .ok outPath w') :
    outPath = cacheDir / target.asset ∧
      ∃ (pid : UInt32) (realTmp : System.FilePath) (meta_ : IO.FS.Metadata)
        (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
        let tmpPath := cacheDir / s!"{target.asset}.download.{pid}"
        tmpPath.symlinkMetadata w₁ = .ok meta_ w₂ ∧
        meta_.type = .file ∧
        IO.FS.realPath tmpPath w₂ = .ok realTmp w₃ ∧
        realTmp.isAbsolute = tmpPath.isAbsolute ∧
        pathParts realTmp = pathParts tmpPath ∧
        Sha256Verified target realTmp w₃ w₄ ∧
        IO.setAccessRights realTmp executableRight w₄ = .ok () w₅ ∧
        IO.FS.rename realTmp (cacheDir / target.asset) w₅ = .ok () w₆ := by
  unfold downloadNoComments at h
  dsimp only at h
  cases hp : (IO.Process.getPID : IO UInt32) w with
  | error e w₁ =>
    rw [io_bind_error hp] at h
    cases h
  | ok pid w₁ =>
    rw [io_bind_ok hp] at h
    cases hs : symlinkType? (cacheDir / s!"{target.asset}.download.{pid}") w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok ot w₂ =>
      rw [io_bind_ok hs] at h
      have hbody : ∀ w₃,
          ((do
              try
                stageNoComments target (cacheDir / target.asset) (cacheDir / s!"{target.asset}.download.{pid}")
              finally
                try
                  match ← symlinkType? (cacheDir / s!"{target.asset}.download.{pid}") with
                  | some .file => IO.FS.removeFile (cacheDir / s!"{target.asset}.download.{pid}")
                  | _ => pure ()
                catch _ =>
                  pure ()
              pure (cacheDir / target.asset)) : IO System.FilePath) w₃ = .ok outPath w' →
          outPath = cacheDir / target.asset ∧
            ∃ (pid : UInt32) (realTmp : System.FilePath) (meta_ : IO.FS.Metadata)
              (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld),
              let tmpPath := cacheDir / s!"{target.asset}.download.{pid}"
              tmpPath.symlinkMetadata w₁ = .ok meta_ w₂ ∧
              meta_.type = .file ∧
              IO.FS.realPath tmpPath w₂ = .ok realTmp w₃ ∧
              realTmp.isAbsolute = tmpPath.isAbsolute ∧
              pathParts realTmp = pathParts tmpPath ∧
              Sha256Verified target realTmp w₃ w₄ ∧
              IO.setAccessRights realTmp executableRight w₄ = .ok () w₅ ∧
              IO.FS.rename realTmp (cacheDir / target.asset) w₅ = .ok () w₆ := by
        intro w₃ h₃
        cases htf : (tryFinally
            (stageNoComments target (cacheDir / target.asset) (cacheDir / s!"{target.asset}.download.{pid}"))
            (try
              match ← symlinkType? (cacheDir / s!"{target.asset}.download.{pid}") with
              | some .file => IO.FS.removeFile (cacheDir / s!"{target.asset}.download.{pid}")
              | _ => pure ()
            catch _ =>
              pure ())) w₃ with
        | error e w₄ =>
          rw [io_bind_error htf] at h₃
          cases h₃
        | ok u w₄ =>
          cases u
          rw [io_bind_ok htf] at h₃
          obtain ⟨hout, -⟩ := EST.Out.ok.inj h₃
          obtain ⟨w₅, hst, -⟩ := finally_ok htf
          obtain ⟨realTmp, meta_, a, b, c, d, e, hm, htype, hreal, habs, hparts, hsha, hch, hren⟩ :=
            stageNoComments_ok target (cacheDir / target.asset) _ w₃ w₅ hst
          exact ⟨hout.symm, pid, realTmp, meta_, a, b, c, d, e, w₅, hm, htype, hreal, habs, hparts, hsha, hch, hren⟩
      cases ot with
      | none =>
        dsimp only at h
        exact hbody w₂ h
      | some t =>
        cases t with
        | file =>
          dsimp only at h
          cases hrm : IO.FS.removeFile (cacheDir / s!"{target.asset}.download.{pid}") w₂ with
          | error e w₃ =>
            rw [io_bind_error hrm] at h
            cases h
          | ok u w₃ =>
            cases u
            rw [io_bind_ok hrm] at h
            exact hbody w₃ h
        | dir | symlink | other =>
          dsimp only at h
          have hthrow : (throw (IO.userError s!"local gate: download staging path is not a regular file: {cacheDir / s!"{target.asset}.download.{pid}"}") : IO Unit) w₂ =
              .error (IO.userError s!"local gate: download staging path is not a regular file: {cacheDir / s!"{target.asset}.download.{pid}"}") w₂ := rfl
          rw [io_bind_error hthrow] at h
          cases h

theorem resolveCachedNoCommentsBin_ok (target : NoCommentsTarget) (binPath : System.FilePath)
    (w w' : Void IO.RealWorld) (h : resolveCachedNoCommentsBin target w = .ok binPath w') :
    ∃ cacheDir w₁,
      CacheDirEstablished cacheDir w w₁ ∧
      ((∃ m w₂, (cacheDir / target.asset).symlinkMetadata w₁ = .ok m w₂ ∧ m.type = .file ∧
          IO.FS.realPath (cacheDir / target.asset) w₂ = .ok binPath w' ∧
          binPath.isAbsolute = (cacheDir / target.asset).isAbsolute ∧
          pathParts binPath = pathParts (cacheDir / target.asset)) ∨
       (∃ path code details w₂,
          (cacheDir / target.asset).symlinkMetadata w₁ = .error (.noFileOrDirectory path code details) w₂ ∧
          downloadNoComments target cacheDir w₂ = .ok binPath w')) := by
  unfold resolveCachedNoCommentsBin at h
  cases hd : ensureNoCommentsCacheDir w with
  | error e w₁ =>
    rw [io_bind_error hd] at h
    cases h
  | ok cacheDir w₁ =>
    rw [io_bind_ok hd] at h
    have hcd := ensureNoCommentsCacheDir_ok cacheDir w w₁ hd
    cases hs : symlinkType? (cacheDir / target.asset) w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok ot w₂ =>
      rw [io_bind_ok hs] at h
      cases ot with
      | some t =>
        cases t with
        | file =>
          obtain ⟨m, hm, hmt⟩ := symlinkType?_some _ _ _ _ hs
          obtain ⟨hr, habs, hparts⟩ := requireExactRealPath_ok _ _ _ _ _ h
          exact ⟨cacheDir, w₁, hcd, .inl ⟨m, w₂, hm, hmt, hr, habs, hparts⟩⟩
        | dir | symlink | other => cases h
      | none =>
        obtain ⟨path, code, details, hno⟩ := symlinkType?_none _ _ _ hs
        exact ⟨cacheDir, w₁, hcd, .inr ⟨path, code, details, w₂, hno, h⟩⟩

theorem resolveNoCommentsBin_ok (target : NoCommentsTarget) (binPath : System.FilePath)
    (w w' : Void IO.RealWorld) (h : resolveNoCommentsBin target w = .ok binPath w') :
    (∃ raw w₁, (IO.getEnv "NO_COMMENTS_BIN" : IO (Option String)) w = .ok (some raw) w₁ ∧
        raw ≠ "" ∧ binPath = System.FilePath.mk raw ∧
        ((System.FilePath.mk raw).pathExists : IO Bool) w₁ = .ok true w') ∨
    (∃ w₁,
        ((IO.getEnv "NO_COMMENTS_BIN" : IO (Option String)) w = .ok none w₁ ∨
         (IO.getEnv "NO_COMMENTS_BIN" : IO (Option String)) w = .ok (some "") w₁) ∧
        resolveCachedNoCommentsBin target w₁ = .ok binPath w') := by
  unfold resolveNoCommentsBin at h
  cases he : (IO.getEnv "NO_COMMENTS_BIN" : IO (Option String)) w with
  | error e w₁ =>
    rw [io_bind_error he] at h
    cases h
  | ok opt w₁ =>
    rw [io_bind_ok he] at h
    cases opt with
    | none => exact .inr ⟨w₁, .inl rfl, h⟩
    | some raw =>
      by_cases hne : raw = ""
      · subst hne
        have hf : (("" != "") : Bool) = false := rfl
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
        exact .inr ⟨w₁, .inr rfl, h⟩
      · have ht : (raw != "") = true := by simp [hne]
        simp only [ht, ↓reduceIte] at h
        cases hx : ((System.FilePath.mk raw).pathExists : IO Bool) w₁ with
        | error e w₂ =>
          rw [io_bind_error hx] at h
          cases h
        | ok ex w₂ =>
          rw [io_bind_ok hx] at h
          cases ex with
          | false => cases h
          | true =>
            obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj h
            exact .inl ⟨raw, w₁, rfl, hne, rfl, hx⟩

def noCommentsRequestSpec (bin : System.FilePath) : IO.Process.SpawnArgs where
  cmd := bin.toString
  args := #["check", "--bootstrap"]
  cwd := some (System.FilePath.mk ".")
  stdin := .null
  env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false"), ("REGULA_FULL", none)]

theorem noCommentsRequest_eq (bin : System.FilePath) :
    noCommentsRequest bin = noCommentsRequestSpec bin := by
  rfl

def NoCommentsRan (bin : System.FilePath) (code : UInt32) (w w' : Void IO.RealWorld) : Prop :=
  ∃ w₁, ∃ child : IO.Process.Child (noCommentsRequestSpec bin).toStdioConfig,
    IO.Process.spawn (noCommentsRequestSpec bin) w = .ok child w₁ ∧
      child.wait w₁ = .ok code w'

theorem runNoCommentsStep_ran (bin : System.FilePath) (code : UInt32) (w w' : Void IO.RealWorld)
    (h : runNoCommentsStep bin w = .ok code w') :
    NoCommentsRan bin code w w' := by
  unfold runNoCommentsStep at h
  change ((IO.Process.spawn (noCommentsRequestSpec bin)) >>= IO.Process.Child.wait) w = .ok code w' at h
  cases hs : IO.Process.spawn (noCommentsRequestSpec bin) w with
  | error e w₁ =>
    rw [io_bind_error hs] at h
    cases h
  | ok child w₁ =>
    rw [io_bind_ok hs] at h
    exact ⟨w₁, child, hs, h⟩

def NoCommentsGateRan (code : UInt32) (w w' : Void IO.RealWorld) : Prop :=
  ∃ (target : NoCommentsTarget) (binPath realBin : System.FilePath) (meta_ : IO.FS.Metadata)
    (w₁ w₂ w₃ w₄ w₅ : Void IO.RealWorld),
    hostNoCommentsTarget? = some target ∧
    resolveNoCommentsBin target w = .ok binPath w₁ ∧
    IO.FS.realPath binPath w₁ = .ok realBin w₂ ∧
    realBin.metadata w₂ = .ok meta_ w₃ ∧
    meta_.type = .file ∧
    announceNoComments w₃ = .ok () w₄ ∧
    Sha256Verified target realBin w₄ w₅ ∧
    NoCommentsRan realBin code w₅ w'

inductive NoCommentsOutcome (w : Void IO.RealWorld) :
    EST.Out IO.Error IO.RealWorld UInt32 → Prop where
  | unsupportedPlatform (e : IO.Error) :
      hostNoCommentsTarget? = none →
      NoCommentsOutcome w (.error e w)
  | resolveError (target : NoCommentsTarget) (e : IO.Error) (w₁ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .error e w₁ →
      NoCommentsOutcome w (.error e w₁)
  | realPathError (target : NoCommentsTarget) (binPath : System.FilePath) (e : IO.Error)
      (w₁ w₂ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .error e w₂ →
      NoCommentsOutcome w (.error e w₂)
  | metadataError (target : NoCommentsTarget) (binPath realBin : System.FilePath) (e : IO.Error)
      (w₁ w₂ w₃ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .error e w₃ →
      NoCommentsOutcome w (.error e w₃)
  | notRegularFile (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata) (e : IO.Error) (w₁ w₂ w₃ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type ≠ .file →
      NoCommentsOutcome w (.error e w₃)
  | announceError (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata) (e : IO.Error) (w₁ w₂ w₃ w₄ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type = .file →
      announceNoComments w₃ = .error e w₄ →
      NoCommentsOutcome w (.error e w₄)
  | sha256OutputError (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata) (e : IO.Error) (w₁ w₂ w₃ w₄ w₅ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type = .file →
      announceNoComments w₃ = .ok () w₄ →
      (IO.Process.output (sha256RequestSpec target realBin) : IO IO.Process.Output) w₄ = .error e w₅ →
      NoCommentsOutcome w (.error e w₅)
  | sha256Mismatch (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata) (out : IO.Process.Output) (e : IO.Error)
      (w₁ w₂ w₃ w₄ w₅ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type = .file →
      announceNoComments w₃ = .ok () w₄ →
      (IO.Process.output (sha256RequestSpec target realBin) : IO IO.Process.Output) w₄ = .ok out w₅ →
      ¬ (out.exitCode = 0 ∧ Sha256OutputMatches (expectedSha256Spec target) out.stdout) →
      NoCommentsOutcome w (.error e w₅)
  | spawnError (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata) (e : IO.Error) (w₁ w₂ w₃ w₄ w₅ w₆ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type = .file →
      announceNoComments w₃ = .ok () w₄ →
      Sha256Verified target realBin w₄ w₅ →
      IO.Process.spawn (noCommentsRequestSpec realBin) w₅ = .error e w₆ →
      NoCommentsOutcome w (.error e w₆)
  | waitError (target : NoCommentsTarget) (binPath realBin : System.FilePath)
      (meta_ : IO.FS.Metadata)
      (child : IO.Process.Child (noCommentsRequestSpec realBin).toStdioConfig)
      (e : IO.Error) (w₁ w₂ w₃ w₄ w₅ w₆ w₇ : Void IO.RealWorld) :
      hostNoCommentsTarget? = some target →
      resolveNoCommentsBin target w = .ok binPath w₁ →
      IO.FS.realPath binPath w₁ = .ok realBin w₂ →
      realBin.metadata w₂ = .ok meta_ w₃ →
      meta_.type = .file →
      announceNoComments w₃ = .ok () w₄ →
      Sha256Verified target realBin w₄ w₅ →
      IO.Process.spawn (noCommentsRequestSpec realBin) w₅ = .ok child w₆ →
      child.wait w₆ = .error e w₇ →
      NoCommentsOutcome w (.error e w₇)
  | ran (code : UInt32) (w' : Void IO.RealWorld) :
      NoCommentsGateRan code w w' →
      NoCommentsOutcome w (.ok code w')

theorem runNoComments_outcome (w : Void IO.RealWorld) :
    NoCommentsOutcome w (runNoComments w) := by
  unfold runNoComments
  cases ht : hostNoCommentsTarget? with
  | none =>
    dsimp only
    exact .unsupportedPlatform _ ht
  | some target =>
    dsimp only
    cases hres : resolveNoCommentsBin target w with
    | error e w₁ =>
      rw [io_bind_error hres]
      exact .resolveError target e w₁ ht hres
    | ok binPath w₁ =>
      rw [io_bind_ok hres]
      cases hreal : IO.FS.realPath binPath w₁ with
      | error e w₂ =>
        rw [io_bind_error hreal]
        exact .realPathError target binPath e w₁ w₂ ht hres hreal
      | ok realBin w₂ =>
        rw [io_bind_ok hreal]
        cases hmeta : realBin.metadata w₂ with
        | error e w₃ =>
          rw [io_bind_error hmeta]
          exact .metadataError target binPath realBin e w₁ w₂ w₃ ht hres hreal hmeta
        | ok meta_ w₃ =>
          rw [io_bind_ok hmeta]
          cases htype : meta_.type with
          | dir =>
            have hne : (IO.FS.FileType.dir == IO.FS.FileType.file) = false := rfl
            simp only [hne, Bool.false_eq_true, ↓reduceIte]
            exact .notRegularFile target binPath realBin meta_ _ w₁ w₂ w₃ ht hres hreal hmeta
              (by simp [htype])
          | symlink =>
            have hne : (IO.FS.FileType.symlink == IO.FS.FileType.file) = false := rfl
            simp only [hne, Bool.false_eq_true, ↓reduceIte]
            exact .notRegularFile target binPath realBin meta_ _ w₁ w₂ w₃ ht hres hreal hmeta
              (by simp [htype])
          | other =>
            have hne : (IO.FS.FileType.other == IO.FS.FileType.file) = false := rfl
            simp only [hne, Bool.false_eq_true, ↓reduceIte]
            exact .notRegularFile target binPath realBin meta_ _ w₁ w₂ w₃ ht hres hreal hmeta
              (by simp [htype])
          | file =>
            have hfile : (IO.FS.FileType.file == IO.FS.FileType.file) = true := rfl
            simp only [hfile, ↓reduceIte]
            cases hann : announceNoComments w₃ with
            | error e w₄ =>
              rw [io_bind_error hann]
              exact .announceError target binPath realBin meta_ e w₁ w₂ w₃ w₄ ht hres hreal hmeta
                htype hann
            | ok u w₄ =>
              cases u
              rw [io_bind_ok hann]
              have hv := verifySha256_outcome target realBin w₄
              cases hveq : verifySha256 target realBin w₄ with
              | error e w₅ =>
                rw [io_bind_error hveq]
                rw [hveq] at hv
                cases hv with
                | outputError _ _ ho =>
                  exact .sha256OutputError target binPath realBin meta_ e w₁ w₂ w₃ w₄ w₅
                    ht hres hreal hmeta htype hann ho
                | mismatch out _ _ ho hnot =>
                  exact .sha256Mismatch target binPath realBin meta_ out e w₁ w₂ w₃ w₄ w₅
                    ht hres hreal hmeta htype hann ho hnot
              | ok u w₅ =>
                cases u
                rw [io_bind_ok hveq]
                rw [hveq] at hv
                cases hv with
                | verified _ hsha =>
                  unfold runNoCommentsStep
                  change ((IO.Process.spawn (noCommentsRequestSpec realBin)) >>= IO.Process.Child.wait) w₅ |>
                    NoCommentsOutcome w
                  cases hsp : IO.Process.spawn (noCommentsRequestSpec realBin) w₅ with
                  | error e w₆ =>
                    rw [io_bind_error hsp]
                    exact .spawnError target binPath realBin meta_ e w₁ w₂ w₃ w₄ w₅ w₆
                      ht hres hreal hmeta htype hann hsha hsp
                  | ok child w₆ =>
                    rw [io_bind_ok hsp]
                    cases hwt : child.wait w₆ with
                    | error e w₇ =>
                      exact .waitError target binPath realBin meta_ child e w₁ w₂ w₃ w₄ w₅ w₆ w₇
                        ht hres hreal hmeta htype hann hsha hsp hwt
                    | ok code w₇ =>
                      exact .ran code w₇
                        ⟨target, binPath, realBin, meta_, w₁, w₂, w₃, w₄, w₅,
                          ht, hres, hreal, hmeta, htype, hann, hsha, ⟨w₆, child, hsp, hwt⟩⟩

theorem runNoComments_ok (code : UInt32) (w w' : Void IO.RealWorld)
    (h : runNoComments w = .ok code w') :
    NoCommentsGateRan code w w' := by
  have ho := runNoComments_outcome w
  rw [h] at ho
  cases ho with
  | ran _ _ hgate => exact hgate

theorem runNoComments_zero (w w' : Void IO.RealWorld) (h : runNoComments w = .ok 0 w') :
    NoCommentsGateRan 0 w w' :=
  runNoComments_ok 0 w w' h

inductive RunInOutcome (target root : String) (w : Void IO.RealWorld) :
    EST.Out IO.Error IO.RealWorld UInt32 → Prop where
  | lakeError (pre post : List Step) (step : Step) (e : IO.Error) (w₁ w₂ : Void IO.RealWorld) :
      localSteps target root = pre ++ step :: post →
      StepsAllZero pre w w₁ →
      runStep step w₁ = .error e w₂ →
      RunInOutcome target root w (.error e w₂)
  | lakeFailed (pre post : List Step) (step : Step) (code : UInt32)
      (w₁ w₂ w₃ : Void IO.RealWorld) :
      localSteps target root = pre ++ step :: post →
      StepsAllZero pre w w₁ →
      StepRan step code w₁ w₂ →
      code ≠ 0 →
      sayResult (localSteps target root) (some (step, code)) w₂ = .ok () w₃ →
      RunInOutcome target root w (.ok 1 w₃)
  | lakeFailedSayError (pre post : List Step) (step : Step) (code : UInt32) (e : IO.Error)
      (w₁ w₂ w₃ : Void IO.RealWorld) :
      localSteps target root = pre ++ step :: post →
      StepsAllZero pre w w₁ →
      StepRan step code w₁ w₂ →
      code ≠ 0 →
      sayResult (localSteps target root) (some (step, code)) w₂ = .error e w₃ →
      RunInOutcome target root w (.error e w₃)
  | noCommentsError (e : IO.Error) (w₁ w₂ : Void IO.RealWorld) :
      StepsAllZero (localSteps target root) w w₁ →
      NoCommentsOutcome w₁ (.error e w₂) →
      RunInOutcome target root w (.error e w₂)
  | noCommentsSayError (ncCode : UInt32) (e : IO.Error) (w₁ w₂ w₃ : Void IO.RealWorld) :
      StepsAllZero (localSteps target root) w w₁ →
      NoCommentsGateRan ncCode w₁ w₂ →
      sayNoCommentsResult (localSteps target root) ncCode w₂ = .error e w₃ →
      RunInOutcome target root w (.error e w₃)
  | completed (ncCode : UInt32) (w₁ w₂ w₃ : Void IO.RealWorld) :
      StepsAllZero (localSteps target root) w w₁ →
      NoCommentsGateRan ncCode w₁ w₂ →
      sayNoCommentsResult (localSteps target root) ncCode w₂ = .ok () w₃ →
      RunInOutcome target root w (.ok (if ncCode == 0 then 0 else 1) w₃)

theorem runIn_outcome (target root : String) (w : Void IO.RealWorld) :
    RunInOutcome target root w (runIn target root w) := by
  unfold runIn
  have hst := runSteps_outcome (localSteps target root) w
  cases hr : runSteps runStep (localSteps target root) w with
  | error e w₁ =>
    rw [io_bind_error hr]
    rw [hr] at hst
    cases hst with
    | errored pre post step _ w₀ _ heq hpre herr =>
      exact .lakeError pre post step e w₀ w₁ heq hpre herr
  | ok r w₁ =>
    rw [io_bind_ok hr]
    rw [hr] at hst
    cases r with
    | some p =>
      dsimp only
      cases hst with
      | failed pre post step code w₀ _ heq hpre hran hne =>
        cases hs : sayResult (localSteps target root) (some (step, code)) w₁ with
        | error e w₂ =>
          rw [io_bind_error hs]
          exact .lakeFailedSayError pre post step code e w₀ w₁ w₂ heq hpre hran hne hs
        | ok u w₂ =>
          cases u
          rw [io_bind_ok hs]
          exact .lakeFailed pre post step code w₀ w₁ w₂ heq hpre hran hne hs
    | none =>
      dsimp only
      cases hst with
      | allZero _ hall =>
        have hnco := runNoComments_outcome w₁
        cases hnc : runNoComments w₁ with
        | error e w₂ =>
          rw [io_bind_error hnc]
          rw [hnc] at hnco
          exact .noCommentsError e w₁ w₂ hall hnco
        | ok ncCode w₂ =>
          rw [io_bind_ok hnc]
          have hgate := runNoComments_ok ncCode w₁ w₂ hnc
          cases hs : sayNoCommentsResult (localSteps target root) ncCode w₂ with
          | error e w₃ =>
            rw [io_bind_error hs]
            exact .noCommentsSayError ncCode e w₁ w₂ w₃ hall hgate hs
          | ok u w₃ =>
            cases u
            rw [io_bind_ok hs]
            exact .completed ncCode w₁ w₂ w₃ hall hgate hs

theorem runIn_zero (target root : String) (w w' : Void IO.RealWorld)
    (h : runIn target root w = .ok 0 w') :
    ∃ w₁ w₂, StepsAllZero (localSteps target root) w w₁ ∧
      NoCommentsGateRan 0 w₁ w₂ ∧
      sayNoCommentsResult (localSteps target root) 0 w₂ = .ok () w' := by
  have haux : ∀ res, RunInOutcome target root w res → res = .ok 0 w' →
      ∃ w₁ w₂, StepsAllZero (localSteps target root) w w₁ ∧
        NoCommentsGateRan 0 w₁ w₂ ∧
        sayNoCommentsResult (localSteps target root) 0 w₂ = .ok () w' := by
    intro res ho heq
    cases ho with
    | lakeError => cases heq
    | lakeFailedSayError => cases heq
    | noCommentsError => cases heq
    | noCommentsSayError => cases heq
    | lakeFailed =>
      have hc := (EST.Out.ok.inj heq).1
      cases hc
    | completed ncCode w₁ w₂ _ hall hgate hsay =>
      obtain ⟨hc, rfl⟩ := EST.Out.ok.inj heq
      by_cases hzero : ncCode = 0
      · subst hzero
        exact ⟨w₁, w₂, hall, hgate, hsay⟩
      · simp [hzero] at hc
  exact haux _ (runIn_outcome target root w) h

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

theorem join_relative (target file : System.FilePath) (h : file.isAbsolute = false) :
    target / file = System.FilePath.mk (target.toString ++ System.FilePath.pathSeparator.toString ++ file.toString) := by
  show System.FilePath.join target file = _
  simp [System.FilePath.join, h]

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

inductive RunLocalOutcome (w : Void IO.RealWorld) :
    EST.Out IO.Error IO.RealWorld UInt32 → Prop where
  | tempDirError (e : IO.Error) (w₁ : Void IO.RealWorld) :
      IO.FS.createTempDir w = .error e w₁ →
      RunLocalOutcome w (.error e w₁)
  | copyError (target : System.FilePath) (e : IO.Error) (w₁ w₂ w' : Void IO.RealWorld)
      (res : EST.Out IO.Error IO.RealWorld UInt32) :
      IO.FS.createTempDir w = .ok target w₁ →
      copyChecker target w₁ = .error e w₂ →
      ((∃ u, IO.FS.removeDirAll target w₂ = .ok u w' ∧ res = .error e w') ∨
       (∃ e', IO.FS.removeDirAll target w₂ = .error e' w' ∧ res = .error e' w')) →
      RunLocalOutcome w res
  | currentDirError (target : System.FilePath) (e : IO.Error) (w₁ w₂ w₃ w' : Void IO.RealWorld)
      (res : EST.Out IO.Error IO.RealWorld UInt32) :
      IO.FS.createTempDir w = .ok target w₁ →
      copyChecker target w₁ = .ok () w₂ →
      IO.currentDir w₂ = .error e w₃ →
      ((∃ u, IO.FS.removeDirAll target w₃ = .ok u w' ∧ res = .error e w') ∨
       (∃ e', IO.FS.removeDirAll target w₃ = .error e' w' ∧ res = .error e' w')) →
      RunLocalOutcome w res
  | ran (target root : System.FilePath) (w₁ w₂ w₃ w₄ w' : Void IO.RealWorld)
      (bodyRes res : EST.Out IO.Error IO.RealWorld UInt32) :
      IO.FS.createTempDir w = .ok target w₁ →
      copyChecker target w₁ = .ok () w₂ →
      IO.currentDir w₂ = .ok root w₃ →
      RunInOutcome target.toString root.toString w₃ bodyRes →
      ((∃ code, bodyRes = .ok code w₄ ∧ IO.FS.removeDirAll target w₄ = .ok () w' ∧ res = .ok code w') ∨
       (∃ code e', bodyRes = .ok code w₄ ∧ IO.FS.removeDirAll target w₄ = .error e' w' ∧ res = .error e' w') ∨
       (∃ e, bodyRes = .error e w₄ ∧ IO.FS.removeDirAll target w₄ = .ok () w' ∧ res = .error e w') ∨
       (∃ e e', bodyRes = .error e w₄ ∧ IO.FS.removeDirAll target w₄ = .error e' w' ∧ res = .error e' w')) →
      RunLocalOutcome w res

theorem runLocal_outcome (w : Void IO.RealWorld) :
    RunLocalOutcome w (runLocal w) := by
  unfold runLocal
  cases ht : IO.FS.createTempDir w with
  | error e w₁ =>
    rw [io_bind_error ht]
    exact .tempDirError e w₁ ht
  | ok target w₁ =>
    rw [io_bind_ok ht]
    have hfin := finally_spec
      (do copyChecker target; runIn target.toString (← IO.currentDir).toString)
      (IO.FS.removeDirAll target) w₁
    change RunLocalOutcome w
      ((tryFinally
        (do copyChecker target; runIn target.toString (← IO.currentDir).toString)
        (IO.FS.removeDirAll target)) w₁)
    generalize hfinRes : (tryFinally
        (do copyChecker target; runIn target.toString (← IO.currentDir).toString)
        (IO.FS.removeDirAll target)) w₁ = res at hfin ⊢
    cases hfin with
    | okOk code u w₂ w' hbody hrem =>
      cases u
      cases hc : copyChecker target w₁ with
      | error e w₃ =>
        rw [io_bind_error hc] at hbody
        cases hbody
      | ok u w₃ =>
        cases u
        rw [io_bind_ok hc] at hbody
        cases hd : IO.currentDir w₃ with
        | error e w₄ =>
          rw [io_bind_error hd] at hbody
          cases hbody
        | ok root w₄ =>
          rw [io_bind_ok hd] at hbody
          have hrio := runIn_outcome target.toString root.toString w₄
          rw [hbody] at hrio
          exact .ran target root w₁ w₃ w₄ w₂ w' (.ok code w₂) (.ok code w')
            ht hc hd hrio (.inl ⟨code, rfl, hrem, rfl⟩)
    | okError code e' w₂ w' hbody hrem =>
      cases hc : copyChecker target w₁ with
      | error e w₃ =>
        rw [io_bind_error hc] at hbody
        cases hbody
      | ok u w₃ =>
        cases u
        rw [io_bind_ok hc] at hbody
        cases hd : IO.currentDir w₃ with
        | error e w₄ =>
          rw [io_bind_error hd] at hbody
          cases hbody
        | ok root w₄ =>
          rw [io_bind_ok hd] at hbody
          have hrio := runIn_outcome target.toString root.toString w₄
          rw [hbody] at hrio
          exact .ran target root w₁ w₃ w₄ w₂ w' (.ok code w₂) (.error e' w')
            ht hc hd hrio (.inr (.inl ⟨code, e', rfl, hrem, rfl⟩))
    | errorOk e u w₂ w' hbody hrem =>
      cases u
      cases hc : copyChecker target w₁ with
      | error e0 w₃ =>
        rw [io_bind_error hc] at hbody
        obtain ⟨he, hw⟩ := EST.Out.error.inj hbody
        subst he; subst hw
        exact .copyError target e0 w₁ w₃ w' (.error e0 w') ht hc (.inl ⟨(), hrem, rfl⟩)
      | ok u w₃ =>
        cases u
        rw [io_bind_ok hc] at hbody
        cases hd : IO.currentDir w₃ with
        | error e0 w₄ =>
          rw [io_bind_error hd] at hbody
          obtain ⟨he, hw⟩ := EST.Out.error.inj hbody
          subst he; subst hw
          exact .currentDirError target e0 w₁ w₃ w₄ w' (.error e0 w') ht hc hd (.inl ⟨(), hrem, rfl⟩)
        | ok root w₄ =>
          rw [io_bind_ok hd] at hbody
          have hrio := runIn_outcome target.toString root.toString w₄
          rw [hbody] at hrio
          exact .ran target root w₁ w₃ w₄ w₂ w' (.error e w₂) (.error e w')
            ht hc hd hrio (.inr (.inr (.inl ⟨e, rfl, hrem, rfl⟩)))
    | errorError e e' w₂ w' hbody hrem =>
      cases hc : copyChecker target w₁ with
      | error e0 w₃ =>
        rw [io_bind_error hc] at hbody
        obtain ⟨he, hw⟩ := EST.Out.error.inj hbody
        subst he; subst hw
        exact .copyError target e0 w₁ w₃ w' (.error e' w') ht hc (.inr ⟨e', hrem, rfl⟩)
      | ok u w₃ =>
        cases u
        rw [io_bind_ok hc] at hbody
        cases hd : IO.currentDir w₃ with
        | error e0 w₄ =>
          rw [io_bind_error hd] at hbody
          obtain ⟨he, hw⟩ := EST.Out.error.inj hbody
          subst he; subst hw
          exact .currentDirError target e0 w₁ w₃ w₄ w' (.error e' w') ht hc hd (.inr ⟨e', hrem, rfl⟩)
        | ok root w₄ =>
          rw [io_bind_ok hd] at hbody
          have hrio := runIn_outcome target.toString root.toString w₄
          rw [hbody] at hrio
          exact .ran target root w₁ w₃ w₄ w₂ w' (.error e w₂) (.error e' w')
            ht hc hd hrio (.inr (.inr (.inr ⟨e, e', rfl, hrem, rfl⟩)))

theorem runLocal_zero (w w' : Void IO.RealWorld) (h : runLocal w = .ok 0 w') :
    ∃ target root w₁ w₂ w₃ w₄ w₅ w₆,
      IO.FS.createTempDir w = .ok target w₁ ∧
      copyChecker target w₁ = .ok () w₂ ∧
      IO.currentDir w₂ = .ok root w₃ ∧
      StepsAllZero (localSteps target.toString root.toString) w₃ w₄ ∧
      NoCommentsGateRan 0 w₄ w₅ ∧
      sayNoCommentsResult (localSteps target.toString root.toString) 0 w₅ = .ok () w₆ ∧
      IO.FS.removeDirAll target w₆ = .ok () w' := by
  have haux : ∀ res, RunLocalOutcome w res → res = .ok 0 w' →
      ∃ target root w₁ w₂ w₃ w₄ w₅ w₆,
        IO.FS.createTempDir w = .ok target w₁ ∧
        copyChecker target w₁ = .ok () w₂ ∧
        IO.currentDir w₂ = .ok root w₃ ∧
        StepsAllZero (localSteps target.toString root.toString) w₃ w₄ ∧
        NoCommentsGateRan 0 w₄ w₅ ∧
        sayNoCommentsResult (localSteps target.toString root.toString) 0 w₅ = .ok () w₆ ∧
        IO.FS.removeDirAll target w₆ = .ok () w' := by
    intro res ho heq
    cases ho with
    | tempDirError => cases heq
    | copyError _ _ _ _ _ _ _ _ hfin =>
      rcases hfin with ⟨_, _, hres⟩ | ⟨_, _, hres⟩ <;> (rw [hres] at heq; cases heq)
    | currentDirError _ _ _ _ _ _ _ _ _ _ hfin =>
      rcases hfin with ⟨_, _, hres⟩ | ⟨_, _, hres⟩ <;> (rw [hres] at heq; cases heq)
    | ran target root w₁ w₂ w₃ w₄ _ bodyRes _ ht hc hd hrio hfin =>
      rcases hfin with ⟨code, hbr, hrem, hres⟩ | ⟨_, _, _, _, hres⟩ | ⟨_, _, _, hres⟩ | ⟨_, _, _, _, hres⟩
      · rw [hres] at heq
        obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj heq
        have hauxIn : ∀ bres, RunInOutcome target.toString root.toString w₃ bres → bres = .ok 0 w₄ →
            ∃ w₅ w₆, StepsAllZero (localSteps target.toString root.toString) w₃ w₅ ∧
              NoCommentsGateRan 0 w₅ w₆ ∧
              sayNoCommentsResult (localSteps target.toString root.toString) 0 w₆ = .ok () w₄ := by
          intro bres hr hb
          cases hr with
          | lakeError => cases hb
          | lakeFailedSayError => cases hb
          | noCommentsError => cases hb
          | noCommentsSayError => cases hb
          | lakeFailed =>
            have hc := (EST.Out.ok.inj hb).1
            cases hc
          | completed ncCode w₅ w₆ _ hall hgate hsay =>
            obtain ⟨hc, rfl⟩ := EST.Out.ok.inj hb
            by_cases hzero : ncCode = 0
            · subst hzero
              exact ⟨w₅, w₆, hall, hgate, hsay⟩
            · simp [hzero] at hc
        obtain ⟨w₅, w₆, hall, hgate, hsay⟩ := hauxIn bodyRes hrio hbr
        exact ⟨target, root, w₁, w₂, w₃, w₅, w₆, w₄, ht, hc, hd, hall, hgate, hsay, hrem⟩
      · rw [hres] at heq; cases heq
      · rw [hres] at heq; cases heq
      · rw [hres] at heq; cases heq
  exact haux _ (runLocal_outcome w) h

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

theorem fullVariable_eq : fullVariable = Regula.Shell.fullVariable := by rfl

theorem noCommentsVersion_eq : noCommentsVersion = "v0.2.0" := by rfl

theorem noCommentsArgs_eq : noCommentsArgs = ["check", "--bootstrap"] := by rfl

theorem noCommentsTargets_eq :
    NoCommentsTarget.darwinArm64.asset = "no-comments-darwin-arm64" ∧
    NoCommentsTarget.darwinArm64.sha256 = "4c610e1b0f0f93f54e89f33acb13c5120ed4e7ecfc3bb5db85e562aba637fe2a" ∧
    NoCommentsTarget.linuxX86_64.asset = "no-comments-linux-x86_64" ∧
    NoCommentsTarget.linuxX86_64.sha256 = "f1a5d5cee2214515f9d36d3bb7245beee3856c06a85f6593ac0b23c4a0c6941e" ∧
    NoCommentsTarget.darwinArm64.url =
      "https://github.com/rbeauchamp/lean-no-comments/releases/download/v0.2.0/no-comments-darwin-arm64" ∧
    NoCommentsTarget.linuxX86_64.url =
      "https://github.com/rbeauchamp/lean-no-comments/releases/download/v0.2.0/no-comments-linux-x86_64" := by
  decide +kernel

theorem hostNoCommentsTarget_darwin_iff :
    hostNoCommentsTarget? = some .darwinArm64 ↔
      System.Platform.isOSX = true ∧ System.Platform.target.startsWith "arm64-" = true := by
  unfold hostNoCommentsTarget?
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp [h]
  · rename_i h
    simp only [Bool.and_eq_true, not_and] at h
    split
    · simp only [Option.some.injEq, reduceCtorEq, false_iff, not_and]
      exact h
    · simp only [reduceCtorEq, false_iff, not_and]
      exact h

theorem hostNoCommentsTarget_linux_iff :
    hostNoCommentsTarget? = some .linuxX86_64 ↔
      System.Platform.isOSX = false ∧ System.Platform.isLinux = true ∧
        System.Platform.target.startsWith "x86_64-" = true := by
  unfold hostNoCommentsTarget?
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp [h.1]
  · rename_i h1
    split
    · rename_i h2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
      simp [h2]
    · rename_i h2
      simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at h2
      simp only [reduceCtorEq, false_iff, not_and]
      intro ho hl
      exact h2 ⟨ho, hl⟩

theorem hostNoCommentsTarget_darwin (hOsx : System.Platform.isOSX = true)
    (hArch : System.Platform.target.startsWith "arm64-" = true) :
    hostNoCommentsTarget? = some .darwinArm64 :=
  hostNoCommentsTarget_darwin_iff.mpr ⟨hOsx, hArch⟩

theorem hostNoCommentsTarget_linux (hOsx : System.Platform.isOSX = false)
    (hLinux : System.Platform.isLinux = true)
    (hArch : System.Platform.target.startsWith "x86_64-" = true) :
    hostNoCommentsTarget? = some .linuxX86_64 :=
  hostNoCommentsTarget_linux_iff.mpr ⟨hOsx, hLinux, hArch⟩

theorem localSteps_eq (checker root : String) :
    localSteps checker root =
      [⟨["clean"], "specification", none⟩,
        ⟨["build", "lint"], checker, none⟩,
        ⟨["exe", "lint", "standard-logical"], checker, some root⟩,
        ⟨["build", "--wfail"], ".", none⟩,
        ⟨["build", "--wfail", "Regula", "lint"], ".", none⟩,
        ⟨["lint"], ".", none⟩,
        ⟨["build", "--wfail"], "specification", none⟩,
        ⟨["lint"], "specification", none⟩] := by rfl

theorem localSteps_full (checker root : String) :
    ∀ s ∈ localSteps checker root,
      s.full = if s.arguments = ["exe", "lint", "standard-logical"] then some root else none := by
  simp [localSteps]

theorem runStep_spawns (step : Step) :
    runStep step = (do
      announce step
      let child ← IO.Process.spawn (stepRequest step)
      child.wait) :=
  by rfl

theorem runNoCommentsStep_spawns (bin : System.FilePath) :
    runNoCommentsStep bin = (do
      let child ← IO.Process.spawn (noCommentsRequestSpec bin)
      child.wait) :=
  by rfl

end RegulaSpecification.GateProgram
