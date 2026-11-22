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

def IsLowerHex (c : Char) : Prop :=
  ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')

theorem isLowerHexChar_iff (c : Char) : isLowerHexChar c = true ↔ IsLowerHex c := by
  simp [isLowerHexChar, IsLowerHex]

theorem parseSha256Line_iff (cs : List Char) (hex : String) :
    parseSha256Line cs = some hex ↔
      (cs.take 64).length = 64 ∧ (∀ c ∈ cs.take 64, IsLowerHex c) ∧
        ((cs.drop 64).take 2 = [' ', ' '] ∨ (cs.drop 64).take 2 = [' ', '*']) ∧
        hex = String.ofList (cs.take 64) := by
  unfold parseSha256Line
  dsimp only
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, isLowerHexChar_iff] at hcond
    rcases hcond with ⟨⟨hlen, hall⟩, hsep⟩
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨hlen, hall, hsep, h.symm⟩, fun ⟨_, _, _, h⟩ => h.symm⟩
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, isLowerHexChar_iff, not_and] at hcond
    constructor
    · intro h
      cases h
    · rintro ⟨hlen, hall, hsep, _⟩
      exact absurd hsep (hcond ⟨hlen, hall⟩)

theorem sha256Matches_iff (expected : String) (out : IO.Process.Output) :
    sha256Matches expected out = true ↔ out.exitCode = 0 ∧ parseSha256Output out.stdout = some expected := by
  simp [sha256Matches]

def Sha256Verified (path : System.FilePath) (expected : String) (w w' : Void IO.RealWorld) : Prop :=
  ∃ out : IO.Process.Output, (IO.Process.output (sha256Request path) : IO IO.Process.Output) w = .ok out w' ∧
    out.exitCode = 0 ∧ parseSha256Output out.stdout = some expected

theorem verifySha256_ok (path : System.FilePath) (expected : String) (w w' : Void IO.RealWorld)
    (h : verifySha256 path expected w = .ok () w') :
    Sha256Verified path expected w w' := by
  unfold verifySha256 at h
  cases ho : (IO.Process.output (sha256Request path) : IO IO.Process.Output) w with
  | error e w₁ =>
    rw [io_bind_error ho] at h
    cases h
  | ok out w₁ =>
    rw [io_bind_ok ho] at h
    cases hm : sha256Matches expected out with
    | false =>
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    | true =>
      simp only [hm, ↓reduceIte] at h
      obtain ⟨_, hw⟩ := EST.Out.ok.inj h
      subst hw
      obtain ⟨hcode, hparse⟩ := (sha256Matches_iff expected out).mp hm
      exact ⟨out, ho, hcode, hparse⟩

def noCommentsRequestSpec (bin : System.FilePath) : IO.Process.SpawnArgs where
  cmd := bin.toString
  args := noCommentsArgs.toArray
  cwd := some (System.FilePath.mk ".")
  stdin := .null
  env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false"), (Regula.Shell.fullVariable, none)]

theorem noCommentsRequest_eq (bin : System.FilePath) :
    noCommentsRequest bin = noCommentsRequestSpec bin := by
  rfl

def NoCommentsRan (bin : System.FilePath) (code : UInt32) (w w' : Void IO.RealWorld) : Prop :=
  ∃ w₁ w₂, ∃ child : IO.Process.Child (noCommentsRequest bin).toStdioConfig,
    announceNoComments w = .ok () w₁ ∧ IO.Process.spawn (noCommentsRequest bin) w₁ = .ok child w₂ ∧
      child.wait w₂ = .ok code w'

theorem runNoCommentsStep_ran (bin : System.FilePath) (code : UInt32) (w w' : Void IO.RealWorld)
    (h : runNoCommentsStep bin w = .ok code w') :
    NoCommentsRan bin code w w' := by
  unfold runNoCommentsStep at h
  cases ha : announceNoComments w with
  | error e w₁ =>
    rw [io_bind_error ha] at h
    cases h
  | ok u w₁ =>
    cases u
    rw [io_bind_ok ha] at h
    change ((IO.Process.spawn (noCommentsRequest bin)) >>= IO.Process.Child.wait) w₁ = .ok code w' at h
    cases hs : IO.Process.spawn (noCommentsRequest bin) w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok child w₂ =>
      rw [io_bind_ok hs] at h
      exact ⟨w₁, w₂, child, ha, hs, h⟩

def NoCommentsGateRan (w w' : Void IO.RealWorld) : Prop :=
  ∃ (target : NoCommentsTarget) (binPath realBin : System.FilePath) (meta_ : IO.FS.Metadata)
    (w₁ w₂ w₃ w₄ : Void IO.RealWorld),
    hostNoCommentsTarget? = some target ∧
    resolveNoCommentsBin target w = .ok binPath w₁ ∧
    IO.FS.realPath binPath w₁ = .ok realBin w₂ ∧
    realBin.metadata w₂ = .ok meta_ w₃ ∧
    meta_.type = .file ∧
    Sha256Verified realBin target.sha256 w₃ w₄ ∧
    NoCommentsRan realBin 0 w₄ w'

theorem runNoComments_zero (w w' : Void IO.RealWorld) (h : runNoComments w = .ok 0 w') :
    NoCommentsGateRan w w' := by
  unfold runNoComments at h
  cases ht : hostNoCommentsTarget? with
  | none =>
    simp only [ht] at h
    cases h
  | some target =>
    simp only [ht] at h
    cases hres : resolveNoCommentsBin target w with
    | error e w₁ =>
      rw [io_bind_error hres] at h
      cases h
    | ok binPath w₁ =>
      rw [io_bind_ok hres] at h
      cases hreal : IO.FS.realPath binPath w₁ with
      | error e w₂ =>
        rw [io_bind_error hreal] at h
        cases h
      | ok realBin w₂ =>
        rw [io_bind_ok hreal] at h
        cases hmeta : realBin.metadata w₂ with
        | error e w₃ =>
          rw [io_bind_error hmeta] at h
          cases h
        | ok meta_ w₃ =>
          rw [io_bind_ok hmeta] at h
          cases htype : meta_.type with
          | dir | symlink | other =>
            simp only [htype] at h
            cases h
          | file =>
            have hfile : (IO.FS.FileType.file == IO.FS.FileType.file) = true := rfl
            simp only [htype, hfile, ↓reduceIte] at h
            cases hv : verifySha256 realBin target.sha256 w₃ with
            | error e w₄ =>
              rw [io_bind_error hv] at h
              cases h
            | ok u w₄ =>
              cases u
              rw [io_bind_ok hv] at h
              exact ⟨target, binPath, realBin, meta_, w₁, w₂, w₃, w₄, ht, hres, hreal, hmeta, htype,
                verifySha256_ok realBin target.sha256 w₃ w₄ hv, runNoCommentsStep_ran realBin 0 w₄ w' h⟩

theorem runIn_zero (target root : String) (w w' : Void IO.RealWorld)
    (h : runIn target root w = .ok 0 w') :
    (∀ s ∈ localSteps target root, ∃ w₁ w₂, StepRan s 0 w₁ w₂) ∧ ∃ w₁ w₂, NoCommentsGateRan w₁ w₂ := by
  unfold runIn at h
  cases hr : runSteps runStep (localSteps target root) w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok r w₁ =>
    rw [io_bind_ok hr] at h
    cases r with
    | some p =>
      simp only at h
      cases hs : sayResult (localSteps target root) (some p) w₁ with
      | error e w₂ =>
        rw [io_bind_error hs] at h
        cases h
      | ok u w₂ =>
        rw [io_bind_ok hs] at h
        have hc : exitOf (some p) = 0 := (EST.Out.ok.inj h).1
        cases hc
    | none =>
      simp only at h
      cases hnc : runNoComments w₁ with
      | error e w₂ =>
        rw [io_bind_error hnc] at h
        cases h
      | ok ncCode w₂ =>
        rw [io_bind_ok hnc] at h
        cases hs : sayNoCommentsResult (localSteps target root) ncCode w₂ with
        | error e w₃ =>
          rw [io_bind_error hs] at h
          cases h
        | ok u w₃ =>
          rw [io_bind_ok hs] at h
          have hc : (if ncCode == 0 then (0 : UInt32) else 1) = 0 := (EST.Out.ok.inj h).1
          by_cases hzero : ncCode = 0
          · subst hzero
            refine ⟨fun s hmem => ?_, ⟨w₁, w₂, runNoComments_zero w₁ w₂ hnc⟩⟩
            obtain ⟨w₄, w₅, hrun⟩ := runSteps_io _ _ _ _ hr s hmem
            exact ⟨w₄, w₅, runStep_ran s 0 w₄ w₅ hrun⟩
          · simp [hzero] at hc

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

theorem runLocal_zero (w w' : Void IO.RealWorld) (h : runLocal w = .ok 0 w') :
    ∃ target root w₁ w₂ w₃ w₄, IO.FS.createTempDir w = .ok target w₁ ∧ copyChecker target w₁ = .ok () w₂ ∧
      IO.currentDir w₂ = .ok root w₃ ∧ runIn target.toString root.toString w₃ = .ok 0 w₄ ∧
      (∀ s ∈ localSteps target.toString root.toString, ∃ a b, StepRan s 0 a b) ∧
      ∃ a b, NoCommentsGateRan a b := by
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
        obtain ⟨hsteps, hnc⟩ := runIn_zero _ _ _ _ hbody
        exact ⟨target, root, w₁, w₃, w₄, w₂, rfl, hc, hd, hbody, hsteps, hnc⟩

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

theorem hostNoCommentsTarget_darwin (hOsx : System.Platform.isOSX = true)
    (hArch : System.Platform.target.startsWith "arm64-" = true) :
    hostNoCommentsTarget? = some .darwinArm64 := by
  simp [hostNoCommentsTarget?, hOsx, hArch]

theorem hostNoCommentsTarget_linux (hOsx : System.Platform.isOSX = false)
    (hLinux : System.Platform.isLinux = true)
    (hArch : System.Platform.target.startsWith "x86_64-" = true) :
    hostNoCommentsTarget? = some .linuxX86_64 := by
  simp [hostNoCommentsTarget?, hOsx, hLinux, hArch]

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
      announceNoComments
      let child ← IO.Process.spawn (noCommentsRequest bin)
      child.wait) :=
  by rfl

end RegulaSpecification.GateProgram
