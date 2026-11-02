module

public import Lake.CLI.Main
public import Regula.TestListing
import all Init.System.ST
import all Lake.CLI.Main
import all Regula.TestListing

/-! # The load configuration of the test listing

The validation pipeline runs the listing of the tests that Lake knows for the package,
`lean/Regula/TestListing.lean`, with `lean --run` before the package is built, so the listing imports
only Lake. It makes its load configuration itself (`Regula.TestListing.loadConfig`), because the module
of `Lake.LakeOptions.mkLoadConfig` links the code of every command of Lake, and this module proves the
two configurations equal. The proof reduces both sides, so each `import all` above makes visible a
body that its module does not expose: `loadConfig` of `Regula.TestListing`, `mkLoadConfig` and what it
calls of `Lake.CLI.Main`, and the bind of `EST` (`Init.System.ST`), the monad of `EIO`.

The theorems about `main` hold for every answer of Lake and of the streams, because `IO` is a state
monad in Lean's own definition. That the compiler keeps the order of the effects stays with the
compiler.
-/

public section

theorem Regula.ProgramCheck.TestListing.loadConfig_eq (elanInstall? : Option Lake.ElanInstall)
    (leanInstall? : Option Lake.LeanInstall) (lakeInstall? : Option Lake.LakeInstall) :
    Regula.TestListing.loadConfig elanInstall? leanInstall? lakeInstall? =
      Lake.LakeOptions.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? } := by
  cases leanInstall? <;> cases lakeInstall? <;> rfl

namespace Regula.ProgramCheck.TestListing

open Regula.TestListing

theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {a : α}
    (h : x w = .ok a w₁) : (x >>= f) w = f a w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

theorem io_bind_error {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {e : IO.Error}
    (h : x w = .error e w₁) : (x >>= f) w = .error e w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

theorem forM_ok (f : String → IO Unit) (l : List String) (w w' : Void IO.RealWorld)
    (h : l.forM f w = .ok () w') : ∀ x ∈ l, ∃ a b, f x a = .ok () b := by
  induction l generalizing w with
  | nil => simp
  | cons y ys ih =>
    intro x hx
    have hc : (y :: ys).forM f = f y >>= fun _ => ys.forM f := rfl
    rw [hc] at h
    cases hf : f y w with
    | error e w₁ =>
      rw [io_bind_error hf] at h
      cases h
    | ok u w₁ =>
      rw [io_bind_ok hf] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨w, w₁, hf⟩
      · exact ih w₁ h x hx

theorem readDriver_eq : readDriver = (do
    let installs ← Lake.findInstall?
    let loaded ← (((loadConfig installs.1 installs.2.1 installs.2.2).adapt toString >>= fun config =>
      liftM (m := EIO String) ((Lake.loadPackage config).toBaseIO : BaseIO _)) :
        EIO String (Option Lake.Package)).toBaseIO
    pure (loaded.map (Option.map (·.testDriver)))) := by
  rfl

theorem main_runs (w w' : Void IO.RealWorld) (c : UInt32) (h : main w = .ok c w') :
    ∃ r w₁ w₂, readDriver w = .ok r w₁ ∧ (outcome r).lines.forM IO.println w₁ = .ok () w₂ ∧
      (outcome r).errors.forM IO.eprintln w₂ = .ok () w' ∧ c = (outcome r).code := by
  unfold main at h
  cases hr : readDriver w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok r w₁ =>
    rw [io_bind_ok hr] at h
    cases hl : (outcome r).lines.forM IO.println w₁ with
    | error e w₂ =>
      rw [io_bind_error hl] at h
      cases h
    | ok u w₂ =>
      rw [io_bind_ok hl] at h
      cases he : (outcome r).errors.forM IO.eprintln w₂ with
      | error e w₃ =>
        rw [io_bind_error he] at h
        cases h
      | ok v w₃ =>
        rw [io_bind_ok he] at h
        obtain ⟨hc, hw⟩ := EST.Out.ok.inj h
        subst hw
        exact ⟨r, w₁, w₂, rfl, hl, he, hc.symm⟩

theorem main_zero (w w' : Void IO.RealWorld) (h : main w = .ok 0 w') :
    ∃ driver lines w₁, readDriver w = .ok (.ok (some driver)) w₁ ∧ listing driver = .ok lines ∧
      ∀ l ∈ lines, ∃ a b, IO.println l a = .ok () b := by
  obtain ⟨r, w₁, w₂, hr, hl, -, hc⟩ := main_runs w w' 0 h
  obtain ⟨driver, rfl, hd, -⟩ := outcome_of_zero hc.symm
  exact ⟨driver, _, w₁, hr, hd, forM_ok _ _ _ _ hl⟩

end Regula.ProgramCheck.TestListing
