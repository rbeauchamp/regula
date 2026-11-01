/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lake.CLI.Main
public import Regula.TestListing
import all Init.System.ST
import all Lake.CLI.Main
import all Regula.TestListing

/-! # The load configuration of the test listing

The validation pipeline runs the listing of the tests that Lake knows for the package,
`lean/Regula/TestListing.lean`, with `lean --run` before the package is built, so the listing
imports only Lake. The listing makes its load configuration itself
(`Regula.TestListing.loadConfig`), not with `Lake.LakeOptions.mkLoadConfig`, whose module links the
code of every command of Lake. This module proves the two configurations equal (`loadConfig_eq`).

The proof reduces both sides, so it reads bodies that those modules do not expose, and each
`import all` above is what makes one visible: `loadConfig` of `Regula.TestListing`, `mkLoadConfig`
and what it calls of `Lake.CLI.Main`, and the bind of `EST` (`Init.System.ST`), the monad of `EIO`.

It also proves of the definition of `main`, at `IO` and from any state of the world, what the program does with what the
load gives (`main_runs`, `main_zero`). This holds for every answer of Lake and of the streams, because `IO` is a state monad in
Lean's own definition. That the compiler keeps the order of the effects stays with the compiler.
-/

public section

/-- The load configuration of the listing is the one that Lake's commands make from the options
that hold only the installations that the listing found, with the same failures in the same order:
`Lake.LakeOptions.mkLoadConfig`, which `lake check-test` runs (`Lake/CLI/Main.lean:131-145`,
`:1094-1097`). The options of `lake check-test` also hold its arguments, which only the load of a
workspace reads (`Regula.TestListing`, "How it reads the package"). -/
theorem Regula.ProgramCheck.TestListing.loadConfig_eq (elanInstall? : Option Lake.ElanInstall)
    (leanInstall? : Option Lake.LeanInstall) (lakeInstall? : Option Lake.LakeInstall) :
    Regula.TestListing.loadConfig elanInstall? leanInstall? lakeInstall? =
      Lake.LakeOptions.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? } := by
  cases leanInstall? <;> cases lakeInstall? <;> rfl

namespace Regula.ProgramCheck.TestListing

open Regula.TestListing

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

/-- A run of `forM` that succeeds: for each member there are states of the world in which `f` of it succeeds. -/
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

/-- The load of the program is a straight line of Lake's calls, passing each result on: the statement is the body. -/
theorem readDriver_eq : readDriver = (do
    let installs ← Lake.findInstall?
    let loaded ← (((loadConfig installs.1 installs.2.1 installs.2.2).adapt toString >>= fun config =>
      liftM (m := EIO String) ((Lake.loadPackage config).toBaseIO : BaseIO _)) :
        EIO String (Option Lake.Package)).toBaseIO
    pure (loaded.map (Option.map (·.testDriver)))) := by
  rfl

/-- What `main` does, of its definition, at `IO` and from any state of the world: when it gives a result, that result is
the code of `outcome` on what the load gave, and it asked exactly the lines of `outcome` on standard output and then its
errors on standard error. It holds for every answer of the load and of the streams. -/
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

/-- Exit 0 from `main`, at `IO`: the load gave Lake's report of a test driver, the lines that `main` asked to print are what
`listing` gives for that driver, and for each line there are states of the world in which `IO.println` of it succeeds. -/
theorem main_zero (w w' : Void IO.RealWorld) (h : main w = .ok 0 w') :
    ∃ driver lines w₁, readDriver w = .ok (.ok (some driver)) w₁ ∧ listing driver = .ok lines ∧
      ∀ l ∈ lines, ∃ a b, IO.println l a = .ok () b := by
  obtain ⟨r, w₁, w₂, hr, hl, -, hc⟩ := main_runs w w' 0 h
  obtain ⟨driver, rfl, hd, -⟩ := outcome_of_zero hc.symm
  exact ⟨driver, _, w₁, hr, hd, forM_ok _ _ _ _ hl⟩

end Regula.ProgramCheck.TestListing
