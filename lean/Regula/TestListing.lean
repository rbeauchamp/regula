module

public import Lake.CLI.Error
public import Lake.Load.Package
import Lake.Util.IO
meta import Lake.CLI.Error
meta import Lake.Load.Package
meta import Lake.Util.IO

public section

namespace Regula.TestListing

def Printable (c : Char) : Prop := 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E

def printable (c : Char) : Bool := 0x21 ≤ c.toNat && c.toNat ≤ 0x7E

theorem printable_iff (c : Char) : printable c = true ↔ Printable c := by
  simp [printable, Printable]

def listing (driver : String) : Except String (List String) :=
  if driver.isEmpty then .ok []
  else if driver.all printable then .ok [driver]
  else .error s!"Lake reports the test driver {driver.quote}, which has a character outside \
    U+0021 to U+007E, so this listing cannot print it as one test identifier"

theorem listing_ok_iff (driver : String) (lines : List String) :
    listing driver = .ok lines ↔
      (driver = "" ∧ lines = []) ∨
        (driver ≠ "" ∧ (∀ c ∈ driver.toList, Printable c) ∧ lines = [driver]) := by
  have all_iff : driver.all printable = true ↔ ∀ c ∈ driver.toList, Printable c := by
    simp only [String.all_bool_eq, List.all_eq_true, printable_iff]
  unfold listing
  by_cases empty : driver = ""
  · subst empty
    have isEmpty : "".isEmpty = true := rfl
    simp only [isEmpty, ite_true, Except.ok.injEq, ne_eq, not_true_eq_false, false_and, or_false,
      true_and]
    exact ⟨Eq.symm, Eq.symm⟩
  · have notEmpty : driver.isEmpty = false := String.isEmpty_eq_false_iff.mpr empty
    by_cases allPrintable : driver.all printable = true
    · simp only [notEmpty, allPrintable, Bool.false_eq_true, ite_false, ite_true, Except.ok.injEq,
        empty, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      exact ⟨fun printed => ⟨all_iff.mp allPrintable, printed.symm⟩,
        fun listed => listed.2.symm⟩
    · simp only [notEmpty, allPrintable, Bool.false_eq_true, ite_false, reduceCtorEq, empty,
        false_and, false_or, ne_eq, not_false_eq_true, true_and, false_iff, not_and]
      exact fun each => absurd (all_iff.mpr each) allPrintable

def loadConfig (elanInstall? : Option Lake.ElanInstall) (leanInstall? : Option Lake.LeanInstall)
    (lakeInstall? : Option Lake.LakeInstall) : EIO Lake.CliError Lake.LoadConfig := do
  let some wsDir ← Lake.resolvePath? "."
    | throw <| .missingRootDir "."
  let lake ← match lakeInstall? with
    | none => throw .unknownLakeInstall
    | some lake => pure lake
  let lean ← match leanInstall? with
    | none => throw .unknownLeanInstall
    | some lean => pure lean
  let lakeEnv ← Lake.Env.compute lake lean elanInstall? none |>.adapt fun msg => .invalidEnv msg
  return {
    lakeArgs? := some #[]
    lakeEnv
    wsDir
    relConfigFile := Lake.defaultConfigFile
    packageOverrides := #[]
    lakeOpts := {}
    leanOpts := Lean.Options.empty
    reconfigure := false
    updateDeps := false
    updateToolchain := true
  }

structure Outcome where
  lines : List String
  errors : List String
  code : UInt32

def outcome : Except String (Option String) → Outcome
  | .error why => { lines := [], errors := [s!"error: {why}"], code := 1 }
  | .ok none => { lines := [], errors := [], code := 1 }
  | .ok (some driver) =>
    match listing driver with
    | .ok lines => { lines, errors := [], code := 0 }
    | .error reason => { lines := [], errors := [s!"error: {reason}"], code := 1 }

theorem outcome_zero_iff (r : Except String (Option String)) :
    (outcome r).code = 0 ↔ ∃ driver lines, r = .ok (some driver) ∧ listing driver = .ok lines := by
  cases r with
  | error why => simp [outcome]
  | ok o =>
    cases o with
    | none => simp [outcome]
    | some driver =>
      simp only [outcome]
      cases hl : listing driver with
      | ok lines => simp [hl]
      | error reason => simp [hl]

theorem outcome_of_zero {r : Except String (Option String)} (h : (outcome r).code = 0) :
    ∃ driver, r = .ok (some driver) ∧ listing driver = .ok (outcome r).lines ∧ (outcome r).errors = [] := by
  obtain ⟨driver, lines, rfl, hl⟩ := (outcome_zero_iff r).mp h
  simp [outcome, hl]

theorem outcome_of_nonzero {r : Except String (Option String)} (h : (outcome r).code ≠ 0) :
    (outcome r).lines = [] := by
  cases r with
  | error why => rfl
  | ok o =>
    cases o with
    | none => rfl
    | some driver =>
      simp only [outcome] at h ⊢
      cases hl : listing driver with
      | ok lines => simp [hl] at h
      | error reason => rfl

def readDriver : IO (Except String (Option String)) := do
  let installs ← Lake.findInstall?
  let loaded ← (((loadConfig installs.1 installs.2.1 installs.2.2).adapt toString >>= fun config =>
    liftM (m := EIO String) ((Lake.loadPackage config).toBaseIO : BaseIO _)) :
      EIO String (Option Lake.Package)).toBaseIO
  pure (loaded.map (Option.map (·.testDriver)))

end Regula.TestListing

open Regula.TestListing in
def main : IO UInt32 := do
  let result := outcome (← readDriver)
  result.lines.forM IO.println
  result.errors.forM IO.eprintln
  return result.code
