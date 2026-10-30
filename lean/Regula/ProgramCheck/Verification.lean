import RegulaVerification.Driver
import Regula.Filesystem

/-! # The dependency check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only the toolchain's libraries. The driver reads the root package's manifest and package
overrides file with Lake's own readers before the first acceptance step
(`RegulaVerification.dependencyFree`). `dependencyFree_effective` proves that a read that the driver
accepts has no entry for any name. The control below runs that read on files that it writes. -/

-- The first acceptance step's check that the root package requires nothing, over the driver's read
-- of a root's manifest and package overrides file: a manifest that records no package is accepted,
-- and again after each refused case is undone; an overrides file that records an entry, a manifest
-- that records a package and an absent manifest are refused.
run_cmd do
  let outcome ← (Regula.Filesystem.withOwnTempDir fun root => do
    let manifest := root / "lake-manifest.json"
    let overrides := root / ".lake" / "package-overrides.json"
    IO.FS.createDirAll (root / ".lake")
    let entry : _root_.Lake.PackageEntry :=
      { name := `batteries, inherited := false
        src := .git "https://example.invalid/batteries" "9999999999999999999999999999999999999999"
          none none }
    let lock (packages : Array _root_.Lake.PackageEntry) : _root_.Lake.Manifest :=
      { name := `regula, lakeDir := ".lake", fixedToolchain := false
        packagesDir? := some ".lake/packages", packages }
    let free : IO Bool := do
      return RegulaVerification.dependencyFree
        (← RegulaVerification.readRoot (RegulaVerification.rootFiles root))
    let require (what : String) (holds : Bool) : IO Unit :=
      unless holds do throw <| IO.userError what
    (lock #[]).save manifest
    require "refused a root that requires nothing" (← free)
    (lock #[entry]).save overrides
    require "accepted an overrides file that records an entry" !(← free)
    IO.FS.removeFile overrides
    require "refused a root that requires nothing, after the overrides file" (← free)
    (lock #[entry]).save manifest
    require "accepted a manifest that records a package" !(← free)
    IO.FS.removeFile manifest
    require "accepted an absent manifest" !(← free)
    (lock #[]).save manifest
    require "refused a root that requires nothing, after the absent manifest" (← free)).toBaseIO
  match outcome with
  | .ok () => pure ()
  | .error error => throwError "the control of the driver's dependency check failed: {error}"

namespace Regula.ProgramCheck.Verification

/-- A read that `dependencyFree` accepts is a manifest and the entries of an overrides file among
which no entry has any name: Lake materializes no package from it. -/
theorem dependencyFree_effective
    {read : Option (_root_.Lake.Manifest × Array _root_.Lake.PackageEntry)}
    (h : RegulaVerification.dependencyFree read = true) :
    ∃ manifest overrides, read = some (manifest, overrides) ∧
      ∀ name, (manifest.packages ++ overrides).findRev? (·.name == name) = none := by
  obtain ⟨manifest, rfl, hPackages⟩ := (RegulaVerification.dependencyFree_iff read).mp h
  exact ⟨manifest, #[], rfl, fun name => by simp [hPackages]⟩

end Regula.ProgramCheck.Verification
