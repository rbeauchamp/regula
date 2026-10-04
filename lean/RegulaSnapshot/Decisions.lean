import RegulaSnapshot
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of the snapshot controller

The decision kind of each pure decision `RegulaSnapshot` runs, with its `@[regula_decision]`
registration. The controller imports only the toolchain, because the installer and the
provisioning program run it with `lean --run` before the package is built. This second module of
its library imports it together with the two checker interfaces, and nothing the controller runs
imports this module. Each kind restates a theorem of the controller about the same definition and
adds the witnesses a kind requires.

The controller's validators `component` and `objectDigest` are private, so no other module can
name them. `Component` and `ObjectDigest` restate their bodies as the specification of the two
transport decisions; each contract is proved from the controller's theorem about the private
validator, so it elaborates only while the restated body unfolds to the executed one. -/
namespace RegulaSnapshot

/-- `admits` accepts exactly a version 1, source-built receipt whose identity, compiler, package
census and completed targets are the expected ones (`admits_iff`): it accepts such a receipt and
refuses the same receipt at version 0. -/
theorem checked_admits : Regula.ExecutableContract admits (fun admits =>
    Regula.Decides (· = true)
      (fun input : Identity × Receipt =>
        input.2.schema = 1 ∧ input.2.sourceBuilt = true ∧ input.2.identity = input.1 ∧
          input.2.compiler = input.1.compiler ∧ input.2.packages = input.1.packages ∧
          input.2.completedTargets = input.1.targets)
      (Function.uncurry admits)) :=
  let identity : Identity :=
    { recipe := 1, compiler := { selector := "", revision := "", version := "" }
      platform := .linuxX64, runtime := #[], inputs := #[], packages := #[], targets := #[] }
  let receipt (schema : Nat) : Receipt :=
    { schema, sourceBuilt := true, identity, compiler := identity.compiler
      packages := #[], completedTargets := #[] }
  ⟨.of_iff (fun input => admits_iff input.1 input.2)
    ⟨(identity, receipt 1), (admits_iff _ _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    ⟨(identity, receipt 0), fun accepted =>
      absurd ((admits_iff identity (receipt 0)).mp accepted).1 (by decide)⟩⟩

/-- A single non-hidden path component that is not an option: the body of the controller's
private `component`. -/
def Component (text : String) : Prop :=
  (!text.isEmpty && !text.startsWith "." && !text.startsWith "-" &&
    text.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') = true

/-- A full lowercase SHA-256 digest: the body of the controller's private `objectDigest`. -/
def ObjectDigest (text : String) : Prop :=
  (text.length == 64 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) = true

/-- The digest of the accepted witnesses is an `ObjectDigest`. -/
private theorem digest_witness :
    ObjectDigest "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" := by
  simp [ObjectDigest]; decide

/-- `Archives.valid` accepts exactly a version 1 descriptor whose archives are the compiler and
package roots in that order, each with at least one layer, every layer named by a `Component` and
carrying an `ObjectDigest` (`Archives.valid_iff`): it accepts a descriptor of one such layer per
root and refuses the same descriptor at version 0. -/
theorem checked_archives : Regula.ExecutableContract Archives.valid
    (Regula.Decides (· = true) (fun description : Archives =>
      description.schema = 1 ∧ description.archives.map (·.target) = #[.compiler, .packages] ∧
        ∀ archive ∈ description.archives, archive.chunks.isEmpty = false ∧
          ∀ chunk ∈ archive.chunks, Component chunk.name ∧ ObjectDigest chunk.sha256)) :=
  let compiler : Compiler := { selector := "", revision := "", version := "" }
  let identity : Identity :=
    { recipe := 1, compiler, platform := .linuxX64, runtime := #[], inputs := #[]
      packages := #[], targets := #[] }
  let receipt : Receipt :=
    { schema := 1, sourceBuilt := true, identity, compiler, packages := #[]
      completedTargets := #[] }
  let layer : Chunk :=
    { name := "a", sha256 := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }
  let archives : Array Archive :=
    #[{ target := .compiler, chunks := #[layer] }, { target := .packages, chunks := #[layer] }]
  ⟨.of_iff Archives.valid_iff
    ⟨{ schema := 1, receipt, archives }, by
      have named : Component "a" := by simp (config := { decide := true }) [Component]
      simp (config := { decide := true }) [Archives.valid, archives, layer]
      exact ⟨named, digest_witness⟩⟩
    ⟨{ schema := 0, receipt, archives }, fun accepted =>
      absurd ((Archives.valid_iff _).mp accepted).1 (by decide)⟩⟩

/-- `Location.valid` accepts exactly a location that names the requested platform and whose
reference is the Regula package prefix followed by an `ObjectDigest` (`Location.valid_iff`): it
accepts such a location for Linux and refuses one that names no platform. -/
theorem checked_location : Regula.ExecutableContract Location.valid (fun valid =>
    Regula.Decides (· = true)
      (fun input : Platform × Location =>
        input.2.platform = input.1.name ∧
          input.2.reference.startsWith "ghcr.io/rbeauchamp/regula-compiled@sha256:" = true ∧
          ObjectDigest (input.2.reference.drop
            "ghcr.io/rbeauchamp/regula-compiled@sha256:".length).toString)
      (Function.uncurry valid)) :=
  ⟨.of_iff (fun input => Location.valid_iff input.1 input.2)
    ⟨(.linuxX64, { platform := "ubuntu24.04-x86_64", reference :=
        "ghcr.io/rbeauchamp/regula-compiled@sha256:\
          0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" }), by
      simp (config := { decide := true }) [Function.uncurry, Location.valid, Platform.name]
      rw [show ("ghcr.io/rbeauchamp/regula-compiled@sha256:\
            0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".drop
              "ghcr.io/rbeauchamp/regula-compiled@sha256:".length).copy =
          "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef" from by decide]
      exact digest_witness⟩
    ⟨(.linuxX64, { platform := "", reference := "" }), fun accepted =>
      absurd ((Location.valid_iff _ _).mp accepted).1 (by decide)⟩⟩

attribute [regula_decision] admits Archives.valid Location.valid

end RegulaSnapshot
