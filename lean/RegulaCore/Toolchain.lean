module

public import RegulaPolicy.Compiler

/-! # Installed compiler identity

The identity parser and exact installed-selector resolution used by `regula doctor`.
Compiler reports, Elan and filesystem observations remain trusted. -/

@[expose] public section

namespace Regula.Toolchain

/-- A compiler's identity and the observed capability used by declaration policy. -/
structure Identity where
  /-- The complete version string, including a prerelease suffix. -/
  version : String
  /-- The full forty-character Git commit. -/
  commit : String
  /-- Whether the compiler's origin-checked Core declares the legacy compiler-trust family. -/
  legacyCompilerTrust : RegulaPolicy.Compiler.LegacyCompilerTrust
  deriving BEq, DecidableEq, Repr

/-- A nonempty version and a complete lowercase hexadecimal source commit. -/
def Identity.valid (i : Identity) : Bool :=
  !i.version.isEmpty && i.commit.length == 40 &&
    i.commit.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- Admit the compiler probe's exact three-line output, including its final newline. -/
def parseIdentity (output : String) : Except String Identity :=
  match output.splitOn "\n" with
  | [v, h, capability, ""] =>
    match RegulaPolicy.Compiler.LegacyCompilerTrust.parse? capability with
    | none => .error "compiler capability is unknown"
    | some capability =>
      let i := Identity.mk v h capability
      if i.valid then .ok i else .error "compiler identity is incomplete"
  | _ => .error "compiler probe did not return exactly a version, full commit and capability"

/-- Parsing cannot replace a malformed or incomplete identity with a default. -/
theorem parseIdentity_valid {output : String} {i : Identity}
    (h : parseIdentity output = .ok i) : i.valid = true := by
  unfold parseIdentity at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h; assumption
      · cases h
  · cases h

/-- The toolchains `elan toolchain list` printed, one name on each line, without the
` (default)` marker Elan 3 appends to the default toolchain. A remaining line with a space,
such as Elan's notice that none is installed, names no toolchain. -/
def listedToolchains (output : String) : List String :=
  (output.splitOn "\n").map (·.trimAscii.toString.dropSuffix " (default)" |>.toString) |>.filter
    (fun line => !line.isEmpty && !line.contains ' ')

/-- The listed toolchain `selector` names: the selector itself, exactly as listed (a linked
toolchain or a full name). It resolves no channel, completes no shorter spelling and installs
nothing: a channel such as `stable` resolves only when the listing names a toolchain spelled
exactly so. -/
def installedName? (listed : List String) (selector : String) : Option String :=
  listed.find? (· == selector)

/-- A selector resolves only to itself, and only when it is listed. -/
theorem installedName?_spec {listed : List String} {selector name : String}
    (h : installedName? listed selector = some name) :
    name ∈ listed ∧ name = selector := by
  unfold installedName? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

end Regula.Toolchain
