module
public import Lake.Load.Config

/-! # Loaded configuration language

Read the language from the relative configuration path selected by Lake, not its resolved
symlink target. The exact correspondence below is about the supplied path's extension.
-/

public section

namespace Regula.Checker.LakeConfig

open System

/-- The language of a selected relative configuration path, or an error for an unsupported
extension. Callers pass `Package.relConfigFile`, which Lake retains after selection.

Assumes: Lake v4.34.1's loader, with no explicit `configLang?`, selects the language from
`relConfigFile.extension` (`Lake/Load/Package.lean:100-109`), and completes an extensionless
relative path with the selected extension (`:110-123`). Regula's workspace loader uses that
default. The resolved `configFile` can name a symlink target with a different extension. -/
def language (relative : FilePath) : Except String _root_.Lake.ConfigLang :=
  match relative.extension with
  | some "lean" => .ok .lean
  | some "toml" => .ok .toml
  | _ => .error s!"lake-config-language: unsupported selected relative configuration {relative}"

/-- For every supplied path and language, the executed reader returns that language exactly
when the path has its supported extension. No filesystem or Lake execution is proved. -/
theorem language_ok_iff (relative : FilePath) (kind : _root_.Lake.ConfigLang) :
    language relative = .ok kind ↔
      relative.extension = some (match kind with | .lean => "lean" | .toml => "toml") := by
  cases h : relative.extension with
  | none => cases kind <;> simp [language, h]
  | some extension =>
    by_cases lean : extension = "lean"
    · cases kind <;> simp [language, h, lean]
    · by_cases toml : extension = "toml"
      · cases kind <;> simp [language, h, toml]
      · cases kind <;> simp [language, h, lean, toml]

end Regula.Checker.LakeConfig
