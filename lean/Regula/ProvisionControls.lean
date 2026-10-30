import Regula.Filesystem
import Regula.Site.Build
import Lean.Elab.Command

/-! # Controls of the selection of a pinned package

The site's record of the website's Verso revision, `Regula.Site.Build.versoRevision`, reads Lake's
manifest and package overrides file with Lake's own readers. These controls observe that boundary
once, on files that they write, with a restored positive control after each case: it takes the last
`verso` entry, and an override's, and a path override of `verso` is refused. They read no network.
The first acceptance step builds this module, and its build fails when a control does not give the
expected result. No program imports it. -/

open System
namespace Regula.ProvisionControls

/-- A manifest entry of the Git package `name` at the commit `rev` from `url`, in the form that Lake
writes. -/
private def gitEntry (name url rev : String) : Lean.Json :=
  Lean.Json.mkObj [("url", url), ("type", "git"), ("subDir", Lean.Json.null), ("scope", ""),
    ("rev", rev), ("name", name), ("manifestFile", "lake-manifest.json"), ("inputRev", rev),
    ("inherited", false), ("configFile", "lakefile.lean")]

/-- A manifest entry of the package `name` in the directory `dir`, in the form that Lake writes,
inherited when `inherited` holds. -/
private def pathEntry (name dir : String) (inherited := false) : Lean.Json :=
  Lean.Json.mkObj [("type", "path"), ("scope", ""), ("name", name),
    ("manifestFile", "lake-manifest.json"), ("inherited", inherited), ("dir", dir),
    ("configFile", "lakefile.lean")]

/-- The text of a manifest with `entries` that records the packages directory `packagesDir`: the
member is left out for `none`, and is `null` for `some none`. -/
private def manifestText (packagesDir : Option (Option String)) (entries : List Lean.Json) :
    String :=
  let recorded := match packagesDir with
    | none => []
    | some dir => [("packagesDir", match dir with | some dir => Lean.Json.str dir | none => .null)]
  (Lean.Json.mkObj ([("version", Lean.Json.str "1.2.0")] ++ recorded ++
    [("packages", Lean.Json.arr entries.toArray), ("name", "regula_control"),
      ("lakeDir", ".lake")])).pretty

/-- The text of a package overrides file with `entries`, in the form that Lake writes. -/
private def overridesText (entries : List Lean.Json) : String :=
  (Lean.Json.mkObj [("schemaVersion", "1.2.0"), ("packages", Lean.Json.arr entries.toArray)]).pretty

/-- Fail with `label` and `what` unless `holds`. -/
private def requireSelection (label what : String) (holds : Bool) : IO Unit :=
  unless holds do throw <| IO.userError s!"selection control {label}: {what}"

/-- Fail unless the run `action` fails with an error whose text contains `needle`. -/
private def requireRefused {α : Type} (label needle : String) (action : IO α) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw <| IO.userError s!"selection control {label}: not refused"
  | .error error =>
    requireSelection label s!"refused with '{error}', not for '{needle}'"
      (((toString error).splitOn needle).length > 1)

-- The site's record of the website's Verso revision.
run_cmd do
  Regula.Filesystem.withOwnTempDir fun root => do
    let website := root / "website"
    let manifest := website / "lake-manifest.json"
    let overrides := website / ".lake" / "package-overrides.json"
    IO.FS.createDirAll (website / ".lake")
    let (pinned, second, third) := ("6666666666666666666666666666666666666666",
      "7777777777777777777777777777777777777777", "8888888888888888888888888888888888888888")
    let url := "https://example.invalid/verso"
    let committed := [gitEntry "verso" url pinned,
      gitEntry "MD4Lean" "https://example.invalid/md4lean" second]
    let revision : IO String := Regula.Site.Build.versoRevision root
    let positive (label : String) : IO Unit := do
      requireSelection label "another Verso revision" ((← revision) == pinned)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "site positive"
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages"))
      (committed ++ [gitEntry "verso" url second]))
    requireSelection "site duplicate verso entry" "not the last entry's revision"
      ((← revision) == second)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "site positive after the duplicate entry"
    IO.FS.writeFile overrides (overridesText [gitEntry "verso" url third])
    requireSelection "site overrides file" "not the override's revision" ((← revision) == third)
    IO.FS.writeFile overrides (overridesText [pathEntry "verso" "../verso"])
    requireRefused "site path override of verso" "materializes no Git package verso" revision
    IO.FS.removeFile overrides
    positive "site positive after the overrides file"

end Regula.ProvisionControls
