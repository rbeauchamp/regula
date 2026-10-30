import Regula.Site.Support
import RegulaCore.Site
import RegulaCore.Prose

/-! # The check of the rendered standard

What the documentation step of acceptance requires of the standard that the Verso package renders
alone (`lake exe site standard HTML DOCS`): each section and checklist-row anchor that the rule
registry links (`Regula.Site.standardAnchors`) and each anchor that the Markdown below `DOCS` links
(`Regula.Site.documentAnchors`) is defined, the rendered checklist's rows are exactly
`Regula.checklistRows`, in order (`Regula.Site.rowsMismatch`), the source of each cited section is
a file of the repository, and each rule ID in the prose of a rendered page is a link to its rule
page (`Regula.Prose.htmlErrors`). The decisions are the claimed `RegulaCore` functions; the
reads of the rendered files and of the Markdown are trusted filesystem effects.
-/

namespace Regula.Site.Standard

open System Regula.Site

/-- The files below `root` with the extension `extension`, each by its path below `root`, written
with `/`, and with its text. -/
def filesBelow (root : FilePath) (extension : String) : IO (List (String × String)) := do
  let components := root.normalize.components
  (← Regula.Filesystem.Construction.walkDirectory root).toList.filterMapM fun path => do
    if path.extension != some extension then return none
    let relative := "/".intercalate (path.normalize.components.drop components.length)
    return some (relative, ← IO.FS.readFile path)

/-- Refuse unless the standard rendered at `html` (the `html-multi` output of Verso) defines each
anchor that the registry and the Markdown below `docs` link, has exactly the checklist rows, cites
only sections whose source is a file below `root`, and links each rule ID of its prose. -/
def check (root html docs : FilePath) : IO Unit := do
  let htmlFiles ← filesBelow html "html"
  let pages := htmlFiles.map fun (path, source) => Page.ofHtml path source
  let missing := missingAnchors pages standardAnchors
  unless missing.isEmpty do
    throw <| IO.userError s!"the rendered standard does not define anchors the rule registry \
      links: {missing}"
  let markdown := (← filesBelow docs "md").map (·.2)
  let missing := missingAnchors pages (documentAnchors markdown)
  unless missing.isEmpty do
    throw <| IO.userError s!"the rendered standard does not define anchors the documentation \
      links: {missing}"
  let rows := renderedRows (← IO.FS.readFile (html / Regula.checklistChapter / "index.html"))
  if let some mismatch := rowsMismatch rows then
    throw <| IO.userError s!"the rendered checklist's rows are not Regula.checklistRows: \
      {mismatch}"
  let unknown ← Regula.Clause.all.filterM fun c => return !(← (root / c.source).pathExists)
  unless unknown.isEmpty do
    throw <| IO.userError s!"cited sections whose source is no file of the repository: \
      {unknown.map (·.heading)}"
  let bare := htmlFiles.flatMap fun (path, source) => Regula.Prose.htmlErrors "" path source
  unless bare.isEmpty do
    throw <| IO.userError ("rule IDs in the rendered prose are not links to their rule pages:\n" ++
      "\n".intercalate bare)

end Regula.Site.Standard
