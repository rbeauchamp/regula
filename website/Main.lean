import VersoManual
import RegulaSite
import RegulaCore.Site
import Generated

/-! Renders the generated rule reference as multi-page HTML. Run through
`lake exe site build` in the repository root, which generates `Generated` and the site
stylesheet `Generated/regula.css` first. Only Verso's search feature is enabled (the site renders
no mathematics, so KaTeX is not shipped). The stylesheet is copied once to each edition's root and
linked from every page's `<head>` after Verso's own, resolved through the page's `<base href>`;
the theme script is inlined so it runs before the first paint. Every page carries the project's
one-line description for link previews. -/

open Verso.Genre Manual
open Verso.Output (Html)

def main := manualMain (%doc Generated) (config := {
  emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 2,
  features := {.search},
  extraFilesHtml := [("Generated/regula.css", "regula.css")],
  extraJs := {⟨RegulaSite.themeScript⟩},
  extraHead := #[
    Html.tag "meta" #[("name", "color-scheme"), ("content", "light dark")] .empty,
    Html.tag "meta" #[("name", "description"), ("content", Regula.Site.tagline)] .empty,
    Html.tag "meta" #[("property", "og:description"), ("content", Regula.Site.tagline)] .empty,
    Html.tag "link" #[("rel", "stylesheet"), ("href", "regula.css")] .empty],
  sourceLink := some "https://github.com/rbeauchamp/regula",
  issueLink := some "https://github.com/rbeauchamp/regula/issues" })
