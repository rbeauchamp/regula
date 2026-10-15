import VersoManual
import RegulaRender
import RegulaSite
import Regula.TaskManagerCheck
import RegulaCore.Site
import Generated
import Regula.Removal
import Regula.ProgramCheck.Renderer

/-! Renders the generated rule reference as multi-page HTML. Run through
`lake exe site build` in the repository root, which generates `Generated` and the site
stylesheet `Generated/regula.css` first. Only Verso's search feature is enabled (the site renders
no mathematics, so KaTeX is not shipped). The stylesheet is copied once to each edition's root and
linked from every page's `<head>` after Verso's own, resolved through the page's `<base href>`;
the theme script is inlined so it runs before the first paint. Every page carries the project's
one-line description for link previews. -/

open Verso.Genre Manual
open Verso.Output (Html)

/-- The configuration of the site's render, before its command-line options. -/
def siteConfig : RenderConfig := {
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
  issueLink := some "https://github.com/rbeauchamp/regula/issues" }

set_option compiler.small 0 in
/-- Renders the site with Verso's command-line options `options` and the configuration `siteConfig`,
which its refusal reads them with too (`refuseSite`). The one call of Verso's `manualMain` in this
program is here: a listed entry of the process and environment rows of `Regula.Removal.boundaries`,
which admits only that row's renderer pairs below it. It is compiled without small-function
inlining (`compiler.small` 0), so its compiled code keeps that call. -/
@[noinline] def renderSite (options : List String) : IO UInt32 :=
  manualMain (%doc Generated) (options := options) (config := siteConfig)

/-- The refusal of the renderer in a process without Lean's task manager
(`Regula.TaskManager.guard`): it moves aside each destination that the arguments name for a render
with `siteConfig` (`RegulaRender.refuse`), and returns 1. For the reason that the guard gives before
each run (`Regula.TaskManager.startedReason`), it moves nothing and returns 1: a run that Verso
starts keeps Verso's write behaviour, and a resumed render reads the saved state of an earlier
one. -/
def refuseSite (reason : String) (args : List String) : IO UInt32 :=
  if reason == Regula.TaskManager.startedReason then pure 1
  else RegulaRender.refuse "regula-site" siteConfig args

/-- Renders the site; a process without Lean's task manager is refused before rendering starts,
with exit code 1 (`Regula.TaskManager.guard`). -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "regula-site" refuseSite renderSite

-- The process starts and environment reads that `main` and the initializers of the modules it
-- links reach, and the removals that the compiled code of those modules reaches, go through their
-- observers or sourced exemptions; Verso's writes are trusted effects of the library: the build of
-- this module fails otherwise (`Regula.ProgramCheck.Renderer.check`).
run_cmd Regula.ProgramCheck.Renderer.check

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
