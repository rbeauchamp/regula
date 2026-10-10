/-! # The summary of Regula

`summary` is the summary of Regula, in Markdown, and `plainText` gives it as plain text. The site's
home page shows `summary` (`RegulaCore/SiteDocs.lean`) and its link previews show
`plainText summary` (`Regula.Site.tagline`), so those two cannot differ from it. The Markdown check
of acceptance (`markdown/MarkdownMain.lean`) refuses the root `README.md` and the adoption guide
unless the first block after the title of each is a paragraph that md4c reads as it reads
`summary` (`Regula.Markdown.summaryErrors`), and it refuses the `description` of `lakefile.lean`,
as Lake reads it, unless that description is `plainText summary`.

This module imports nothing, so each of those users can import it.
-/

namespace Regula.Site

/-- The summary of Regula, in Markdown: what `lake lint` does not accept. -/
def summary : String :=
  "A strict linter for Lean projects. `lake lint` does not accept a theorem that depends on an \
    `axiom` of your project, on `native_decide` or on a `sorry`, also through its imports."

/-- Markdown text without its backticks: the plain text of Markdown whose only markup is code
spans, as the summary is. -/
def plainText (markdown : String) : String := markdown.replace "`" ""

end Regula.Site
