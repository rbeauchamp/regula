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

/-- The summary of Regula, in Markdown: what it checks for each theorem, the foundation that the
project chooses, also through imports, and the cases that `lake build` accepts and `lake lint`
refuses. Its plain text is at most 350 characters, the limit of the description of a GitHub
repository. -/
def summary : String :=
  "A strict linter for Lean. It checks that each theorem of your project depends only on the \
    axioms of the foundation that you choose, also through its imports. Thus `lake lint` refuses \
    a `sorry`, an `axiom` of your project and `native_decide`, which `lake build` accepts."

/-- Markdown text without its backticks: the plain text of Markdown whose only markup is code
spans, as the summary is. -/
def plainText (markdown : String) : String := markdown.replace "`" ""

-- The plain text of the summary fits the description of a GitHub repository.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (plainText summary).length ≤ 350

end Regula.Site
