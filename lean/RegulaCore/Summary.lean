/-! # The summary of Regula

`summary` is the summary of Regula, in Markdown, and `plainText` gives it as plain text. The site's
home page shows `summary` (`RegulaCore/SiteDocs.lean`) and its link previews show
`plainText summary` (`Regula.Site.tagline`), so those two cannot differ from it. The Markdown check
of acceptance (`markdown/MarkdownMain.lean`) refuses the root `README.md` and the adoption guide
unless its first top-level block is a title of level 1 and its second is the paragraph that md4c
reads for `summary` (`Regula.Markdown.summaryErrors`), and it refuses the `description` of
`lakefile.lean`, as Lake reads it, unless that description is `plainText summary`.

This module imports nothing, so each of those users can import it.
-/

namespace Regula.Site

/-- The summary of Regula, in Markdown: the proof defects it refuses, and the rule page of each
finding, which gives the fix. Its plain text is at most 350 characters, the limit of the
description of a GitHub repository. -/
def summary : String :=
  "A strict linter for Lean. Regula refuses proof holes, project axioms and proofs that trust \
    the compiler. Each finding links to its rule page, which gives the fix."

/-- Markdown text without its backticks: the plain text of Markdown whose only markup is code
spans, as the summary is. -/
def plainText (markdown : String) : String := markdown.replace "`" ""

-- The plain text of the summary fits the description of a GitHub repository.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (plainText summary).length ≤ 350

end Regula.Site
