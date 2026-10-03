import RegulaMarkdown

/-! Checks every Markdown document the repository tracks for a rule ID in prose that is not a
link to its rule page (`Regula.Markdown.check`). The documents are the files Git tracks below
the repository root whose extension is `md` or `markdown`, as `git ls-files` lists them; each is
read from the working tree. The documentation step of acceptance runs it
(`lean/RegulaVerification.lean`). -/

open Regula.Markdown

/-- The paths of the tracked Markdown documents below `root`, relative to it. -/
def trackedDocuments (root : System.FilePath) : IO (List String) := do
  let listed ← IO.Process.output { cmd := "git", args := #["ls-files", "-z"], cwd := some root }
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"git ls-files failed in {root}: {listed.stderr}"
  return (listed.stdout.splitOn "\x00").filter isMarkdown

/-- Check the tracked Markdown documents of the repository at the directory given as the only
argument. Exit code 0 when there is at least one document and none is refused, and 1
otherwise, after printing each refusal with its file, its line and the ID or the construct. -/
def main (args : List String) : IO UInt32 := do
  let [root] := args
    | IO.eprintln "usage: lake exe regula-markdown REPOSITORY"
      return 1
  let documents ← trackedDocuments root
  if documents.isEmpty then
    IO.eprintln s!"FAIL: Git tracks no Markdown document below {root}"
    return 1
  let mut refusals : List String := []
  for document in documents do
    let source ← IO.FS.readFile (System.FilePath.mk root / document)
    refusals := refusals ++ check document source
  unless refusals.isEmpty do
    IO.eprintln ("FAIL: tracked Markdown documents have a rule ID in prose that is not a link to \
      its rule page, or a construct the check does not read:\n" ++ "\n".intercalate refusals)
    return 1
  IO.println s!"Markdown documents: {documents.length} tracked documents read by md4c; every rule \
    ID in their prose links to its rule page"
  return 0
