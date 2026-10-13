import Regula.Site.Build
import Regula.TaskManager

/-! # The control of the renderers' destinations (issue 424)

`regula-site` and `regula-standard`, the programs of the website package, render through Verso's
`manualMain`, which writes the places that their options name: the pages below `--output DIR`, the
saved state of `--delay-html-multi FILE` and the word count of `--with-word-count FILE`. Each
program refuses a process without Lean's task manager before Verso starts. Before issue 424, that
refusal left an earlier run's saved state in place, and `--resume-html-multi FILE` rendered from it.

Regula invalidates the destinations of the runs it refuses itself; a run Verso starts keeps Verso's
write behaviour. The refusal reads the options with Verso's own parser and moves each destination
that they name and where something is into a new directory beside it, under its own name
(`RegulaRender.refuse` in the website package, `Regula.Filesystem.moveAside`). It removes nothing.

`control` builds the two programs in the website package and runs them. The processes, Verso and
the filesystem are its subject, an external boundary: it observes this build's programs and proves
nothing. `lake exe site renderer-refusal` runs it, after `lake exe site build` in
`./scripts/verify.sh site`. -/

namespace Regula.Site.RendererRefusal

open System Regula.Qualification

/-- Whether something is at `path`, by a read that follows no symbolic link. -/
private def present (path : FilePath) : IO Bool := do
  try discard (Regula.Filesystem.observeMetadata path); return true catch _ => return false

/-- The output of a process, for a failure message. -/
private def shown (output : IO.Process.Output) : String :=
  s!"(exit {output.exitCode})\n{output.stdout}{output.stderr}"

/-- Write `text` to the file `path`, after making its parent directory. -/
private def seed (path : FilePath) (text : String := "seed") : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

/-- Whether `text` occurs in `output`'s standard error. -/
private def reports (output : IO.Process.Output) (text : String) : Bool :=
  (output.stderr.splitOn text).length > 1

/-- Require that the refused run `output` of the program `program` stopped as its guard does:
exit code 1 and the guard's reason line on standard error (`Regula.TaskManager.refusalLine`). -/
private def requireRefused (program : String) (output : IO.Process.Output) : IO Unit := do
  let line := Regula.TaskManager.refusalLine program Regula.Probe.taskManagerMissingReason
  requireChecks [⟨s!"{program} with LEAN_NUM_THREADS=0 did not refuse with exit 1 and the \
    guard's line {repr line} {shown output}",
    output.exitCode == 1 && (output.stderr.splitOn "\n").contains line⟩]

/-- The new directories beside `path` into which a refusal moved it: the entries of the directory
where `path` is whose names are its own name followed by `.regula-refused-`. -/
private def asides (path : FilePath) : IO (List FilePath) := do
  let some name := path.fileName | return []
  let entries ← (path.parent.getD ".").readDir
  return (entries.filter (·.fileName.startsWith s!"{name}.regula-refused-")).toList.map (·.path)

/-- Require that the refused run `output` moved `path` aside whole, and give where it is now:
nothing is at `path`, one new directory is beside it, and the entry is in that directory under its
own name, with each path of `inside` below it. -/
private def requireMoved (output : IO.Process.Output) (path : FilePath)
    (inside : List FilePath := []) : IO FilePath := do
  let moved ← match ← asides path, path.fileName with
    | [aside], some name => pure (aside / name)
    | found, _ => throw (IO.userError s!"a refused run did not move {path} into one new directory \
        beside it, but made {found} {shown output}")
  let whole ← inside.allM fun entry => present (moved / entry)
  requireChecks [⟨s!"a refused run did not move {path} aside whole to {moved} {shown output}",
    !(← present path) && (← present moved) && whole⟩]
  return moved

/-- The issue's reproduction with `regula-standard` at `program`, in the directory `scratch`: a
delayed render writes its saved state and keeps a file that was in its output directory, since a
run that Verso starts does no more than Verso writes. A resumed render renders from the saved state.
Then a refused run with the same options and a word count moves the saved state, the word count
and the output directory aside whole, and a resumed render stops, with no pages, instead of
rendering from an earlier state. -/
private def reproduction (website program scratch : FilePath)
    (env refusing : Array (String × Option String)) : IO Unit := do
  let out := scratch / "standard"
  let state := scratch / "standard-state.json"
  let count := scratch / "standard-count.txt"
  let pages := out / "html-multi"
  let delay := #["--output", out.toString, "--delay-html-multi", state.toString]
  let resume := #["--output", out.toString, "--resume-html-multi", state.toString]
  seed (out / "kept.txt")
  let delayed ← run website program.toString delay env
  requireChecks [⟨s!"a delayed render of regula-standard did not write its saved state and its \
    cross-reference table, or did not keep a file of its output directory {shown delayed}",
    delayed.exitCode == 0 && (← present state) && (← present (pages / "xref.json")) &&
      (← present (out / "kept.txt"))⟩]
  let resumed ← run website program.toString resume env
  requireChecks [⟨s!"a resumed render of regula-standard did not render from the saved state \
    {shown resumed}", resumed.exitCode == 0 && (← present (pages / "index.html"))⟩]
  seed count
  let refused ← run website program.toString (delay ++ #["--with-word-count", count.toString])
    refusing
  requireRefused "regula-standard" refused
  discard (requireMoved refused state)
  discard (requireMoved refused count)
  discard (requireMoved refused out ["kept.txt", ("html-multi" : FilePath) / "index.html"])
  let stale ← run website program.toString resume env
  requireChecks [⟨s!"a resumed render of regula-standard after a refused run rendered from an \
    earlier saved state {shown stale}",
    stale.exitCode != 0 && !(← present (pages / "index.html"))⟩]

/-- The refusals of the program `name` at `program`, in the directory `scratch`, without a render:

- a refused delayed render moves its saved state, its word count and its output directory aside
  whole, with the pages of a mode that the options do not select (`tex`);
- a refused resumed render moves its output directory aside and keeps the saved state that it
  reads, which its options name as no destination;
- a word count that is a symbolic link is moved itself, and its target stays;
- a saved state in the output directory moves with it;
- an output directory `.` or an empty one is reported and stays, and the word count is still moved;
- a word count in a directory where the refusal can make nothing is reported and stays;
- options that Verso's parser refuses move nothing. -/
private def refusals (program scratch : FilePath) (name : String)
    (refusing : Array (String × Option String)) : IO Unit := do
  let base := scratch / s!"{name}-refusals"
  let refuse (cwd : FilePath) (args : Array String) : IO IO.Process.Output := do
    let output ← run cwd program.toString args refusing
    requireRefused name output
    return output
  let out := base / "delay"
  let state := base / "state.json"
  let count := base / "count.txt"
  seed state
  seed count
  seed (out / "html-multi" / "index.html")
  seed (out / "tex" / "main.tex")
  let refused ← refuse base #["--output", out.toString, "--delay-html-multi", state.toString,
    "--with-word-count", count.toString]
  discard (requireMoved refused state)
  discard (requireMoved refused count)
  discard (requireMoved refused out
    [("html-multi" : FilePath) / "index.html", ("tex" : FilePath) / "main.tex"])
  let out := base / "resume"
  let resumed := base / "resumed.json"
  seed resumed "resumed"
  seed (out / "html-multi" / "xref.json") "{}"
  let refused ← refuse base #["--output", out.toString, "--resume-html-multi", resumed.toString]
  discard (requireMoved refused out [("html-multi" : FilePath) / "xref.json"])
  requireChecks [⟨s!"a refused resumed render of {name} moved or changed the saved state that it \
    reads {shown refused}",
    (← IO.FS.readFile resumed) == "resumed" && (← asides resumed).isEmpty⟩]
  let target := base / "target.txt"
  let link := base / "linked-count.txt"
  seed target "target"
  let made ← run base "ln" #["-s", target.toString, link.toString]
  requireChecks [⟨s!"ln -s {target} {link} {shown made}", made.exitCode == 0⟩]
  let refused ← refuse base #["--output", (base / "linked").toString, "--with-word-count",
    link.toString]
  let moved ← requireMoved refused link
  requireChecks [⟨s!"a refused run of {name} whose word count is a symbolic link did not move \
    the link itself, or moved or changed its target {shown refused}",
    (← moved.symlinkMetadata).type == .symlink && (← IO.FS.readFile target) == "target" &&
      (← asides target).isEmpty⟩]
  let out := base / "nested"
  seed (out / "state.json")
  let refused ← refuse base #["--output", out.toString, "--delay-html-multi",
    (out / "state.json").toString]
  discard (requireMoved refused out ["state.json"])
  let dot := base / "dot"
  seed (dot / "kept.txt")
  seed (dot / "count.txt")
  let refused ← refuse dot #["--output", ".", "--with-word-count", "count.txt"]
  discard (requireMoved refused (dot / "count.txt"))
  requireChecks [⟨s!"a refused run of {name} with the output directory `.` moved it, or did not \
    report it {shown refused}",
    (← present (dot / "kept.txt")) && (← asides dot).isEmpty &&
      reports refused ". was not moved aside: its last component is `.` or `..`"⟩]
  let refused ← refuse dot #["--output", "", "--without-html-multi"]
  requireChecks [⟨s!"a refused run of {name} with an empty output directory did not report it \
    {shown refused}",
    reports refused "was not moved aside: it is an empty path" &&
      (← present (dot / "kept.txt"))⟩]
  let locked := base / "locked"
  seed (locked / "count.txt")
  let lock ← run base "chmod" #["a-w", locked.toString]
  requireChecks [⟨s!"chmod a-w {locked} {shown lock}", lock.exitCode == 0⟩]
  try
    let refused ← refuse base #["--output", (base / "unmade").toString, "--with-word-count",
      (locked / "count.txt").toString]
    requireChecks [⟨s!"a refused run of {name} whose word count is in a directory where nothing \
      can be made did not report it, or moved it {shown refused}",
      reports refused s!"{locked / "count.txt"} was not moved aside: " &&
        (← present (locked / "count.txt")) && (← asides (locked / "count.txt")).isEmpty⟩]
  finally
    discard (run base "chmod" #["u+w", locked.toString])
  let out := base / "unparsed"
  seed (out / "index.html")
  let refused ← refuse base #["--output", out.toString, "--unknown-option"]
  requireChecks [⟨s!"a refused run of {name} with options that Verso's parser refuses moved \
    something, or did not report the parser's refusal {shown refused}",
    reports refused "nothing was moved aside: Verso's parser refused the options" &&
      (← present (out / "index.html")) && (← asides out).isEmpty⟩]

/-- Build `regula-site` and `regula-standard` in the website package of the repository at
`root`, then run the issue's reproduction with `regula-standard` (`reproduction`) and the refusals
of both programs (`refusals`), in a fresh scratch directory. The first failure stops it. It runs
after `lake exe site build`, which builds the website package and generates the sources of
`regula-site`. -/
def control (root : FilePath) : IO Unit := do
  let website := root / "website"
  let built ← run website "lake" #["build", "regula-site", "regula-standard"] cleanEnv
  requireChecks [⟨s!"build of regula-site and regula-standard {shown built}",
    built.exitCode == 0⟩]
  let refusing := cleanEnv.push ("LEAN_NUM_THREADS", some "0")
  let program (name : String) := website / ".lake" / "build" / "bin" / name
  Regula.Checker.withScratch root "site-renderer-refusal" fun scratch => do
    reproduction website (program "regula-standard") scratch cleanEnv refusing
    for name in ["regula-standard", "regula-site"] do
      refusals (program name) scratch name refusing

end Regula.Site.RendererRefusal
