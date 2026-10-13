import Regula.Site.Build
import Regula.TaskManager

/-! # The control of the renderers' destinations (issue 424)

`regula-site` and `regula-standard`, the programs of the website package, render through Verso's
`manualMain`, which writes the places that their options name: the pages below `--output DIR`, the
saved state of `--delay-html-multi FILE` and the word count of `--with-word-count FILE`. Each
program invalidates these places before it renders, and its refusal in a process without Lean's
task manager invalidates them in a run's place (`RegulaRender.begin` and `RegulaRender.refuse` in
the website package). Without that, a refused run left an earlier run's saved state in place, and
`--resume-html-multi FILE` rendered from it (issue 424). Each program first resolves these places
into a plan, observes the files of its removals and reads by their identity and admits that
observation. So it stops before it removes anything when a removal could reach a file that the
render reads, or a saved state or a word count could be in the output directory
(`RegulaRender.resolvePlan`, `RegulaRender.refusal`).

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

/-- Require that the refused run `output` of the program `program` stopped as its guard does:
exit code 1 and the guard's reason line on standard error (`Regula.TaskManager.refusalLine`). -/
private def requireRefused (program : String) (output : IO.Process.Output) : IO Unit := do
  let line := Regula.TaskManager.refusalLine program Regula.Probe.taskManagerMissingReason
  requireChecks [⟨s!"{program} with LEAN_NUM_THREADS=0 did not refuse with exit 1 and the \
    guard's line {repr line} {shown output}",
    output.exitCode == 1 && (output.stderr.splitOn "\n").contains line⟩]

/-- The issue's reproduction with `regula-standard` at `program`, in the directory `scratch`: a
delayed render writes its saved state, and a resumed render renders from it, which reads the
cross-reference table that the delayed render left. Then a refused run with the same options and a
word count removes the saved state, the word count and the pages, and a resumed render stops,
with no pages, instead of rendering from an earlier state. -/
private def reproduction (website program scratch : FilePath)
    (env refusing : Array (String × Option String)) : IO Unit := do
  let out := scratch / "standard"
  let state := scratch / "standard-state.json"
  let count := scratch / "standard-count.txt"
  let pages := out / "html-multi"
  let delay := #["--output", out.toString, "--delay-html-multi", state.toString]
  let resume := #["--output", out.toString, "--resume-html-multi", state.toString]
  let delayed ← run website program.toString delay env
  requireChecks [⟨s!"a delayed render of regula-standard did not write its saved state and its \
    cross-reference table {shown delayed}",
    delayed.exitCode == 0 && (← present state) && (← present (pages / "xref.json"))⟩]
  let resumed ← run website program.toString resume env
  requireChecks [⟨s!"a resumed render of regula-standard did not render from the saved state \
    {shown resumed}", resumed.exitCode == 0 && (← present (pages / "index.html"))⟩]
  seed count
  let refused ← run website program.toString (delay ++ #["--with-word-count", count.toString])
    refusing
  requireRefused "regula-standard" refused
  requireChecks [⟨s!"a refused run of regula-standard left its saved state, its word count or its \
    pages in place {shown refused}",
    !(← present state) && !(← present count) && !(← present pages)⟩]
  let stale ← run website program.toString resume env
  requireChecks [⟨s!"a resumed render of regula-standard after a refused run rendered from an \
    earlier saved state {shown stale}", stale.exitCode != 0 && !(← present (pages / "index.html"))⟩]

/-- The refusals of the program `name` at `program`, in the directory `scratch`, without a render.
A refused delayed render removes the saved state, the word count and each directory of pages that
earlier runs left, also one of a mode that the options do not select (`tex`). A refused resumed
render removes each directory of pages, and each entry of its own but the cross-reference table that
it reads, and keeps its saved state, outside the output directory. A run whose saved state is in its
output directory stops before it removes or renders anything. -/
private def refusals (website program scratch : FilePath) (name : String)
    (env refusing : Array (String × Option String)) : IO Unit := do
  let out := scratch / s!"{name}-delay"
  let state := scratch / s!"{name}-state.json"
  let count := scratch / s!"{name}-count.txt"
  seed state
  seed count
  seed (out / "html-multi" / "index.html")
  seed (out / "tex" / "main.tex")
  let refused ← run website program.toString #["--output", out.toString, "--delay-html-multi",
    state.toString, "--with-word-count", count.toString] refusing
  requireRefused name refused
  requireChecks [⟨s!"a refused delayed render of {name} left its saved state, its word count or \
    a directory of pages in place {shown refused}",
    !(← present state) && !(← present count) && !(← present (out / "html-multi")) &&
      !(← present (out / "tex"))⟩]
  let out := scratch / s!"{name}-resume"
  let pages := out / "html-multi"
  let state := scratch / s!"{name}-resumed.json"
  seed state
  seed (pages / "xref.json") "{}"
  seed (pages / "index.html")
  seed (pages / "page" / "index.html")
  seed (out / "html-single" / "index.html")
  let refused ← run website program.toString #["--output", out.toString, "--resume-html-multi",
    state.toString] refusing
  requireRefused name refused
  requireChecks [⟨s!"a refused resumed render of {name} removed what it reads, the \
    cross-reference table or the saved state, or left a page in place {shown refused}",
    (← present (pages / "xref.json")) && (← present state) &&
      !(← present (pages / "index.html")) && !(← present (pages / "page")) &&
      !(← present (out / "html-single"))⟩]
  let inside := out / "state.json"
  seed (pages / "index.html")
  let confined ← run website program.toString #["--output", out.toString, "--delay-html-multi",
    inside.toString] env
  requireChecks [⟨s!"a run of {name} with its saved state in its output directory did not stop \
    with the reason before it removed or rendered anything {shown confined}",
    confined.exitCode != 0 && (confined.stderr.splitOn "may be in the output directory").length > 1 &&
      (← present (pages / "index.html")) && !(← present inside)⟩]

/-- Whether the run `output` stopped with a nonzero exit code and `reason` on standard error. -/
private def stoppedWith (output : IO.Process.Output) (reason : String) : Bool :=
  output.exitCode != 0 && (output.stderr.splitOn reason).length > 1

/-- The runs of the program `name` at `program`, in the directory `scratch`, that stop with the
reason before they remove or render anything, one for each case that the resolution of a render or
the admission of its observation refuses (`RegulaRender.resolvePlan`, `RegulaRender.refusal`):

- a kept cross-reference table that is a symbolic link, through which Verso would write a file
  outside the output directory;
- an empty output directory;
- an output directory with a trailing separator and a saved state in it;
- a saved state that is a symbolic link to a file in the output directory;
- a word count at the saved state that a resumed render reads;
- a saved state in an absent output directory spelled in another case;
- a word count that is a hard link of the saved state that a resumed render reads, the same file
  by its identity;
- a word count at the remote configuration. -/
private def stops (website program scratch : FilePath) (name : String)
    (env : Array (String × Option String)) : IO Unit := do
  let base := scratch / s!"{name}-stops"
  let target := base / "target.txt"
  seed target "target"
  let link (destination place : FilePath) : IO Unit := do
    let made ← run base "ln" #["-s", destination.toString, place.toString]
    requireChecks [⟨s!"ln -s {destination} {place} {shown made}", made.exitCode == 0⟩]
  let out := base / "linked-table"
  let state := base / "table-state.json"
  seed (out / "html-multi" / "index.html")
  seed state
  link target (out / "html-multi" / "xref.json")
  let linked ← run website program.toString #["--output", out.toString, "--resume-html-multi",
    state.toString] env
  requireChecks [⟨s!"a resumed render of {name} whose cross-reference table is a symbolic link did \
    not stop before it removed anything, or changed the link's target {shown linked}",
    stoppedWith linked "is not a file at its own place" &&
      (← IO.FS.readFile target) == "target" && (← present (out / "html-multi" / "index.html"))⟩]
  let empty ← run website program.toString #["--output", "", "--without-html-multi"] env
  requireChecks [⟨s!"a run of {name} with an empty output directory did not stop {shown empty}",
    stoppedWith empty "is an empty path"⟩]
  let fresh := base / "fresh"
  let trailing ← run website program.toString #["--output", fresh.toString ++ "/",
    "--delay-html-multi", (fresh / "state.json").toString] env
  requireChecks [⟨s!"a run of {name} with a trailing separator in its output directory and its \
    saved state there did not stop before it made anything {shown trailing}",
    stoppedWith trailing "may be in the output directory" && !(← present fresh)⟩]
  let out := base / "linked-state"
  let saved := out / "html-multi" / "saved" / "state.json"
  let linkedState := base / "linked-state.json"
  seed saved
  link saved linkedState
  let through ← run website program.toString #["--output", out.toString, "--resume-html-multi",
    linkedState.toString] env
  requireChecks [⟨s!"a resumed render of {name} whose saved state is a symbolic link to a file in \
    its output directory did not stop before it removed the file {shown through}",
    stoppedWith through "is not a file at its own place" && (← present saved)⟩]
  let state := base / "single-state.json"
  seed state
  let same ← run website program.toString #["--output", (base / "same").toString,
    "--resume-html-single", state.toString, "--without-html-multi", "--with-word-count",
    state.toString] env
  requireChecks [⟨s!"a resumed render of {name} whose word count is its saved state did not stop \
    before it removed the saved state {shown same}",
    stoppedWith same "which the render removes first, may be or contain" &&
      (← present state)⟩]
  let lower := base / "lower"
  let upper := base / "LOWER" / "state.json"
  let cased ← run website program.toString #["--output", lower.toString, "--delay-html-multi",
    upper.toString] env
  requireChecks [⟨s!"a run of {name} whose saved state differs from a path in its absent output \
    directory only in case did not stop before it made anything {shown cased}",
    stoppedWith cased "may be in the output directory" && !(← present lower) &&
      !(← present (base / "LOWER"))⟩]
  let state := base / "hard-state.json"
  let hard := base / "hard-count.txt"
  seed state
  let linkedHard ← run base "ln" #[state.toString, hard.toString]
  requireChecks [⟨s!"ln {state} {hard} {shown linkedHard}", linkedHard.exitCode == 0⟩]
  let identical ← run website program.toString #["--output", (base / "hard").toString,
    "--resume-html-multi", state.toString, "--with-word-count", hard.toString] env
  requireChecks [⟨s!"a resumed render of {name} whose word count is a hard link of its saved state \
    did not stop before it removed the link {shown identical}",
    stoppedWith identical "which the render removes first, may be or contain" &&
      (← present state) && (← present hard)⟩]
  let remotes := base / "remotes.json"
  seed remotes "{}"
  let remote ← run website program.toString #["--output", (base / "remote").toString,
    "--remote-config", remotes.toString, "--with-word-count", remotes.toString] env
  requireChecks [⟨s!"a run of {name} whose word count is its remote configuration did not stop \
    before it removed the configuration {shown remote}",
    stoppedWith remote "which the render removes first, may be or contain" &&
      (← present remotes)⟩]

/-- The run of `regula-site` at `program`, in the website package `website`, whose word count is the
stylesheet that its configuration copies (`Generated/regula.css`): it stops with the reason before
it removes anything, and the stylesheet stays as it was. -/
private def copySource (website program scratch : FilePath)
    (env : Array (String × Option String)) : IO Unit := do
  let stylesheet := website / "Generated" / "regula.css"
  let before ← present stylesheet
  let copied ← run website program.toString #["--output", (scratch / "copy-source").toString,
    "--with-word-count", "Generated/regula.css"] env
  requireChecks [⟨s!"a run of regula-site whose word count is the stylesheet that it copies did \
    not stop before it removed the stylesheet {shown copied}",
    stoppedWith copied "which the render removes first, may be or contain" &&
      (← present stylesheet) == before⟩]

/-- Build `regula-site` and `regula-standard` in the website package of the repository at
`root`, then run the issue's reproduction with `regula-standard` (`reproduction`), the refusals
(`refusals`) and the stopped runs (`stops`) of both programs, and the stopped run of `regula-site`
on the file that it copies (`copySource`), in a fresh scratch directory. The first failure stops
it. It runs after `lake exe site build`, which builds the website package and generates the sources
of `regula-site`. -/
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
      refusals website (program name) scratch name cleanEnv refusing
      stops website (program name) scratch name cleanEnv
    copySource website (program "regula-site") scratch cleanEnv

end Regula.Site.RendererRefusal
