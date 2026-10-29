import Regula.Site.Build
import Regula.TaskManager
import Regula.Scratch

/-! # The control of the renderers' destinations (issue 424)

`regula-site` and `regula-standard`, the programs of the website package, render through Verso's
`manualMain`, which writes the places that their options name: the pages below `--output DIR`, the
saved state of `--delay-html-multi FILE` and the word count of `--with-word-count FILE`. Each
program refuses a process without Lean's task manager before Verso starts, and `regula-standard`
also refuses a standard that lacks a section the rule registry cites. Before issue 424, a refusal
left an earlier run's saved state in place, and `--resume-html-multi FILE` rendered from it.

Regula invalidates the destinations of the runs it refuses itself, the guard's refusals and the
missing-sections refusal; a run Verso starts keeps Verso's write behaviour. Each refusal reads the
options with Verso's own parser and moves each destination that they name and where something is
into a new directory beside it, under its own name (`RegulaRender.refuse` in the website package,
`Regula.Filesystem.moveAside`). It removes nothing.

`control` builds the two programs in the website package and runs them. The processes, Verso and
the filesystem are its subject, an external boundary: it observes this build's programs and proves
nothing. It runs the guard's refusals only: the missing-sections refusal needs a standard that
lacks a cited section, and it is covered by the shared `RegulaRender.refuse` path, not by this
control. `lake exe site renderer-refusal` runs it, after `lake exe site build` in
`./scripts/verify.sh site`. -/

namespace Regula.Site.RendererRefusal

open System Regula.Site

/-- Whether something is at `path`, by a read that follows no symbolic link: `false` only when
nothing is there, and every other failure of the read thrown
(`Regula.Filesystem.entryIfPresent`). -/
private def present (path : FilePath) : IO Bool :=
  return (← Regula.Filesystem.entryIfPresent path).isSome

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

/-- Whether `text` starts with the suffix of a new directory's name and the end of its line: 16
hexadecimal digits (`Regula.Filesystem.moveAside`) and a line feed. -/
private def newSuffix (text : String) : Bool :=
  let chars := text.toList
  chars.length > 16 && (chars.take 16).all ("0123456789abcdef".toList.contains ·) &&
    chars[16]? == some '\n'

/-- Require that the refused run `output` of the program `program` stopped as its guard does:
exit code 1 and the guard's reason line on standard error (`Regula.TaskManager.refusalLine`). -/
private def requireRefused (program : String) (output : IO.Process.Output) : IO Unit := do
  let line := Regula.TaskManager.refusalLine program Regula.TaskManager.taskManagerMissingReason
  requireChecks [⟨s!"{program} with LEAN_NUM_THREADS=0 did not refuse with exit 1 and the \
    guard's line {repr line} {shown output}",
    output.exitCode == 1 && (output.stderr.splitOn "\n").contains line⟩]

/-- The new directories beside `path` into which a refusal moved it: the entries of the directory
where `path` is whose names are its own name followed by `.regula-refused-`. The directory is listed
through the admitted enumerator (`Regula.Filesystem.Construction.listDirectory`), so a failed read
fails the control instead of hiding an aside. -/
private def asides (path : FilePath) : IO (List FilePath) := do
  let some name := path.fileName | return []
  let entries ← Regula.Filesystem.Construction.listDirectory (path.parent.getD ".")
  return (entries.filter (·.fileName.startsWith s!"{name}.regula-refused-")).toList.map (·.path)

/-- Require that the refused run `output` moved `path` aside whole, and give where it is now:
nothing is at `path`, one new directory is beside it, and the entry is in that directory under its
own name, with each path of `inside` below it and, when `bytes` is given, those bytes in it. -/
private def requireMoved (output : IO.Process.Output) (path : FilePath)
    (inside : List FilePath := []) (bytes : Option ByteArray := none) : IO FilePath := do
  let moved ← match ← asides path, path.fileName with
    | [aside], some name => pure (aside / name)
    | found, _ => throw (IO.userError s!"a refused run did not move {path} into one new directory \
        beside it, but made {found} {shown output}")
  let whole ← inside.allM fun entry => present (moved / entry)
  let same ← match bytes with
    | some before => do
      if ← present moved then pure ((← IO.FS.readBinFile moved).data == before.data)
      else pure false
    | none => pure true
  requireChecks [⟨s!"a refused run did not move {path} aside whole, with its bytes, to {moved} \
    {shown output}", !(← present path) && (← present moved) && whole && same⟩]
  return moved

/-- The issue's reproduction with `regula-standard` at `program`, in the directory `scratch`: a
delayed render writes its saved state and keeps a file that was in its output directory, since a
run that Verso starts does no more than Verso writes. A resumed render renders from the saved state.
Then a refused run with the same options and a word count moves the saved state, the word count
and the output directory aside whole, the files with the bytes that they had, and a resumed render
stops, with no pages, instead of rendering from an earlier state. -/
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
  let stateBytes ← IO.FS.readBinFile state
  let countBytes ← IO.FS.readBinFile count
  let refused ← run website program.toString (delay ++ #["--with-word-count", count.toString])
    refusing
  requireRefused "regula-standard" refused
  discard (requireMoved refused state (bytes := some stateBytes))
  discard (requireMoved refused count (bytes := some countBytes))
  discard (requireMoved refused out ["kept.txt", ("html-multi" : FilePath) / "index.html"])
  let stale ← run website program.toString resume env
  requireChecks [⟨s!"a resumed render of regula-standard after a refused run rendered from an \
    earlier saved state {shown stale}",
    stale.exitCode != 0 && !(← present (pages / "index.html"))⟩]

/-- The refusals of the program `name` at `program`, in the directory `scratch`, without a render:

- a refused delayed render moves its saved state, its word count and its output directory aside
  whole, the files with their bytes, with the pages of a mode that the options do not select
  (`tex`);
- a refused resumed render moves its output directory aside and keeps the saved state that it
  reads outside that directory, which its options name as no destination;
- a word count that is a symbolic link is moved itself, and its target stays;
- a saved state in the output directory moves with it;
- an output directory `.` or an empty one is reported and stays, and the word count is still moved;
- a word count whose new directory would have a name longer than the file system's limit
  (`NAME_MAX`) is reported and stays, whatever the privileges of the process;
- options that Verso's parser refuses move nothing.

Assumes: POSIX.1-2024: `mkdir()` fails with `ENAMETOOLONG` when a component of its path is longer
than `NAME_MAX` (https://pubs.opengroup.org/onlinepubs/9799919799/functions/mkdir.html), whatever
the privileges of the process, and `getconf NAME_MAX DIR` gives that limit for the file system of
`DIR` (https://pubs.opengroup.org/onlinepubs/9799919799/utilities/getconf.html). Lean 4.35.0 maps
`ENAMETOOLONG` to libuv's `UV_ENAMETOOLONG` and gives it as `IO.Error.invalidArgument` with the
path and libuv's message for that code (`src/runtime/io.cpp:195, 256-274`). `IO.Error.toString`
prints that error as `invalid argument (error code: N, name too long)` and a line `  file: PATH`
(`src/Init/System/IOError.lean:256-258, 277`). libuv 1.52.1, which Lean 4.35.0 links
(`lib/libuv.a`), gives the message `name too long` for `UV_ENAMETOOLONG` and for no other code
(`UV_ERRNO_MAP` in `include/uv.h`, https://github.com/libuv/libuv/blob/v1.52.1/include/uv.h). -/
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
  seed state "state"
  seed count "count"
  seed (out / "html-multi" / "index.html")
  seed (out / "tex" / "main.tex")
  let refused ← refuse base #["--output", out.toString, "--delay-html-multi", state.toString,
    "--with-word-count", count.toString]
  discard (requireMoved refused state (bytes := some "state".toUTF8))
  discard (requireMoved refused count (bytes := some "count".toUTF8))
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
  -- A word count whose name is `NAME_MAX` long has a new directory whose name is longer.
  let limit ← run base "getconf" #["NAME_MAX", base.toString]
  let some longest := (limit.stdout.splitOn "\n").head?.bind String.toNat?
    | throw (IO.userError s!"getconf NAME_MAX {base} gave no number {shown limit}")
  let long := base / String.ofList (List.replicate longest 'n')
  seed long "long"
  let refused ← refuse base #["--output", (base / "unmade").toString, "--with-word-count",
    long.toString]
  let made := s!"\n  file: {long}.regula-refused-"
  let derived := match refused.stderr.splitOn made with
    | [_, after] => newSuffix after
    | _ => false
  requireChecks [⟨s!"a refused run of {name} whose word count's new directory would have a name \
    longer than NAME_MAX did not report ENAMETOOLONG at that directory, or moved or changed the \
    word count {shown refused}",
    reports refused s!"{long} was not moved aside: invalid argument (error code: " &&
      reports refused s!", name too long){made}" && derived &&
      (← IO.FS.readFile long) == "long" && (← asides long).isEmpty⟩]
  let out := base / "unparsed"
  seed (out / "index.html")
  let refused ← refuse base #["--output", out.toString, "--unknown-option"]
  requireChecks [⟨s!"a refused run of {name} with options that Verso's parser refuses moved \
    something, or did not report the parser's refusal {shown refused}",
    reports refused "nothing was moved aside: Verso's parser refused the options" &&
      (← present (out / "index.html")) && (← asides out).isEmpty⟩]

/-- The two JSON values of `text`, with white space before and after each, read by Lean's own JSON
parser: `Lean.Json.Parser.anyCore` reads one value and the white space after it. -/
private def twoJsonValues (text : String) : Except String (Lean.Json × Lean.Json) :=
  Std.Internal.Parsec.String.Parser.run (do
    Std.Internal.Parsec.String.ws
    let first ← Lean.Json.Parser.anyCore
    let second ← Lean.Json.Parser.anyCore
    Std.Internal.Parsec.eof
    return (first, second)) text

/-- Build `regula-site` and `regula-standard` in the website package of the repository at `root`
and find their executables with `lake query --json`, then run the issue's reproduction with
`regula-standard` (`reproduction`) and the refusals of both programs (`refusals`), in a fresh
scratch directory. The first failure stops it. It runs after `lake exe site build`, which builds
the website package and generates the sources of `regula-site`.

Assumes: Lake 4.35.0 builds the executable of a `lean_exe` target at `LeanExe.file`, the package's
`binDir` with the executable's file name, and gives that path as the target's result
(`src/lake/Lake/Build/Executable.lean:22-31, 38-40`, `src/lake/Lake/Config/LeanExe.lean:72-73`).
`lake query --json` prints the result of each target that it names in that order, each as a
compact JSON value (`src/lake/Lake/CLI/Main.lean:299, 992-1002`,
`src/lake/Lake/Config/OutFormat.lean:61, 78-81`). A path is a JSON string of its text on Linux and
macOS (`src/Lean/Data/Json/FromToJson/Basic.lean:108-109`,
`src/lake/Lake/Util/FilePath.lean:29-36`), and a compact JSON string escapes a line feed
(`src/Lean/Data/Json/Printer.lean:36-43`), so a path with a line feed in it is read whole. -/
def control (root : FilePath) : IO Unit := do
  let website := root / "website"
  let built ← run website "lake" #["query", "--json", "regula-site", "regula-standard"] cleanEnv
  let found : Except String (FilePath × FilePath) := do
    let (site, standard) ← twoJsonValues built.stdout
    return (← Lean.fromJson? site, ← Lean.fromJson? standard)
  let (site, standard) ← match built.exitCode, found with
    | 0, .ok (site, standard) => pure (website / site, website / standard)
    | _, _ => throw (IO.userError s!"lake query of regula-site and regula-standard did not give \
        their two executables {shown built}")
  let refusing := cleanEnv.push ("LEAN_NUM_THREADS", some "0")
  let _ ← Regula.Scratch.withScratch root "site-renderer-refusal" fun scratch => do
    reproduction website standard scratch cleanEnv refusing
    for (name, program) in [("regula-standard", standard), ("regula-site", site)] do
      refusals program scratch name refusing

end Regula.Site.RendererRefusal
