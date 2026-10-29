import VersoManual
import RegulaRender.Options
import Regula.Filesystem

/-! # The destinations of a refused render (issue 424)

`regula-site` and `regula-standard` render through Verso's `manualMain`, which writes the places
that its options name: the output directory (`--output DIR`), the saved state of a delayed render
(`--delay-html-multi FILE`, `--delay-html-single FILE`) and the word count
(`--with-word-count FILE`). Each program refuses a process without Lean's task manager before
Verso starts (`Regula.TaskManager.guard`), and `regula-standard` also refuses a standard that lacks
a section the rule registry cites (`renderStandard`). Before issue 424, a refusal left an earlier
run's files in place, and a later reader accepted them: `--resume-html-multi FILE` rendered from an
earlier saved state.

Regula invalidates the destinations of the runs it refuses itself, the guard's refusals and the
missing-sections refusal; a run Verso starts keeps Verso's write behaviour. The refusal (`refuse`)
reads the options with Verso's own parser (`versoOptions`), takes the destinations of that reading
(`destinations`), and moves each where something is into a new directory beside it (`invalidate`,
`Regula.Filesystem.moveAside`). It removes nothing, it moves only the paths that the options name
as destinations, with what is below them, and the copies that it moves aside stay there: a refusal
after each later run adds one more beside the destination, and the renderers delete none. A refused
run reads nothing, so no file that a render reads is at stake, except one at or below a
destination, which is moved aside with it. -/

namespace RegulaRender

open System Verso.Genre.Manual Regula.Filesystem

/-- The destinations that the command-line options of a render with `config` name: the output
directory, the saved state of each delayed mode of pages and the word count, in that order.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module.

Assumes: Verso `304b8561`, `src/verso-manual/VersoManual.lean`: a render writes below its output
directory (TeX at 428, single-page HTML at 751, multi-page HTML at 843), `.delay f` writes its saved
state to `f` (1081, through `SavedState.save`, 957-958), and the word count is written to its file
(1056-1059, through `wordCount`, 731). A render, a resumed one too, also writes the cache files of
its remote configuration: both emitters call `updateRemotes` (753, 842), which writes them
(`src/multi-verso/MultiVerso.lean`, 670 and 673). This inventory excludes them, since a refused run
starts no Verso and so writes none of them. -/
def destinations (config : RenderConfig) : List FilePath :=
  match config.toOutputConfig with
  | ⟨root, _tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let saved : EmitHtml → List FilePath
      | .no | .immediately | .resumeFrom _ => []
      | .delay state => [state]
    root :: saved single ++ saved multi ++ wordCount.toList

/-- The operations of a refusal. For each destination in order, `Regula.Filesystem.moveAside` takes
its place, observes whether something is there and names a new directory beside it, and runs the
operations of that observation (`Regula.Filesystem.AsidePlace.plan`), up to the first that fails;
`observed` is these observations in order. The operations are two for each destination where
something was, and each is the making of the new directory beside such a destination or the rename
of the destination into it under its own name. Each path is the names of the directories above the
destination followed by one or two names of one entry each (`Regula.Filesystem.EntryName`), so the
new directory is beside the destination and the rename moves the destination into it.
`Regula.Filesystem.AsideOperation` has no removal.

The theorem is about the plan, not about the file system. What the operations do there rests on the
`Assumes:` entry of `Regula.Filesystem.moveAside`: `mkdir(2)` is exclusive, and `rename(2)` is
atomic within one file system and renames a symbolic link at its first path itself. -/
theorem moves_operations (observed : List (AsidePlace × Bool × EntryName)) :
    (observed.flatMap fun (p, present, aside) => p.plan present aside).length =
        2 * (observed.filter fun (_, present, _) => present).length ∧
      ∀ operation ∈ observed.flatMap (fun (p, present, aside) => p.plan present aside),
        ∃ p aside, (p, true, aside) ∈ observed ∧
          (operation = .makeDirectory (namesPath p.absolute (p.above ++ [aside.name])) ∨
            operation = .rename (namesPath p.absolute (p.above ++ [p.name.name]))
              (namesPath p.absolute (p.above ++ [aside.name, p.name.name]))) := by
  constructor
  · induction observed with
    | nil => rfl
    | cons head more ih =>
      obtain ⟨p, present, aside⟩ := head
      rw [List.flatMap_cons, List.length_append, ih]
      cases present
      · simp only [AsidePlace.plan, Bool.false_eq_true, ↓reduceIte, List.length_nil,
          List.filter_cons]
        omega
      · simp only [AsidePlace.plan, ↓reduceIte, List.length_cons, List.length_nil,
          List.filter_cons]
        omega
  · intro operation listed
    obtain ⟨⟨p, present, aside⟩, mem, here⟩ := List.mem_flatMap.mp listed
    cases present
    · simp only [AsidePlace.plan, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at here
    · simp only [AsidePlace.plan, ↓reduceIte, AsidePlace.aside, AsidePlace.path,
        AsidePlace.moved, List.mem_cons, List.not_mem_nil, or_false] at here
      exact ⟨p, aside, mem, here⟩

/-- Move each destination of `paths` where something is aside (`Regula.Filesystem.moveAside`), in
order, and give a line for each that it moved or did not move: where it moved one, or why it did
not. It observes each destination when it reaches it, so one below a destination that it moved
before is absent then, and it moved it with the directory above it. A destination that it cannot
move, such as a mount point or an empty path, gives its line, and it goes on with the next. The
operations that it runs are those of `moves_operations`. -/
def invalidate (paths : List FilePath) : IO (List String) := do
  let mut lines : List String := []
  for path in paths do
    try
      if let some moved ← moveAside path then
        lines := lines ++ [s!"{path} was moved aside to {moved}"]
    catch error => lines := lines ++ [s!"{path} was not moved aside: {error}"]
  return lines

/-- The refusal of the program `program`, whose configuration is `config`, of a run that the
program refuses before Verso starts: the refusal of a process without Lean's task manager by the
guard of `regula-site` and `regula-standard` (`Regula.TaskManager.guard`), and the refusal of a
standard that lacks a cited section by `regula-standard` (`renderStandard`). It reads `args` with
Verso's own parser (`versoOptions`) and moves the destinations of that reading aside
(`destinations`, `invalidate`), printing a line for each, and returns 1. When the parser refuses
the options, it prints why and moves nothing: a run with those options writes nothing either, since
`manualMain` parses them before it writes anything.

Assumes: Verso `304b8561`, `src/verso-manual/VersoManual.lean`: `manualMain` parses its options with
`opts` (1046) before it writes anything. -/
def refuse (program : String) (config : RenderConfig) (args : List String) : IO UInt32 := do
  match ← (versoOptions config args).toBaseIO with
  | .error error =>
    IO.eprintln s!"{program}: nothing was moved aside: Verso's parser refused the options {args}: \
      {error}"
  | .ok config =>
    for line in ← invalidate (destinations config) do
      IO.eprintln s!"{program}: {line}"
  return 1

end RegulaRender
