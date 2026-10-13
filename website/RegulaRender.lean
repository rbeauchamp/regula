import VersoManual
import RegulaRender.Options
import Regula.Filesystem

/-! # The destinations of a refused render (issue 424)

`regula-site` and `regula-standard` render through Verso's `manualMain`, which writes the places
that its options name: the output directory (`--output DIR`), the saved state of a delayed render
(`--delay-html-multi FILE`, `--delay-html-single FILE`) and the word count
(`--with-word-count FILE`). Each program refuses a process without Lean's task manager before
Verso starts (`Regula.TaskManager.guard`). Before issue 424, that refusal left an earlier run's
files in place, and a later reader accepted them: `--resume-html-multi FILE` rendered from an
earlier saved state.

Regula invalidates the destinations of the runs it refuses itself; a run Verso starts keeps Verso's
write behaviour. The refusal (`refuse`) reads the options with Verso's own parser (`versoOptions`),
takes the destinations of that reading (`destinations`), and moves each that is present aside into
a new directory beside it (`invalidate`, `Regula.Filesystem.moveAside`). It removes nothing, and it
moves only the paths that the options name as destinations. A refused run reads nothing, so no file
that a render reads is at stake, except one that the options also name as a destination, which is
moved aside whole. -/

namespace RegulaRender

open System Verso.Genre.Manual

/-- The destinations that a render with `config` writes and that its options name: the output
directory, the saved state of each delayed mode of pages and the word count, in that order.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: a render writes below its output
directory (TeX at 426, single-page HTML at 748, multi-page HTML at 840), `.delay f` writes its saved
state to `f` (1078, through `SavedState.save`, 954-955), and the word count is written to its file
(1053-1056, through `wordCount`, 728). A resumed mode reads its saved state (1080) and writes no
other file outside the output directory. -/
def destinations (config : RenderConfig) : List FilePath :=
  match config.toOutputConfig with
  | ⟨root, _tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let saved : EmitHtml → List FilePath
      | .no | .immediately | .resumeFrom _ => []
      | .delay state => [state]
    root :: saved single ++ saved multi ++ wordCount.toList

/-- The path that the names `names` give, from the root of the filesystem when `absolute` holds and
from the working directory otherwise. -/
def joinNames (absolute : Bool) (names : List String) : FilePath :=
  if absolute then
    if names.isEmpty then ⟨FilePath.pathSeparator.toString⟩
    else ⟨String.join (names.map (FilePath.pathSeparator.toString ++ ·))⟩
  else if names.isEmpty then "." else mkFilePath names

/-- A destination that can be moved aside: the names of the directory where it is, from the root of
the filesystem or from the working directory, and its own name there. -/
structure Destination where
  /-- Whether the names are from the root of the filesystem. -/
  absolute : Bool
  /-- The names of the directory where the destination is. -/
  above : List String
  /-- The name of the destination in that directory: not empty, `.` or `..`. -/
  name : String

/-- The path of a destination. -/
def Destination.path (d : Destination) : FilePath := joinNames d.absolute (d.above ++ [d.name])

/-- The new directory beside a destination into which a refusal moves it, whose name has
`suffix`. -/
def Destination.aside (d : Destination) (suffix : String) : FilePath :=
  joinNames d.absolute (d.above ++ [s!"{d.name}.regula-refused-{suffix}"])

/-- The move of a destination aside, into its new directory with `suffix`, under its own name. -/
def Destination.move (d : Destination) (suffix : String) : Regula.Filesystem.AsideMove :=
  { path := d.path, aside := d.aside suffix, name := d.name }

/-- The destination at `path`, or why it cannot be moved aside: an empty path, or one whose last
component is `.` or `..`, which `rename(2)` does not rename. The empty components of `path` are
dropped, so `out/` names `out`; a symbolic link at `out` is then moved itself. -/
def destination (path : FilePath) : Except String Destination :=
  let names := path.components.filter (!·.isEmpty)
  match names.getLast? with
  | none => .error "it is an empty path"
  | some name =>
    if name == "." || name == ".." then .error "its last component is `.` or `..`"
    else .ok { absolute := path.isAbsolute, above := names.dropLast, name }

/-- The moves of a refusal, for each destination in order with whether something was there when the
refusal reached it and the suffix of its new directory: one move aside for each destination where
something was, and none for the others. -/
def moves (observed : List (Destination × Bool × String)) : List Regula.Filesystem.AsideMove :=
  observed.filterMap fun (d, present, suffix) => if present then some (d.move suffix) else none

/-- The moves of observations in turn are the moves of each in turn: `invalidate` runs the moves
of each destination when it reaches it, so the moves that it runs over all destinations are `moves`
of all its observations in order, to which `moves_operations` applies. -/
theorem moves_append (first later : List (Destination × Bool × String)) :
    moves (first ++ later) = moves first ++ moves later :=
  List.filterMap_append

/-- The operations of a refusal's moves (`Regula.Filesystem.moveAside` runs the operations of each
move, `Regula.Filesystem.AsideMove.operations`): two for each destination where something was, and
each is the making of the new directory beside such a destination or the rename of the destination
into it under its own name. `Regula.Filesystem.AsideOperation` has no removal.

The theorem is about the plan, not about the file system. What the operations do there rests on the
`Assumes:` entry of `Regula.Filesystem.moveAside`: `mkdir(2)` is exclusive, and `rename(2)` is
atomic within one file system and renames a symbolic link at its first path itself. -/
theorem moves_operations (observed : List (Destination × Bool × String)) :
    ((moves observed).flatMap (·.operations)).length =
        2 * (observed.filter fun (_, present, _) => present).length ∧
      ∀ operation ∈ (moves observed).flatMap (·.operations), ∃ d suffix,
        (d, true, suffix) ∈ observed ∧
          (operation = .makeDirectory (d.aside suffix) ∨
            operation = .rename d.path (d.aside suffix / d.name)) := by
  have length : ∀ ms : List Regula.Filesystem.AsideMove,
      (ms.flatMap (·.operations)).length = 2 * ms.length := by
    intro ms
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      simp only [Regula.Filesystem.AsideMove.operations, List.length_cons, List.length_nil]
      omega
  have count : (moves observed).length =
      (observed.filter fun (_, present, _) => present).length := by
    induction observed with
    | nil => rfl
    | cons head more ih =>
      obtain ⟨d, present, suffix⟩ := head
      cases present
      · simp only [moves, List.filterMap_cons, Bool.false_eq_true, ↓reduceIte,
          List.filter_cons] at ih ⊢
        exact ih
      · simp only [moves, List.filterMap_cons, ↓reduceIte, List.filter_cons,
          List.length_cons] at ih ⊢
        rw [ih]
  refine ⟨by rw [length, count], fun operation listed => ?_⟩
  obtain ⟨m, isMove, here⟩ := List.mem_flatMap.mp listed
  obtain ⟨⟨d, present, suffix⟩, mem, made⟩ := List.mem_filterMap.mp isMove
  cases present
  · simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at made
  · simp only [↓reduceIte, Option.some.injEq] at made
    subst made
    simp only [Regula.Filesystem.AsideMove.operations, Destination.move, List.mem_cons,
      List.not_mem_nil, or_false] at here
    exact ⟨d, suffix, mem, here⟩

/-- Whether something is at `path`, by a read that follows no symbolic link there
(`Regula.Filesystem.observeMetadata`): a symbolic link is something, also one whose target is
absent. A failure of the read other than an absent path stops it. -/
def present (path : FilePath) : IO Bool :=
  tryCatch (do discard (Regula.Filesystem.observeMetadata path); pure true) fun
    | .noFileOrDirectory .. => pure false
    | error => throw error

/-- A suffix for the name of a new directory: 16 hexadecimal digits from `IO.getRandomBytes`. The
directory is new because `Regula.Filesystem.moveAside` makes it with `mkdir(2)`, which fails when
anything is there; the suffix only makes that failure unlikely. -/
def freshSuffix : IO String := do
  let digit (byte : UInt8) : String := String.ofList ((Nat.toDigits 16 (byte.toNat + 256)).drop 1)
  return (← IO.getRandomBytes 8).foldl (fun suffix byte => suffix ++ digit byte) ""

/-- Move each destination of `paths` that is present aside (`moves`, `Regula.Filesystem.moveAside`),
in order, and give a line for each: where it moved one, or why it did not. It observes each
destination when it reaches it (`present`), so one below a destination that it moved before is
absent then, and it moves it with the directory above it. A destination that it cannot move, such
as a mount point or an empty path, gives its line, and it goes on with the next. The moves that it
runs are `moves` of its observations in order (`moves_append`), and `Regula.Filesystem.moveAside`
runs the operations of each (`Regula.Filesystem.AsideMove.operations`), so `moves_operations` gives
what it runs, up to the first operation that fails for a destination. -/
def invalidate (paths : List FilePath) : IO (List String) := do
  let mut lines : List String := []
  for path in paths do
    match destination path with
    | .error reason => lines := lines ++ [s!"{path} was not moved aside: {reason}"]
    | .ok d =>
      try
        let here ← present d.path
        for move in moves [(d, here, ← freshSuffix)] do
          Regula.Filesystem.moveAside move
          lines := lines ++ [s!"{d.path} was moved aside to {move.aside / move.name}"]
      catch error => lines := lines ++ [s!"{d.path} was not moved aside: {error}"]
  return lines

/-- The refusal of the program `program`, whose configuration is `config`, in a process without
Lean's task manager (`Regula.TaskManager.guard`): it reads `args` with Verso's own parser
(`versoOptions`) and moves the destinations of that reading aside (`destinations`, `invalidate`),
printing a line for each, and returns 1. When the parser refuses the options, it prints why and
moves nothing: a run with those options writes nothing either, since `manualMain` parses them
before it writes anything.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `manualMain` parses its options with
`opts` (1043) before it writes anything. -/
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
