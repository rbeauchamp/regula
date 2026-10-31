/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import LeanIntent.Record
import LeanIntent.Obligations
import LeanIntent.Progress
import RegulaSpecification.Language
import Regula.Effect
import Regula.Language
import Regula.Load

/-!
# What a run of the checker does

What the checker's program must do with whatever Lean, Lake and the operating system answer. It imports the
closed type of the operations, the pure loader and the pure decision, and none of the code that asks the
operations (`Regula.Reader`, `Regula.Shell`).

A run is a list of events, each an operation with the response it got (`Runs`). Each statement here is about
what a run received and what it did with it, for every response, so that none rests on the file system staying
still. `RegulaSpecification.Proofs.Effects` proves them of the program the `lint` executable runs, and that the
executable's interpretation of that program is such a run.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext isTerminalCommand)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-- One operation that a run asked, with the response it received. -/
structure Event (L E : Type) where
  /-- The operation. -/
  op : Op L E
  /-- Its response. -/
  resp : Resp op

/-- `Runs p t a`: for the responses that the events `t` hold, the program `p` asks exactly the operations of
`t`, in that order, and ends with the value `a`. A response is any value of its type, so this quantifies over
everything the external functions can give, a failure included. -/
inductive Runs {α : Type} : Prog L E α → List (Event L E) → α → Prop where
  /-- A program that has ended asks nothing. -/
  | done (a : α) : Runs (.done a) [] a
  /-- A program that asks `o` and receives `r` goes on as `next r` does. -/
  | ask (o : Op L E) (next : Resp o → Prog L E α) (r : Resp o) {t : List (Event L E)} {a : α} :
      Runs (next r) t a → Runs (.ask o next) (⟨o, r⟩ :: t) a

/-! ## Reading a run -/

/-- The text of a line that an event printed. -/
def Event.line? : Event L E → Option String
  | ⟨.println text, _⟩ => some text
  | _ => none

/-- The lines that a run printed, in order. Whether a print succeeded does not matter here: this is what the
run asked to print. -/
def printed (t : List (Event L E)) : List String :=
  t.filterMap Event.line?

/-- The events of a run that change a file or a directory, or that run a command, each with the directory
they act in or on. -/
def Event.acted? : Event L E → Option FilePath
  | ⟨.writeFile p _, _⟩ => some p
  | ⟨.createDirAll p, _⟩ => some p
  | ⟨.removeDirAll p, _⟩ => some p
  | ⟨.runLake _ cwd _, _⟩ => some cwd
  | _ => none

/-- A build of the checker's tree: the Lake command with these arguments. -/
def Event.isBuild : Event L E → Bool
  | ⟨.runLake .., _⟩ => true
  | _ => false

/-- Whether an event loads a finished build for the rules. -/
def Event.isImportForRules : Event L E → Bool
  | ⟨.importForRules _, _⟩ => true
  | _ => false

/-- An event that makes nothing outside what it prints or what it asks of Lean's constants. -/
def Event.isOnlySaying : Event L E → Bool
  | ⟨.leanVersion, _⟩ => true
  | ⟨.println _, _⟩ => true
  | ⟨.flush, _⟩ => true
  | _ => false

/-- A path by its components, with `.` removed. -/
abbrev parts (p : FilePath) : List String :=
  Regula.Load.exactParts p

/-- `path` lies at or below `dir`, by components. -/
def AtOrBelow (dir path : FilePath) : Prop :=
  parts dir <+: parts path

/-- The path of the components `rel` below `dir`. -/
def under (dir : FilePath) (rel : List String) : FilePath :=
  rel.foldl (fun d p => d.join (FilePath.mk p)) dir

/-! ## What a read is -/

/-- A failed answer to what the reader asks. A name that is absent, for the one name the reader tests that
way, is no failure, because absence is what it asks about. -/
def Event.failedRead : Event L E → Prop
  | ⟨.appPath, r⟩ | ⟨.realPath _, r⟩ | ⟨.findOLean _, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error FilePath)
  | ⟨.readFile _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error String)
  | ⟨.writeFile .., r⟩ | ⟨.createDirAll _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error Unit)
  | ⟨.parseHeader _, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error (Syntax × ModuleParserState × MessageLog × Array Import))
  | ⟨.importForParser _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error (E × List Name))
  | ⟨.parseToml _, r⟩ => ∃ e, r = (Except.error e : Except MessageLog Lake.Toml.Table)
  | ⟨.libModules _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error (Array (Name × FilePath)))
  | ⟨.loadRoot .., r⟩ =>
    (∃ e, r = (Except.error e : Except String (Option (Root L) × List String))) ∨
      ∃ log, r = (Except.ok (none, log) : Except String (Option (Root L) × List String))
  | ⟨.symlinkMetadata _, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error IO.FS.Metadata) ∧
      ∀ name code details, e ≠ .noFileOrDirectory name code details
  | _ => False

/-- Lean's parser read the commands `commands` of the input `input` in order from the state `state` and the
log `messages`, up to the log `final`: one event for each, each started from where the last ended. `stop` is a
parse that stopped short of the parser's end of input, which `ReadToEnd` then refuses. -/
inductive Parsed (input : InputContext) (env : E) :
    ModuleParserState → MessageLog → List Syntax → MessageLog → List (Event L E) → Prop where
  /-- The reader stopped here. -/
  | stop {state messages} : Parsed input env state messages [] messages []
  /-- The parser's end of input. -/
  | last {state messages stx state' final} : isTerminalCommand stx = true →
      Parsed input env state messages [stx] final
        [⟨.parseCommand input env state messages, (stx, state', final)⟩]
  /-- One command and then the rest. -/
  | next {state messages stx state' messages' rest final events} : isTerminalCommand stx = false →
      Parsed input env state' messages' rest final events →
      Parsed input env state messages (stx :: rest) final
        (⟨.parseCommand input env state messages, (stx, state', messages')⟩ :: events)

/-- `f` is what the run read of one file: the project's file `under project rel` passed the exact-path test
on its real path, its text is what `readFile` returned, that same text was written to `path`, the same
relative path in the tree, and Lean's parser gave the header and commands of `f` from that same text, in an
environment that an import gave together with the scoped parsers `f` states. `imports` is what that header
states, and `mods` is what the import was asked to load. So the text the decision judged is the text placed
in the tree. -/
def ReadAs (t : List (Event L E)) (project tree : FilePath) (f : FileRead) (path : FilePath)
    (imports : Array Import) (mods : List Name) : Prop :=
  ∃ (rel : List String) (real : FilePath) (text : String) (state : ModuleParserState)
    (messages final : MessageLog) (env : E) (commands : List (Event L E)),
    TreeRelative (parts tree) (parts path) rel ∧
    parts real = parts (under project rel) ∧ parts project <+: parts (under project rel) ∧
    ([⟨.realPath (under project rel), .ok real⟩, ⟨.readFile (under project rel), .ok text⟩,
      ⟨.writeFile path text, .ok ()⟩,
      ⟨.parseHeader (mkInputContext text path.toString), .ok (f.header, state, messages, imports)⟩] :
        List (Event L E)).Sublist t ∧
    (⟨.importForParser mods, .ok (env, f.scopedParsers)⟩ : Event L E) ∈ t ∧
    Parsed (mkInputContext text path.toString) env state messages f.commands final commands ∧
    commands.Sublist t ∧
    f.parsed = !final.hasErrors

/-- `modules` are the modules of the default targets of `root`, as this run's responses list them: each module
of a default library, and the root of each default executable, in the order of the targets. -/
inductive DefaultModules (t : List (Event L E)) (root : Root L) :
    List Name → List (Name × FilePath) → Prop where
  /-- No more targets. -/
  | nil : DefaultModules t root [] []
  /-- A default library: what Lake listed for it. -/
  | lib {target lib targets ms modules} : root.findLib target = some lib →
      (⟨.libModules lib, .ok ms⟩ : Event L E) ∈ t → DefaultModules t root targets modules →
      DefaultModules t root (target :: targets) (ms.toList ++ modules)
  /-- A default executable: its root. -/
  | exe {target m targets modules} : root.findLib target = none → root.findExe target = some m →
      DefaultModules t root targets modules → DefaultModules t root (target :: targets) (m :: modules)
  /-- A default target that is neither builds no Lean module. -/
  | other {target targets modules} : root.findLib target = none → root.findExe target = none →
      DefaultModules t root targets modules → DefaultModules t root (target :: targets) modules

/-- `n` is the toolchain's own module by this run's responses: Lean's search found its `.olean`, whose real
path lies below the real path of a directory of the toolchain's library. -/
def HeldByToolchain (t : List (Event L E)) (root : Root L) (n : Name) : Prop :=
  ∃ olean real dir dirReal,
    ([⟨.findOLean n, .ok olean⟩, ⟨.realPath olean, .ok real⟩] : List (Event L E)).Sublist t ∧
    dir ∈ root.toolchain ∧ (⟨.realPath dir, .ok dirReal⟩ : Event L E) ∈ t ∧
    Regula.Load.below dirReal real = true

/-- What Lake compiles for the claim: the modules of the default targets with their files, and each module
that the imports of what it compiles reach and that Lake's resolution of an import gives a file for. `headers`
gives the imports of each module. That this is what Lake's build does is the hypothesis `LakeBehaviour`. -/
inductive Compiled (headers : List (Name × Array Import)) (root : Root L)
    (modules : List (Name × FilePath)) : Name → FilePath → Prop where
  /-- A module of a default target. -/
  | root {m path} : (m, path) ∈ modules → Compiled headers root modules m path
  /-- A module an import reaches. -/
  | imported {m path imports n path'} : Compiled headers root modules m path →
      headers.lookup m = some imports → (∃ i ∈ imports, i.module = n) →
      root.resolve n = some path' → Compiled headers root modules n path'

end RegulaSpecification.Effects
