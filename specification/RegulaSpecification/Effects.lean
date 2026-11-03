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

A run is a list of events, each an operation with the response it got ({lit}`Runs`). Each statement here is about
what a run received and what it did with it, for every response, so that none rests on the file system
staying still.
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

/-- {lit}`Runs p t a`: for the responses that the events {lit}`t` hold, the program {lit}`p` asks exactly the operations of
{lit}`t`, in that order, and ends with the value {lit}`a`. -/
inductive Runs {α : Type} : Prog L E α → List (Event L E) → α → Prop where
  /-- A program that has ended asks nothing. -/
  | done (a : α) : Runs (.done a) [] a
  /-- A program that asks {name}`o` and receives {name}`r` goes on as {lean}`next r` does. -/
  | ask (o : Op L E) (next : Resp o → Prog L E α) (r : Resp o) {t : List (Event L E)} {a : α} :
      Runs (next r) t a → Runs (.ask o next) (⟨o, r⟩ :: t) a

/-- The text passed to {name (full := Regula.Effect.Op.println)}`println`, which can contain line separators. -/
def Event.line? : Event L E → Option String
  | ⟨.println text, _⟩ => some text
  | _ => none

/-- The physical lines requested by the run's {name (full := Regula.Effect.Op.println)}`println` calls, in order, splitting each argument at LF.
{name}`IO.println` appends LF ({lit}`Init/System/IO.lean:1276-1277` at v4.35.0), so each call ends its last line.
This is requested output, independent of print success, and excludes output from child processes. -/
def printed (t : List (Event L E)) : List String :=
  (t.filterMap Event.line?).flatMap fun text => (text.toList.splitOn '\n').map String.ofList

/-- The characters requested by the run's {name (full := Regula.Effect.Op.println)}`println` calls, including each terminating LF. Lean's output
operation writes their UTF-8 encoding; buffering, failures and external writers are outside this trace. -/
def serialized (t : List (Event L E)) : List Char :=
  (t.filterMap Event.line?).flatMap fun text => (text.push '\n').toList

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
  | ⟨.importForRules .., _⟩ => true
  | _ => false

/-- An event that makes nothing outside what it prints or what it asks of Lean's constants. -/
def Event.isOnlySaying : Event L E → Bool
  | ⟨.leanVersion, _⟩ => true
  | ⟨.println _, _⟩ => true
  | ⟨.flush, _⟩ => true
  | _ => false

/-- A path by its components: what Lean's {name}`FilePath.normalize` and {name}`FilePath.components` give, with each empty one and each {lit}`.` removed. A
`..` stays. This reads the text of a path, and no file system. -/
abbrev parts (p : FilePath) : List String :=
  p.normalize.components.filter fun c => c != "" && c != "."

/-- The name that the run gives Lean's parser for the file at a path: its components, joined. It labels messages and selects nothing. -/
abbrev inputNameOf (p : FilePath) : String :=
  "/".intercalate (parts p)

/-- {name}`path` lies at or below {name}`dir`, by components. -/
def AtOrBelow (dir path : FilePath) : Prop :=
  parts dir <+: parts path

/-- {name}`path` lies below {name}`dir`, by components, and is not {name}`dir`. -/
abbrev StrictlyBelow (dir path : FilePath) : Prop :=
  parts dir <+: parts path ∧ parts dir ≠ parts path

/-- {name}`real`, the real path that the operating system answered for {name}`path`, has the components of {name}`path`, and {name}`path` lies at or below {name}`dir`. So
{name}`path` crossed no link, by that answer, and holds no `..`. -/
abbrev ExactlyBelow (dir path real : FilePath) : Prop :=
  parts real = parts path ∧ AtOrBelow dir path

/-- The path of the components {name}`rel` below {name}`dir`. -/
def under (dir : FilePath) (rel : List String) : FilePath :=
  rel.foldl (fun d p => d.join (FilePath.mk p)) dir

/-- What this event leaves at the path with the components {name}`p`, given what stood there. A write there puts its text,
whatever its response, because a failed write leaves the file unknown and the text before it no longer stands. A
removal of that path or of a directory above it takes the text away. No other operation is a statement about a file's
text, and the match over the closed type {name}`Op` makes a new operation a new decision. What a trusted call does inside
itself, such as a Lake command, is no event of this function. -/
def Event.leaves (e : Event L E) (p : List String) (held : Option String) : Option String :=
  match e.op with
  | .writeFile q text => if parts q = p then some text else held
  | .removeDirAll q => if (parts q).isPrefixOf p then none else held
  | .leanVersion | .getEnv _ | .realPath _ | .readFile _ | .symlinkMetadata _
  | .createDirAll _ | .createTempDir | .println _ | .flush | .parseHeader _ | .parseCommand ..
  | .findOLean .. | .importForRules .. | .importForParser .. | .kernelReplay _ | .parseToml _
  | .lakeInstall _ | .loadWorkspace .. | .loadRoot .. | .libModules _ | .runLake .. => held

/-- What the acts of {name}`t` leave at the path with the components {name}`p`, from a tree that held nothing there: the
text of its last write, unless a later removal took it away. This is a function of the run's requests alone:
it observes no file system and says nothing about another process. -/
def written (t : List (Event L E)) (p : List String) : Option String :=
  t.foldl (fun held e => e.leaves p held) none

/-- A failed answer. An environment variable that is not set, an error of an operation that can fail, a load of Lake that
gives no workspace and a Lake command that does not end with 0 are failures. A name that is absent, for the one name the
reader tests that way, is no failure, because absence is what it asks about. A failed print, flush or removal is none
either, because no verdict rests on it. Whether a failure justifies a result is what {lit}`Reason` and the reasons of a load
state, which bind it to the requested build. -/
def Event.failed : Event L E → Prop
  | ⟨.getEnv _, r⟩ => r = (none : Option String)
  | ⟨.realPath _, r⟩ | ⟨.findOLean .., r⟩ | ⟨.createTempDir, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error FilePath)
  | ⟨.readFile _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error String)
  | ⟨.writeFile .., r⟩ | ⟨.createDirAll _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error Unit)
  | ⟨.parseHeader _, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error (Syntax × ModuleParserState × MessageLog × Array Import))
  | ⟨.importForParser .., r⟩ => ∃ e, r = (Except.error e : Except IO.Error (E × List Name))
  | ⟨.importForRules .., r⟩ => ∃ e, r = (Except.error e : Except IO.Error Environment)
  | ⟨.kernelReplay _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error Unit)
  | ⟨.parseToml _, r⟩ => ∃ e, r = (Except.error e : Except MessageLog Lake.Toml.Table)
  | ⟨.libModules _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error (Array (Name × FilePath)))
  | ⟨.loadWorkspace .., r⟩ | ⟨.loadRoot .., r⟩ =>
    (∃ e, r = (Except.error e : Except String (Option (Root L) × List String))) ∨
      ∃ log, r = (Except.ok (none, log) : Except String (Option (Root L) × List String))
  | ⟨.symlinkMetadata _, r⟩ =>
    ∃ e, r = (Except.error e : Except IO.Error IO.FS.Metadata) ∧
      ∀ name code details, e ≠ .noFileOrDirectory name code details
  | ⟨.runLake .., r⟩ => r ≠ (Except.ok 0 : Except IO.Error UInt32)
  | _ => False

/-- Lean's parser read the commands {lit}`commands` of the input {name}`input` in order from the state {lit}`state` and the
log {lit}`messages`, up to the log {lit}`final`: one event for each, each started from where the last ended. {lit}`fuel` bounds the
calls, which one more than the bytes of a file does not run out of: {lit}`stop` is a parse that took them all and stopped
short of the parser's end of input, which {name}`ReadToEnd` then refuses. -/
inductive Parsed (input : InputContext) (env : E) :
    Nat → ModuleParserState → MessageLog → List Syntax → MessageLog → List (Event L E) → Prop where
  /-- The reader took as many commands as {lit}`fuel` allows, and stopped here. -/
  | stop {state messages} : Parsed input env 0 state messages [] messages []
  /-- The parser's end of input. -/
  | last {fuel state messages stx state' final} : isTerminalCommand stx = true →
      Parsed input env (fuel + 1) state messages [stx] final
        [⟨.parseCommand input env state messages, (stx, state', final)⟩]
  /-- One command and then the rest. -/
  | next {fuel state messages stx state' messages' rest final events} : isTerminalCommand stx = false →
      Parsed input env fuel state' messages' rest final events →
      Parsed input env (fuel + 1) state messages (stx :: rest) final
        (⟨.parseCommand input env state messages, (stx, state', messages')⟩ :: events)

/-- {name}`f` is what the run judged of the text {name}`text` of one file: the project's file {lit}`under project rel` passed the
exact-path test on its real path, {name}`text` is what {name (full := Regula.Effect.Op.readFile)}`readFile` returned, and Lean's parser gave the header and
commands of {name}`f` from that same text, in an environment that an import on the toolchain's library of {name}`root`
gave together with the scoped parsers {name}`f` states. This says what was read and parsed, and nothing of what
the tree holds: {lit}`Evidence` says that, through what it is given as held. -/
def ReadText (t : List (Event L E)) (root : Root L) (project tree : FilePath) (f : FileRead) (path : FilePath)
    (imports : Array Import) (mods : List Name) (text : String) : Prop :=
  ∃ (rel : List String) (real : FilePath) (state : ModuleParserState)
    (messages final : MessageLog) (env : E) (commands : List (Event L E)),
    TreeRelative (parts tree) (parts path) rel ∧
    parts real = parts (under project rel) ∧ parts project <+: parts (under project rel) ∧
    ([⟨.realPath (under project rel), .ok real⟩, ⟨.readFile (under project rel), .ok text⟩,
      ⟨.parseHeader (mkInputContext text (inputNameOf path)), .ok (f.header, state, messages, imports)⟩] :
        List (Event L E)).Sublist t ∧
    (⟨.importForParser root.toolchain mods, .ok (env, f.scopedParsers)⟩ : Event L E) ∈ t ∧
    Parsed (mkInputContext text (inputNameOf path)) env ((mkInputContext text (inputNameOf path)).inputString.utf8ByteSize + 1)
      state messages f.commands final commands ∧
    commands.Sublist t ∧
    f.parsed = !final.hasErrors

/-- {name}`f` is what the run judged of some text of one file. -/
def ReadAs (t : List (Event L E)) (root : Root L) (project tree : FilePath) (f : FileRead) (path : FilePath)
    (imports : Array Import) (mods : List Name) : Prop :=
  ∃ text, ReadText t root project tree f path imports mods text

/-- {lit}`modules` are the modules of the default targets of {name}`root`, as this run's responses list them: each module
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

/-- {name}`n` is the toolchain's own module by this run's responses: Lean's search, on the toolchain's library that the load {name}`root` names, found its {lit}`.olean`. -/
def HeldByToolchain (t : List (Event L E)) (root : Root L) (n : Name) : Prop :=
  ∃ olean, (⟨.findOLean root.toolchain n, .ok olean⟩ : Event L E) ∈ t

/-- What Lake compiles for the claim: the modules of the default targets with their files, each module
that the imports of what it compiles reach and that Lake's resolution of an import gives a file for, and the file
that resolution gives for the name of a module of a default target. {name}`headers` gives the imports of each module. That this is what Lake's build does is the hypothesis {lit}`LakeBehaviour`. -/
inductive Compiled (headers : List (Name × Array Import)) (root : Root L)
    (modules : List (Name × FilePath)) : Name → FilePath → Prop where
  /-- A module of a default target. -/
  | root {m path} : (m, path) ∈ modules → Compiled headers root modules m path
  /-- A module an import reaches. -/
  | imported {m path imports n path'} : Compiled headers root modules m path →
      headers.lookup m = some imports → (∃ i ∈ imports, i.module = n) →
      root.resolve n = some path' → Compiled headers root modules n path'
  /-- The file that Lake's resolution gives for a module of a default target, which a later spelling can name. -/
  | resolved {m path path'} : (m, path) ∈ modules → root.resolve m = some path' → Compiled headers root modules m path'

end RegulaSpecification.Effects
