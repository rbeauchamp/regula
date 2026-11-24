module

public import LeanIntent.Record
public import LeanIntent.Obligations
public import LeanIntent.Progress
public import RegulaSpecification.Language
public import Regula.Effect
public import Regula.Language
public import Regula.Load

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext isTerminalCommand)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

structure Event (L E : Type) where
  op : Op L E
  resp : Resp op

inductive Runs {α : Type} : Prog L E α → List (Event L E) → α → Prop where
  | done (a : α) : Runs (.done a) [] a
  | ask (o : Op L E) (next : Resp o → Prog L E α) (r : Resp o) {t : List (Event L E)} {a : α} :
      Runs (next r) t a → Runs (.ask o next) (⟨o, r⟩ :: t) a

def Event.line? : Event L E → Option String
  | ⟨.println text, _⟩ => some text
  | _ => none

def printed (t : List (Event L E)) : List String :=
  (t.filterMap Event.line?).flatMap fun text => (text.toList.splitOn '\n').map String.ofList

def serialized (t : List (Event L E)) : List Char :=
  (t.filterMap Event.line?).flatMap fun text => (text.push '\n').toList

def Event.acted? : Event L E → Option FilePath
  | ⟨.writeFile p _, _⟩ => some p
  | ⟨.createDirAll p, _⟩ => some p
  | ⟨.removeDirAll p, _⟩ => some p
  | ⟨.runLake _ cwd _, _⟩ => some cwd
  | _ => none

def Event.isBuild : Event L E → Bool
  | ⟨.runLake .., _⟩ => true
  | _ => false

def Event.isImportForRules : Event L E → Bool
  | ⟨.importForRules .., _⟩ => true
  | _ => false

def Event.isOnlySaying : Event L E → Bool
  | ⟨.leanVersion, _⟩ => true
  | ⟨.println _, _⟩ => true
  | ⟨.flush, _⟩ => true
  | _ => false

abbrev parts (p : FilePath) : List String :=
  p.normalize.components.filter fun c => c != "" && c != "."

abbrev inputNameOf (p : FilePath) : String :=
  "/".intercalate (parts p)

def AtOrBelow (dir path : FilePath) : Prop :=
  parts dir <+: parts path

abbrev StrictlyBelow (dir path : FilePath) : Prop :=
  parts dir <+: parts path ∧ parts dir ≠ parts path

abbrev ExactlyBelow (dir path real : FilePath) : Prop :=
  parts real = parts path ∧ AtOrBelow dir path

def under (dir : FilePath) (rel : List String) : FilePath :=
  rel.foldl (fun d p => d.join (FilePath.mk p)) dir

def Event.leaves (e : Event L E) (p : List String) (held : Option String) : Option String :=
  match e.op with
  | .writeFile q text => if parts q = p then some text else held
  | .removeDirAll q => if (parts q).isPrefixOf p then none else held
  | .leanVersion | .getEnv _ | .realPath _ | .readFile _ | .symlinkMetadata _
  | .createDirAll _ | .createTempDir | .println _ | .flush | .parseHeader _ | .parseCommand ..
  | .findOLean .. | .importForRules .. | .importForParser .. | .kernelReplay _ | .parseToml _
  | .lakeInstall _ | .loadWorkspace .. | .loadRoot .. | .libModules _ | .runLake .. => held

def written (t : List (Event L E)) (p : List String) : Option String :=
  t.foldl (fun held e => e.leaves p held) none

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

inductive Parsed (input : InputContext) (env : E) :
    Nat → ModuleParserState → MessageLog → List Syntax → MessageLog → List (Event L E) → Prop where
  | stop {state messages} : Parsed input env 0 state messages [] messages []
  | last {fuel state messages stx state' final} : isTerminalCommand stx = true →
      Parsed input env (fuel + 1) state messages [stx] final
        [⟨.parseCommand input env state messages, (stx, state', final)⟩]
  | next {fuel state messages stx state' messages' rest final events} : isTerminalCommand stx = false →
      Parsed input env fuel state' messages' rest final events →
      Parsed input env (fuel + 1) state messages (stx :: rest) final
        (⟨.parseCommand input env state messages, (stx, state', messages')⟩ :: events)

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

def ReadAs (t : List (Event L E)) (root : Root L) (project tree : FilePath) (f : FileRead) (path : FilePath)
    (imports : Array Import) (mods : List Name) : Prop :=
  ∃ text, ReadText t root project tree f path imports mods text

inductive DefaultModules (t : List (Event L E)) (root : Root L) :
    List Name → List (Name × FilePath) → Prop where
  | nil : DefaultModules t root [] []
  | lib {target lib targets ms modules} : root.findLib target = some lib →
      (⟨.libModules lib, .ok ms⟩ : Event L E) ∈ t → DefaultModules t root targets modules →
      DefaultModules t root (target :: targets) (ms.toList ++ modules)
  | exe {target m targets modules} : root.findLib target = none → root.findExe target = some m →
      DefaultModules t root targets modules → DefaultModules t root (target :: targets) (m :: modules)
  | other {target targets modules} : root.findLib target = none → root.findExe target = none →
      DefaultModules t root targets modules → DefaultModules t root (target :: targets) modules

def HeldByToolchain (t : List (Event L E)) (root : Root L) (n : Name) : Prop :=
  ∃ olean, (⟨.findOLean root.toolchain n, .ok olean⟩ : Event L E) ∈ t

inductive Compiled (headers : List (Name × Array Import)) (root : Root L)
    (modules : List (Name × FilePath)) : Name → FilePath → Prop where
  | root {m path} : (m, path) ∈ modules → Compiled headers root modules m path
  | imported {m path imports n path'} : Compiled headers root modules m path →
      headers.lookup m = some imports → (∃ i ∈ imports, i.module = n) →
      root.resolve n = some path' → Compiled headers root modules n path'
  | resolved {m path path'} : (m, path) ∈ modules → root.resolve m = some path' → Compiled headers root modules m path'

end RegulaSpecification.Effects
