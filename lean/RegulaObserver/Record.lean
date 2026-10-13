import Lean.Environment
import Lean.Message

/-! # The observer's record of one module's elaboration

The data that Regula's elaboration observer (`RegulaObserver`) writes into the `.olean` of each
module it observes, and the persistent environment extension that carries it. This module only
registers the extension; `RegulaObserver` registers the linters that fill it, so a process that
reads records, such as Regula's checker, imports this module alone and runs no observer.

Lean runs each linter with the environment it had before the linter (`withoutModifyingEnv`,
`Lean/Elab/Command.lean` lines 510 to 516 at Lean 4.34.1), so a linter cannot add an entry to the
module's environment. The extension's state is instead two references that the linters write, and
its `exportEntriesFn` reads them when Lean writes the `.olean`. That function is pure in Lean's
interface (`Lean/Environment.lean` line 1647), so the read is the opaque `readHandles`, which never
blocks: a reference that holds nothing gives a record whose part is absent, and the audit refuses
a module whose record is not complete.

Assumes: in Lean 4.34.1 the command-line frontend writes the `.olean` only after reporting every
snapshot of the module, the tasks of every linter among them (`Lean/Elab/Frontend.lean` lines 334,
and 381 to 385), so a reference holds what a linter wrote when `readHandles` reads it. Code that
runs during the module's own elaboration can write either reference or unregister the linters;
that is an in-process change outside what the record establishes. -/
namespace RegulaObserver
open Lean

/-- How the source set an option: a `set_option` command, the command form `set_option … in`
before one command, the term or tactic form (the `grind` tactic form among them), or an
elaboration whose `set_option` syntax the observer did not find. -/
inductive Form where
  /-- `set_option name value` as a command. -/
  | command
  /-- `set_option name value in` before one command. -/
  | commandIn
  /-- `set_option name value in` inside a term. -/
  | term
  /-- `set_option name value in` inside a tactic block. -/
  | tactic
  /-- `{set_option name value}` in a documentation comment, which sets the option for the rest of
  that comment. -/
  | docComment
  /-- An option set without `set_option` syntax the observer found. -/
  | elaborated
  deriving Inhabited, BEq, Repr

/-- One option that the module's source set, as Lean elaborated it. -/
structure Setting where
  /-- The option, as Lean's `set_option` elaborator named it (`Lean.Elab.OptionInfo`). -/
  name : Name
  /-- The literal value of its `set_option` syntax, or none when the observer found no such syntax
  or its value is not a literal. -/
  value : Option DataValue
  /-- The option's registered default, or none when the running Lean declares no such option. -/
  registeredDefault : Option DataValue
  /-- How the source set it. -/
  form : Form
  /-- For the form before one command, the syntax kind of the command that `set_option … in`
  wraps, through each further `set_option … in`; none for the other forms. -/
  wrapped : Option Name
  /-- Where the option's name is. -/
  position : Position
  deriving Inhabited

/-- A command that drops or replaces the messages of the commands it runs: `#guard_msgs` or
`#guard_panic`, found in a macro expansion or in a command an elaborator ran. -/
structure Guard where
  /-- The syntax kind, `Lean.guardMsgsCmd` or `Lean.guardPanicCmd`. -/
  kind : Name
  /-- Where it is. -/
  position : Position
  deriving Inhabited

/-- A message that Lean keeps out of the command-line output (`isSilent`). -/
structure Silent where
  /-- Its severity. -/
  severity : MessageSeverity
  /-- Where it is. -/
  position : Position
  deriving Inhabited

/-- What the observer's stateful linter folded over the commands it ran on, in source order. -/
structure Fold where
  /-- Where each command before the module's terminal command starts that it ran on, among
  them the commands that `#guard_msgs` and `#guard_panic` run, which Lean also lints. -/
  linted : Array Position
  /-- Every option the source set. -/
  settings : Array Setting
  /-- Every `#guard_msgs` or `#guard_panic` in an expansion or an elaborated command, and every
  top-level `#guard_panic`. -/
  guards : Array Guard
  /-- Every silent message. -/
  silent : Array Silent
  deriving Inhabited

/-- What the observer's module linter read from the commands' syntax at the terminal command. -/
structure Commands where
  /-- Where each command before the terminal command starts. -/
  positions : Array Position
  /-- Where each command is whose syntax contains `#guard_msgs`: Lean runs no linter on such a
  command (`Lean/Elab/Command.lean` line 868). -/
  skipped : Array Position
  deriving Inhabited

/-- The record of one module: each part, or none when its linter did not complete. -/
structure Record where
  /-- The stateful linter's fold. -/
  fold : Option Fold
  /-- The module linter's reading. -/
  commands : Option Commands
  deriving Inhabited

/-- The references the observer's linters write while one module elaborates. -/
structure Handles where
  /-- The stateful linter's fold, written at the terminal command. -/
  fold : IO.Ref (Option Fold)
  /-- The module linter's reading, written at the terminal command. -/
  commands : IO.Ref (Option Commands)

/-- New references holding nothing. -/
def Handles.new : BaseIO Handles := do
  return { fold := ← IO.mkRef none, commands := ← IO.mkRef none }

private unsafe def readHandlesImpl (handles : Handles) : Record :=
  unsafeBaseIO do
    return { fold := ← handles.fold.get, commands := ← handles.commands.get }

/-- What the references hold when Lean writes the module's `.olean`: the module's record. -/
@[implemented_by readHandlesImpl]
opaque readHandles (handles : Handles) : Record

/-- The record of the module being elaborated: one entry, at every `.olean` level, read from the
references when Lean writes the `.olean`; a part is absent when its reference holds nothing, as
when no observer linter ran. -/
initialize records : PersistentEnvExtension Record Unit (Option Handles) ←
  registerPersistentEnvExtension {
    mkInitial := return none
    addImportedFn := fun _ => some <$> Handles.new
    addEntryFn := fun state _ => state
    exportEntriesFnEx := fun _ state =>
      .uniform #[state.elim { fold := none, commands := none } readHandles] }

/-- The record that `env` holds for its module `idx`: its one entry, or none when it holds no entry
or several. -/
def recordOf? (env : Environment) (idx : ModuleIdx) : Option Record :=
  match records.getModuleEntries env idx (level := .private) with
  | #[record] => some record
  | _ => none

end RegulaObserver
