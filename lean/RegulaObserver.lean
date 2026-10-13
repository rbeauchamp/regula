import Lean.Elab.Command
import RegulaObserver.Record

/-! # Regula's elaboration observer

A Lean plugin that records, for each module it elaborates, what the module's commands did that a
build's messages do not show: the options the source set, the `#guard_msgs` and `#guard_panic`
commands that drop or replace messages, and the messages Lean keeps out of its command-line output.
It decides nothing: Regula's audit reads the record from the module's `.olean`
(`RegulaObserver.records`) and decides RG2003 and RG2006 from it. It imports only Lean, since Lean
loads a plugin's shared library alone, without the libraries of its imports.

Lake loads it into the elaboration of each module of the root package through the `presetup`
facet that Regula's `lakefile.lean` declares, and Regula's audit builds load it the same way
(`Regula.Checker.Observer.observerPresetup`). Loading the plugin runs this module's initializers,
which register the two linters below (`Lean/LoadDynlib.lean` lines 95 to 118).

- The stateful linter folds each command's observations in source order: Lean chains its runs
  through the previous command's state, so its run at the terminal command follows every earlier
  run (`Lean/Elab/Command.lean` lines 556 to 597). That run writes the fold.
- The module linter runs at the terminal command with the syntax of every earlier command
  (`Lean/Elab/Command.lean` lines 513 and 514) and writes their count and where each command is
  that contains `#guard_msgs`, on which Lean runs no linter (line 868).

Assumes: in Lean 4.34.1 Lean runs both linters on every command whose syntax contains no
`#guard_msgs`, the terminal command included, whatever the options and errors
(`Lean/Elab/Command.lean` lines 338 to 368 and 865 to 871), with the command's complete info trees
(lines 520 to 545 and 567 to 597). The stateful linter reads the command's messages, silent ones
included, as its own post runs: those of the command's elaboration, of the ordinary linters, whose
task the stateful linters wait for (lines 541 and 563 to 566), and of each stateful linter's pre
and of the posts that run before its own (lines 416 to 425). Lean loads the plugin before it runs
the initializers of the module's imports (`Lean/Environment.lean` line 2446), so a stateful linter
that imported code registers runs its post after the observer's (`Lean/Elab/Command.lean` lines 190
to 192), and Lean starts the next command with no messages (`Lean/Language/Lean.lean` line 760).
Lean gives a plugin no later point at which it can read a command's messages. A message that such a
linter logs is outside the record: that linter is code that runs inside the audited elaboration,
like a trusted plugin.

Each `set_option` form records the option's name in the info tree (`Lean/Elab/SetOption.lean` line
65), and the record holds the options set through `Lean.Elab.elabSetOption` (`setOptionKinds`).
An option that elaborator code changes directly is outside the record: a temporary change for
the code's own commands through `withScope`, such as `autoImplicit` in the `ToExpr` deriving
handler (`Lean/Elab/Deriving/ToExpr.lean` line 228), `warn.exposeOnPrivate` in every deriving
handler (`Lean/Elab/Deriving/Basic.lean` lines 294 to 297) and
`quotPrecheck.allowSectionVars` in a `local notation` (`Lean/Elab/Notation.lean` lines 154 to
157). Of Lean's builtin commands, only `set_option` and `unlock_limits` assign the options of the
enclosing scope for the commands after them (`modifyScope`, `Lean/Elab/BuiltinCommand.lean` lines
520 and 527). `unlock_limits` sets `maxHeartbeats`, `maxRecDepth` and
`synthInstance.maxHeartbeats` to `0`, which RG2006 accepts
(`RegulaPolicy.Community.unlockLimits_accepted`), so the observer does not record it. -/

namespace RegulaObserver
open Lean Elab Command

/-- The syntax kinds of the commands that drop or replace the messages of the commands they run. -/
def guardKinds : Array Name := #[``Lean.guardMsgsCmd, ``Lean.guardPanicCmd]

/-- The syntax kinds whose elaborators call `Lean.Elab.elabSetOption` with their second and fourth
arguments as the option's name and value: the command, term, tactic and `grind` tactic forms of
`set_option` (`Lean/Elab/BuiltinCommand.lean` line 517, `Lean/Elab/BuiltinTerm.lean` line 416,
`Lean/Elab/Tactic/BuiltinTactic.lean` line 217, `Lean/Elab/Tactic/Grind/BuiltinTactic.lean` line
524). The linters that also call it (`Lean/Linter/Basic.lean` line 45,
`Lean/Linter/MissingDocs.lean` line 321) record no information node, and repeat a `set_option` of
the source. -/
def setOptionKinds : Array Name :=
  #[``Lean.Parser.Command.set_option, ``Lean.Parser.Term.set_option,
    ``Lean.Parser.Tactic.set_option, ``Lean.Parser.Tactic.Grind.setOption]

/-- The value Lean's `set_option` elaborator establishes from `value`: a string or numeral literal,
or the atom `true` or `false` (`Lean.Elab.elabSetOption`, `Lean/Elab/SetOption.lean` lines 74 to
83, which refuses any other syntax), or none for any other syntax. Lean records the option's name
in the info tree (`Lean.Elab.OptionInfo`, `Lean/Elab/InfoTree/Types.lean` lines 120 to 123) but
not the value, and the elaborator returns the value only to its caller, so the observer decodes
the same syntax the same way. -/
def literal (value : Syntax) : Option DataValue :=
  match value.isStrLit?, value.isNatLit?, value with
  | some s, _, _ => some (.ofString s)
  | none, some n, _ => some (.ofNat n)
  | none, none, .atom _ "true" => some (.ofBool true)
  | none, none, .atom _ "false" => some (.ofBool false)
  | _, _, _ => none

/-- The position of `stx` in the module's file, or the start of the file when it has none. -/
def positionOf (fileMap : FileMap) (stx : Syntax) : Position :=
  fileMap.toPosition ((stx.getPos? (canonicalOnly := false)).getD 0)

/-- Whether `a` and `b` are the same occurrence: the same syntax (`Syntax.structEq`, which ignores
source information, `Init/Meta/Defs.lean` line 520) at the same start and end position. -/
def sameOccurrence (a b : Syntax) : Bool :=
  a.structEq b && a.getPos? (canonicalOnly := false) == b.getPos? (canonicalOnly := false) &&
    a.getTailPos? (canonicalOnly := false) == b.getTailPos? (canonicalOnly := false)

/-- Whether `stx` contains the occurrence `id` (`sameOccurrence`). -/
def mentions (stx id : Syntax) : Bool :=
  (stx.find? (sameOccurrence · id)).isSome

/-- The `set_option` syntax that wrote the occurrence `id` of an option name: the first node of a
kind in `setOptionKinds` whose second argument is `id`, in the syntax of the innermost of the
nodes `ancestors` above it that contains one. -/
def setterOf (id : Syntax) (ancestors : List Syntax) : Option Syntax :=
  ancestors.findSome? fun stx =>
    stx.find? fun n => setOptionKinds.contains n.getKind && sameOccurrence n[1] id

/-- The command that the command form `set_option … in cmd` wraps: `cmd`, through each further
`set_option … in` that `cmd` is. -/
partial def wrappedCommand (cmd : Syntax) : Syntax :=
  if cmd.isOfKind ``Lean.Parser.Command.in && cmd[0].isOfKind ``Lean.Parser.Command.set_option then
    wrappedCommand cmd[2]
  else cmd

/-- The form of the `set_option` syntax `setter`, with `ancestors` the syntax of the nodes above
it, and for the command form before one command the syntax kind of the command it wraps
(`wrappedCommand`). The command form is `commandIn` when an ancestor is `cmd in cmd` whose first
command is `setter`; the `grind` tactic form is a tactic form. -/
def formOf (setter : Option Syntax) (ancestors : List Syntax) : Form × Option Name :=
  match setter with
  | none => (.elaborated, none)
  | some setter =>
    if setter.isOfKind ``Lean.Parser.Command.set_option then
      match ancestors.find? fun a => a.isOfKind ``Lean.Parser.Command.in &&
          sameOccurrence a[0] setter with
      | some a => (.commandIn, some (wrappedCommand a[2]).getKind)
      | none => (.command, none)
    else if setter.isOfKind ``Lean.Parser.Term.set_option then (.term, none)
    else (.tactic, none)

/-- An option name the `set_option` elaborator recorded, with what the walk knew above it. -/
structure Found where
  /-- The recorded name. -/
  info : OptionInfo
  /-- The elaborators and syntax of the nodes above it, innermost first. -/
  ancestors : List (Name × Syntax)

/-- What one walk of a command's info trees collects. -/
structure Walk where
  /-- Each option name the `set_option` elaborator recorded. -/
  options : Array Found := #[]
  /-- Each command elaborated as `#guard_msgs` or `#guard_panic`. -/
  guards : Array Syntax := #[]

/-- Walk an info tree, with `ancestors` the elaborator and syntax of each command, tactic and term
node above, innermost first. -/
partial def walk (ancestors : List (Name × Syntax)) (acc : Walk) : InfoTree → Walk
  | .context _ tree => walk ancestors acc tree
  | .hole _ => acc
  | .node info children =>
    let acc := match info with
      | .ofCommandInfo i => if guardKinds.contains i.stx.getKind then
          { acc with guards := acc.guards.push i.stx } else acc
      | .ofOptionInfo i => { acc with options := acc.options.push { info := i, ancestors } }
      | _ => acc
    let ancestors := match info with
      | .ofCommandInfo i => (i.elaborator, i.stx) :: ancestors
      | other => match other.toElabInfo? with
        | some i => (i.elaborator, i.stx) :: ancestors
        | none => ancestors
    children.foldl (walk ancestors) acc

/-- The setting that `found` records: its value and form from its `set_option` syntax
(`setterOf`), and, when its name is not in the module's source text, its origin, the innermost
node above whose syntax does not contain the name, the macro that wrote it, with `builtins` the
builtin declarations of the running Lean (`Lean.builtinDeclRanges`). -/
def settingOf (env : Environment) (decls : OptionDecls) (builtins : NameMap DeclarationRanges)
    (fileMap : FileMap) (found : Found) : Setting :=
  let id := found.info.stx
  let source := id.getHeadInfo matches .original ..
  let origin := if source then none else
    (found.ancestors.find? fun (_, stx) => !mentions stx id).map fun (declaration, _) =>
      { declaration
        «module» := ((env.getModuleIdxFor? declaration).bind fun idx =>
            env.header.moduleNames[idx.toNat]?).getD
          (if env.contains declaration then env.mainModule else .anonymous)
        builtin := !env.contains declaration && builtins.contains declaration : Origin }
  let syntaxes := found.ancestors.map (·.2)
  let setter := setterOf id syntaxes
  let (form, wrapped) := formOf setter syntaxes
  { name := found.info.optionName
    value := setter.bind fun setter => literal setter[3]
    registeredDefault := (decls.find? found.info.optionName).map (·.defValue)
    form, wrapped, origin
    position := positionOf fileMap id }

/-- The observations of the command `stx`, appended to `fold`. -/
def observe (stx : Syntax) (fold : Fold) : CommandElabM Fold := do
  let fileMap ← getFileMap
  let env ← getEnv
  let decls ← getOptionDecls
  let mut acc : Walk := {}
  for tree in (← getInfoTrees) do
    acc := walk [(.anonymous, stx)] acc tree
  let builtins ← builtinDeclRanges.get
  let settings := acc.options.map (settingOf env decls builtins fileMap)
  let mut fold := { fold with settings := fold.settings ++ settings }
  for guard in acc.guards do
    let observed : Guard := { kind := guard.getKind, position := positionOf fileMap guard }
    fold := { fold with guards := fold.guards.push observed }
  for message in (← get).messages.reportedPlusUnreported do
    if message.isSilent then
      let observed : Silent := { severity := message.severity, position := message.pos }
      fold := { fold with silent := fold.silent.push observed }
  return fold

/-- The stateful linter: fold each command's observations, and at the terminal command write the
fold to the module's record. -/
def foldCommand (stx : Syntax) (prev : Fold) : CommandElabM Fold := do
  let terminal := Parser.isTerminalCommand stx
  let fileMap ← getFileMap
  let fold ← observe stx
    (if terminal then prev else { prev with linted := prev.linted.push (positionOf fileMap stx) })
  if terminal then
    if let some handles := records.getState (← getEnv) then
      handles.fold.set (some fold)
  return fold

/-- The module linter: write where each command before the terminal one starts, and where each is
that contains `#guard_msgs`, to the module's record. -/
def readCommands (cmds : Array Syntax) : CommandElabM Unit := do
  let fileMap ← getFileMap
  let skipped := cmds.filterMap fun cmd =>
    (cmd.find? (·.isOfKind ``Lean.guardMsgsCmd)).map fun _ => positionOf fileMap cmd
  if let some handles := records.getState (← getEnv) then
    handles.commands.set (some { positions := cmds.map (positionOf fileMap), skipped })

initialize
  discard <| registerStatefulLinter (σ := Fold) (τ := Unit)
    (init := { linted := #[], settings := #[], guards := #[], silent := #[] })
    (post := fun stx prev _ _ _ => foldCommand stx prev)
  addModuleLinter { name := `RegulaObserver.readCommands, run := readCommands }

end RegulaObserver
