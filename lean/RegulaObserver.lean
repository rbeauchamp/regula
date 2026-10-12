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
(`Regula.Checker.Lake.observerPresetup`). Loading the plugin runs this module's initializers,
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
and messages, silent ones included (lines 520 to 545 and 567 to 597). Each `set_option` form
records the option's name in the info tree (`Lean/Elab/SetOption.lean` line 65). -/
namespace RegulaObserver
open Lean Elab Command

/-- The syntax kinds of the commands that drop or replace the messages of the commands they run. -/
def guardKinds : Array Name := #[``Lean.guardMsgsCmd, ``Lean.guardPanicCmd]

/-- The value Lean's `set_option` elaborator reads from `value`: a string, numeral or Boolean
literal (`Lean.Elab.elabSetOption`, which each `set_option` elaborator gives its fourth argument), or none for any other syntax. -/
partial def literal (value : Syntax) : Option DataValue :=
  match value.isStrLit?, value.isNatLit?, value with
  | some s, _, _ => some (.ofString s)
  | none, some n, _ => some (.ofNat n)
  | none, none, .atom _ "true" => some (.ofBool true)
  | none, none, .atom _ "false" => some (.ofBool false)
  | none, none, .node _ _ #[inner] => literal inner
  | _, _, _ => none

/-- The position of `stx` in the module's file, or the start of the file when it has none. -/
def positionOf (fileMap : FileMap) (stx : Syntax) : Position :=
  fileMap.toPosition ((stx.getPos? (canonicalOnly := false)).getD 0)

/-- Whether `stx` contains `id`, the same syntax with the same source information. -/
def mentions (stx id : Syntax) : Bool :=
  (stx.find? (·.structEq id)).isSome

/-- The form of the `set_option` syntax `setter` that wrote the option name `id`, with `ancestors`
the syntax of the nodes above it, innermost first: the command form is `commandIn` when an
ancestor is `cmd in cmd` whose first command is a `set_option` of `id`. -/
def formOf (setter id : Syntax) (ancestors : List Syntax) : Form :=
  if setter.isOfKind ``Lean.Parser.Command.set_option then
    if ancestors.any fun a => a.isOfKind ``Lean.Parser.Command.in &&
        a[0].isOfKind ``Lean.Parser.Command.set_option && a[0][1].structEq id then .commandIn
    else .command
  else if setter.isOfKind ``Lean.Parser.Term.set_option then .term
  else if setter.isOfKind ``Lean.Parser.Tactic.set_option then .tactic
  else .elaborated

/-- An option name the `set_option` elaborator recorded, with what the walk knew above it. -/
structure Found where
  /-- The recorded name. -/
  info : OptionInfo
  /-- The syntax of the elaborator node directly above it, the `set_option` that wrote it. -/
  setter : Syntax
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
      | .ofOptionInfo i =>
        let setter := (ancestors.head?.map (·.2)).getD .missing
        { acc with options := acc.options.push { info := i, setter, ancestors := ancestors.drop 1 } }
      | _ => acc
    let ancestors := match info with
      | .ofCommandInfo i => (i.elaborator, i.stx) :: ancestors
      | other => match other.toElabInfo? with
        | some i => (i.elaborator, i.stx) :: ancestors
        | none => ancestors
    children.foldl (walk ancestors) acc

/-- The setting that `found` records: its value and form from its `set_option` syntax, and, when
its name is not in the module's source text, its origin, the innermost node above whose syntax
does not contain the name, the macro that wrote it. -/
def settingOf (env : Environment) (decls : OptionDecls) (fileMap : FileMap) (found : Found) :
    Setting :=
  let id := found.info.stx
  let source := id.getHeadInfo matches .original ..
  let origin := if source then none else
    (found.ancestors.find? fun (_, stx) => !mentions stx id).map fun (declaration, _) =>
      Origin.mk declaration (((env.getModuleIdxFor? declaration).bind fun idx =>
          env.header.moduleNames[idx.toNat]?).getD
        (if env.contains declaration then env.mainModule else .anonymous))
  let form := formOf found.setter id (found.ancestors.map (·.2))
  { name := found.info.optionName
    value := if form == .elaborated || !found.setter[1].structEq id then none
      else literal found.setter[3]
    registeredDefault := (decls.find? found.info.optionName).map (·.defValue)
    form, origin
    position := positionOf fileMap id }

/-- The observations of the command `stx`, appended to `fold`. -/
def observe (stx : Syntax) (fold : Fold) : CommandElabM Fold := do
  let fileMap ← getFileMap
  let env ← getEnv
  let decls ← getOptionDecls
  let mut acc : Walk := {}
  for tree in (← getInfoTrees) do
    acc := walk [(.anonymous, stx)] acc tree
  let settings := acc.options.map (settingOf env decls fileMap)
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
