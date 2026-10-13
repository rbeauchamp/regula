import Lean.Elab.Command
import RegulaObserver.Record

/-! # Regula's elaboration observer

A Lean plugin that records, for each module it elaborates, what the module's commands did that a
build's messages do not show: the options the source set, the `#guard_msgs` and `#guard_panic`
commands that drop or replace messages, and the messages Lean keeps out of its command-line output.
It decides nothing: Regula's audit reads the record from the module's `.olean`
(`RegulaObserver.records`) and decides RG2003 and RG2006 from it. It imports only Lean, since Lean
loads a plugin's shared library alone, without the libraries of its imports.

Lake loads it into the elaboration of each module of a target whose `plugins` name its shared
library, `@regula/RegulaObserver:shared`, through Lake's own `presetup` facet, and Regula's audit
reads from each claimed module's completed `presetup` whether it did
(`Regula.Checker.Observer.pluginLoaded`). Loading the plugin runs this module's initializers,
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
65), and the record holds the options set through `Lean.Elab.elabSetOption` (`setOptionKinds`) and
through the documentation command `{set_option name value}`. Lean records an option's name in two
more places that set no option of the scope, the documentation role `{option}` and a `simp` user
option, which the record leaves out (`settingOf?`). An option that elaborator code changes
directly is outside the record: a temporary change for the code's own commands through
`withScope`, such as `autoImplicit` in the `ToExpr` deriving handler
(`Lean/Elab/Deriving/ToExpr.lean` line 228), `warn.exposeOnPrivate` in every deriving handler
(`Lean/Elab/Deriving/Basic.lean` lines 294 to 297) and
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

/-- The syntax kinds of the commands that Lean elaborates for `cmd` once every macro of `steps` has
expanded them, where `steps` holds each macro expansion that Lean elaborated (`macroSteps`) as the
syntax before and after it. A command that a macro expanded gives the kinds of its expansion. A
list of commands, a node of kind `null` such as a macro's expansion to several commands, gives the
kinds of each of its commands, since Lean elaborates such a list command by command
(`Lean.Elab.Command.elabCommand`, `Lean/Elab/Command.lean` lines 698 to 703). Any other command,
one that no macro expanded, gives its own kind. On each path at most `fuel` expansions are
followed; one more gives the anonymous kind, which no decision accepts. The recursion ends, since
an argument of a list is a smaller syntax tree and each expansion uses up `fuel`. -/
partial def leafKinds (steps : Array (Syntax × Syntax)) (fuel : Nat) (cmd : Syntax) : Array Name :=
  match steps.find? (sameOccurrence ·.1 cmd), fuel with
  | some _, 0 => #[.anonymous]
  | some (_, output), fuel + 1 => leafKinds steps fuel output
  | none, _ =>
    if cmd.isOfKind nullKind then cmd.getArgs.flatMap (leafKinds steps fuel) else #[cmd.getKind]

/-- The form of the `set_option` syntax `setter`, with `ancestors` the syntax of the nodes above
it, and for the command form before one command the syntax kinds of the commands that Lean
elaborates for the command it wraps (`wrappedCommand`) once the macros of `steps` have expanded
them (`leafKinds`). The command form is `commandIn` when an ancestor is `cmd in cmd` whose first
command is `setter`; the `grind` tactic form is a tactic form. -/
def formOf (steps : Array (Syntax × Syntax)) (setter : Syntax) (ancestors : List Syntax) :
    Form × Option (Array Name) :=
  if setter.isOfKind ``Lean.Parser.Command.set_option then
    match ancestors.find? fun a => a.isOfKind ``Lean.Parser.Command.in &&
        sameOccurrence a[0] setter with
    | some a => (.commandIn, some (leafKinds steps steps.size (wrappedCommand a[2])))
    | none => (.command, none)
  else if setter.isOfKind ``Lean.Parser.Term.set_option then (.term, none)
  else (.tactic, none)

/-- An option name that Lean recorded (`Lean.Elab.OptionInfo`), with what the walk knew above it. -/
structure Found where
  /-- The recorded name. -/
  info : OptionInfo
  /-- The syntax of the nodes above it, innermost first. -/
  ancestors : List Syntax
  /-- For a name recorded inside an element of a documentation comment, the expander that Lean's
  documentation elaborator records for the innermost such element (`Lean.Elab.DocElabInfo`), or
  none when it records none; none outside documentation. -/
  doc : Option (Option Name)

/-- What one walk of a command's info trees collects. -/
structure Walk where
  /-- Each option name that Lean recorded. -/
  options : Array Found := #[]
  /-- Each command elaborated as `#guard_msgs` or `#guard_panic`. -/
  guards : Array Syntax := #[]
  /-- Each identifier inside a documentation comment that Lean resolved to a constant, with that
  constant, from the term information that the resolution recorded
  (`realizeGlobalConstNoOverloadWithInfo`). -/
  resolved : Array (Syntax × Name) := #[]
  /-- Each command that an elaborator expanded, with the elaborator and the syntax before and after
  the expansion: a command node whose child records that expansion of the node's own syntax
  (`Lean.Elab.MacroExpansionInfo`). `macroSteps` keeps those whose elaborator is a macro. -/
  expansions : Array (Name × Syntax × Syntax) := #[]

/-- Walk an info tree, with `ancestors` the syntax of each command, tactic and term node above,
innermost first, and `doc` what `Found.doc` records for a name below. Lean's documentation
elaborator elaborates each element of a comment under a `Lean.Elab.DocInfo` node and records the
expander that elaborated it as a `Lean.Elab.DocElabInfo` leaf among that node's children
(`Lean/Elab/DocString.lean` lines 1487 to 1489, 1549 to 1554, 1572 to 1574 and 1679 to 1684).
When a macro expands a command, Lean records a command node that names the macro, whose child
records the expansion of the same syntax (`Lean.Elab.Command.elabCommand`, `Lean/Elab/Command.lean`
lines 712 to 716, and `withMacroExpansion`, lines 656 to 658). -/
partial def walk (ancestors : List Syntax) (doc : Option (Option Name)) (acc : Walk) :
    InfoTree → Walk
  | .context _ tree => walk ancestors doc acc tree
  | .hole _ => acc
  | .node info children =>
    let acc := match info with
      | .ofCommandInfo i =>
        let acc := if guardKinds.contains i.stx.getKind then
          { acc with guards := acc.guards.push i.stx } else acc
        children.foldl (init := acc) fun acc child => match child with
          | .node (.ofMacroExpansionInfo m) _ => if sameOccurrence m.stx i.stx then
              { acc with expansions := acc.expansions.push (i.elaborator, m.stx, m.output) }
            else acc
          | _ => acc
      | .ofOptionInfo i => { acc with options := acc.options.push { info := i, ancestors, doc } }
      | .ofTermInfo i => match doc, i.expr with
        | some _, .const name _ => { acc with resolved := acc.resolved.push (i.stx, name) }
        | _, _ => acc
      | _ => acc
    let doc := match info with
      | .ofDocInfo _ => some <| children.toList.findSome? fun
          | .node (.ofDocElabInfo d) _ => some d.name
          | _ => none
      | _ => doc
    let ancestors := match info with
      | .ofCommandInfo i => i.stx :: ancestors
      | other => match other.toElabInfo? with
        | some i => i.stx :: ancestors
        | none => ancestors
    children.foldl (walk ancestors doc) acc

/-- The expander that Lean records for the documentation command `{set_option name value}`
(`Lean.Doc.set_option`, `Lean/Elab/DocString/Builtin.lean` lines 1329 to 1338), which sets the
option for the rest of the comment. -/
def docSetter : Name := `Lean.Doc.set_option.getArgs

/-- The expander that Lean records for the documentation role `{option}`, which refers to an option
by its name or by `set_option` text and sets none: it validates the value and only renders the
reference (`Lean.Doc.option`, `Lean/Elab/DocString/Builtin.lean` lines 1161 to 1205). -/
def docReference : Name := `Lean.Doc.option.getArgs

/-- The value that the documentation command `{set_option name value}` sets, from the syntax `block`
of the command and `id`, the option's name in it: its arguments must be `name` and a literal value,
both positional, and Lean reads a numeral, a string or an identifier that resolves to `Bool.true`
or `Bool.false` (`instance : FromDocArg DataValue`, `Lean/Elab/DocString.lean` lines 454 to 466,
which refuses any other constant). The identifier's constant is the one Lean resolved, read from
`resolved` (`Walk.resolved`), so `Bool.true` and `true` give the same value. None for any other
syntax, or for an identifier with no resolution recorded. -/
def docValue (resolved : Array (Syntax × Name)) (id : Syntax) (block : Syntax) :
    Option DataValue :=
  match block[2].getArgs with
  | #[name, value] =>
    if !block.isOfKind `Lean.Doc.Syntax.command || !name.isOfKind `Lean.Doc.Syntax.anon ||
        !value.isOfKind `Lean.Doc.Syntax.anon || !sameOccurrence name[0][0] id then none
    else
      let arg := value[0]
      if arg.isOfKind `Lean.Doc.Syntax.arg_num then arg[0].isNatLit?.map .ofNat
      else if arg.isOfKind `Lean.Doc.Syntax.arg_str then arg[0].isStrLit?.map .ofString
      else if arg.isOfKind `Lean.Doc.Syntax.arg_ident then
        match (resolved.find? (sameOccurrence ·.1 arg[0])).map (·.2) with
        | some ``Bool.true => some (.ofBool true)
        | some ``Bool.false => some (.ofBool false)
        | _ => none
      else none
  | _ => none

/-- Whether `found` is a `simp` or `dsimp` configuration item `+user.name`, `-user.name` or
`(user.name := value)`: its name is under `tactic.simp.user` and it is the option of a
configuration item above it. Lean records it in `Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions`
(`Lean/Elab/ConfigEval/Extra.lean` lines 21 to 29), whose only callers, the configuration
elaborators of `simp` and `dsimp` (`Lean/Elab/Tactic/Simp.lean` lines 57 and 98), set the option in
the tactic's own `userConfig`, which only `simp`'s procedures read
(`Lean/Meta/Tactic/Simp/Types.lean` lines 64 to 66 and 472), not in the options of the scope. -/
def simpUserOption (found : Found) : Bool :=
  (`tactic.simp.user).isPrefixOf found.info.optionName &&
    found.ancestors.any fun stx => (stx.find? fun n =>
      [`Lean.Parser.Tactic.posConfigItem, `Lean.Parser.Tactic.negConfigItem,
        `Lean.Parser.Tactic.valConfigItem].contains n.getKind &&
        n.getArgs.any (sameOccurrence · found.info.stx)).isSome

/-- The setting that `found` records, or none when the code that recorded it sets no option of the
source. Lean v4.34.1 records an option's name in four places, which
`Regula.Checker.GeneratedSettingSearch.producers` lists: `Lean.Elab.elabSetOption`, which the
`set_option` forms call; the documentation command `{set_option name value}` (`docSetter`); the
documentation role `{option}` (`docReference`), which sets none; and a `simp` user option
(`simpUserOption`), which sets none of the scope. A name under `set_option` syntax has the value
and form of that syntax (`setterOf`); the documentation command's has its value (`docValue`); any
other has no value, so RG2006 rejects it. The form before one command reads the macro expansions
`steps` (`formOf`). Who wrote the syntax is not recorded: RG2006 decides on the setting alone. -/
def settingOf? (decls : OptionDecls) (fileMap : FileMap) (resolved : Array (Syntax × Name))
    (steps : Array (Syntax × Syntax)) (found : Found) : Option Setting :=
  let id := found.info.stx
  let setting (value : Option DataValue) (form : Form) (wrapped : Option (Array Name)) :
      Setting :=
    { name := found.info.optionName
      value, form, wrapped
      registeredDefault := (decls.find? found.info.optionName).map (·.defValue)
      position := positionOf fileMap id }
  match setterOf id found.ancestors, found.doc with
  | some setter, _ =>
    let (form, wrapped) := formOf steps setter found.ancestors
    some (setting (literal setter[3]) form wrapped)
  | none, some (some expander) =>
    if expander == docReference then none
    else if expander == docSetter then
      some (setting ((found.ancestors.find? (·.isOfKind `Lean.Doc.Syntax.command)).bind
        (docValue resolved id)) .docComment none)
    else some (setting none .elaborated none)
  | none, _ => if simpUserOption found then none else some (setting none .elaborated none)

/-- The expansions of `expansions` (`Walk.expansions`) whose elaborator is a macro of its syntax's
kind in `env`, as `Lean.Elab.expandMacroImpl?` finds one (`Lean/Elab/Util.lean` lines 157 to 167),
as the syntax before and after each. Only these are steps that `leafKinds` follows: a macro runs
in `MacroM` and returns syntax, so it changes no message and no state of the command. A command
whose elaborator records an expansion itself, as `Lean.Elab.Command.adaptExpander` does
(`Lean/Elab/Command.lean` lines 874 to 876), stays a command that no macro expanded. -/
def macroSteps (env : Environment) (expansions : Array (Name × Syntax × Syntax)) :
    Array (Syntax × Syntax) :=
  expansions.filterMap fun (elaborator, before, after) =>
    if (macroAttribute.getEntries env before.getKind).any (·.declName == elaborator) then
      some (before, after)
    else none

/-- The observations of the command `stx`, appended to `fold`. -/
def observe (stx : Syntax) (fold : Fold) : CommandElabM Fold := do
  let fileMap ← getFileMap
  let decls ← getOptionDecls
  let mut acc : Walk := {}
  for tree in (← getInfoTrees) do
    acc := walk [stx] none acc tree
  let steps := macroSteps (← getEnv) acc.expansions
  let settings := acc.options.filterMap (settingOf? decls fileMap acc.resolved steps)
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
