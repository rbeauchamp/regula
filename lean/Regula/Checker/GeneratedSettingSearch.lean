import Lean
import RegulaPolicy.Community

/-! # The settings that Lean's generated code writes

The search that gives `RegulaPolicy.Community.generatedSettings`: the (option, value) pairs that the
code of the pinned toolchain writes as `set_option` syntax into the code it generates. RG2006
accepts each of them wherever a claimed module's source sets it. The registry checks run the search
and refuse unless its result is that list, so the list follows the pinned toolchain.

The search reads the elaborated values of the constants in the environment of the modules `Lean`
and `Lake`, which import `Init` and `Std`. A quotation elaborates to an application of
`Lean.Syntax.node` or one of `Lean.Syntax.node1` to `Lean.Syntax.node8` to a literal kind name and
the node's children. A construction is such an application whose kind is one of `kinds`. Its
option is the name of its second child, a `Lean.Syntax.ident`, and its value is what Lean's
`set_option` elaborator reads from its fourth child (`optionValue?`), as `RegulaObserver.literal`
reads the same positions of the syntax. A construction whose option or value is not a literal of
the compiled code gives no pair; the search names the constant that holds it (`nonLiteral`).

Each other function that the compiled code applies to a kind of `kinds` is listed too (`readers`),
so that a construction through a function other than `Lean.Syntax.node` is not left out silently:
the registry checks refuse unless both lists are the ones this module states. A kind name that the
code computes rather than writes as a literal is outside the search. -/

namespace Regula.Checker.GeneratedSettingSearch

open Lean

/-- The syntax kinds of Lean's `set_option` forms, as `RegulaObserver.setOptionKinds` lists them:
the command, the term, the tactic and the `grind` tactic form. -/
def kinds : List Name :=
  [``Lean.Parser.Command.set_option, ``Lean.Parser.Term.set_option,
    ``Lean.Parser.Tactic.set_option, ``Lean.Parser.Tactic.Grind.setOption]

/-- What the search finds. -/
structure Result where
  /-- The (option, value) pairs of the constructions with a literal option and value, each once,
  sorted by their text. -/
  pairs : List (Name × RegulaPolicy.Community.OptionValue)
  /-- The constants with a construction whose option or value is not a literal, sorted. -/
  nonLiteral : List Name
  /-- The functions other than the syntax-node constructors that the code applies to a kind of
  `kinds`, sorted. -/
  readers : List Name
  /-- The definitions that construct a `Lean.Elab.OptionInfo`, the information node in which Lean
  records an option's name, other than recursors and `noConfusion`, sorted. -/
  producers : List Name
  /-- The constants that call `Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions`, sorted. -/
  userOptionCallers : List Name
  deriving BEq, Repr

/-- The constant `e` builds, when it is a literal `Name`: `Name.anonymous`, `Name.str`,
`Name.num` or one of the `Name.mkStr` and `Name.mkNum` helpers applied to literals, or a name under
`Lean.addMacroScope`, which a quotation applies to the names it writes. -/
partial def nameLit? (e : Expr) : Option Name :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Name.anonymous _, #[] => some .anonymous
  | .const ``Name.str _, #[p, .lit (.strVal s)] | .const ``Name.mkStr _, #[p, .lit (.strVal s)] =>
    (nameLit? p).map (·.str s)
  | .const ``Name.num _, #[p, .lit (.natVal k)] | .const ``Name.mkNum _, #[p, .lit (.natVal k)] =>
    (nameLit? p).map (·.num k)
  | .const ``Lean.addMacroScope _, #[_, n, _] => nameLit? n
  | .const c _, args =>
    if c.getPrefix == ``Name && "mkStr".isPrefixOf c.getString! && !args.isEmpty then
      args.foldlM (init := Name.anonymous) fun n a => match a with
        | .lit (.strVal s) => some (n.str s)
        | _ => none
    else none
  | _, _ => none

/-- The elements of a literal array: `#[…]`, as `List.toArray` of a literal list or one of the
`Array.mkArray` helpers. -/
partial def arrayLit? (e : Expr) : Option (Array Expr) :=
  match e.getAppFn with
  | .const c _ =>
    if c.getPrefix == ``Array && "mkArray".isPrefixOf c.getString! then
      some (e.getAppArgs.extract 1)
    else if c == ``List.toArray then listLit? (e.getArg! 1)
    else none
  | _ => none
where
  /-- The elements of a literal list. -/
  listLit? (e : Expr) : Option (Array Expr) :=
    match e.getAppFn, e.getAppArgs with
    | .const ``List.nil _, _ => some #[]
    | .const ``List.cons _, #[_, h, t] => (listLit? t).map (#[h] ++ ·)
    | _, _ => none

/-- The kind and children of a syntax node that `e` builds with `Lean.Syntax.node` or one of the
`Lean.Syntax.node1` to `Lean.Syntax.node8` helpers, when its kind is a literal. -/
def node? (e : Expr) : Option (Name × Array Expr) :=
  match e.getAppFn with
  | .const c _ =>
    if c == ``Syntax.node && e.getAppNumArgs == 3 then
      (nameLit? (e.getArg! 1)).bind fun k => (arrayLit? (e.getArg! 2)).map (k, ·)
    else if c.getPrefix == ``Syntax && "node".isPrefixOf c.getString! && c != ``Syntax.node &&
        e.getAppNumArgs ≥ 2 then
      (nameLit? (e.getArg! 1)).map (·, e.getAppArgs.extract 2)
    else none
  | _ => none

/-- The name of a literal identifier node. -/
def identName? (e : Expr) : Option Name :=
  if e.isAppOfArity ``Syntax.ident 4 then nameLit? (e.getArg! 2) else none

/-- The syntax that `e` builds when it is a literal atom, or a literal node of one such child, such
as the `num` or `str` node of a numeral or a string literal. -/
partial def valueSyntax? (e : Expr) : Option Syntax :=
  if e.isAppOfArity ``Syntax.atom 2 then
    match e.getArg! 1 with
    | .lit (.strVal s) => some (.atom .none s)
    | _ => none
  else match node? e with
    | some (k, #[a]) => (valueSyntax? a).map fun s => .node .none k #[s]
    | _ => none

/-- The value that Lean's `set_option` elaborator reads from the value syntax `val`
(`Lean.Elab.elabSetOption`, `Lean/Elab/SetOption.lean` lines 69 to 77), through the same
`Syntax.isStrLit?` and `Syntax.isNatLit?`: a string literal, a numeral in any base Lean accepts, or
the atom `true` or `false`. -/
def optionValue? (val : Syntax) : Option RegulaPolicy.Community.OptionValue :=
  match val.isStrLit?, val.isNatLit?, val with
  | some s, _, _ => some (.string s)
  | none, some n, _ => some (.nat n)
  | none, none, .atom _ "true" => some (.bool true)
  | none, none, .atom _ "false" => some (.bool false)
  | _, _, _ => none

/-- What one constant's value holds: its constructions, as an option and a value when both are
literals, and the functions it applies to a kind of `kinds` that are not syntax-node
constructors. -/
structure Found where
  /-- Each construction's pair, or none when its option or value is not a literal. -/
  constructions : Array (Option (Name × RegulaPolicy.Community.OptionValue)) := #[]
  /-- Each other function applied to a kind. -/
  readers : Array Name := #[]

/-- Walk `e` once for each distinct subterm, adding what `Found` records. Each application is read
at its whole spine, so a partial application is not read again. -/
partial def scan (e : Expr) : StateM (Std.HashSet Expr × Found) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, found) => (seen.insert e, found)
  match e with
  | .app .. =>
    let args := e.getAppArgs
    if args.any fun a => (nameLit? a).any kinds.contains then
      match node? e with
      | some (k, children) =>
        if kinds.contains k then
          let pair := (children[1]?.bind identName?).bind fun name =>
            ((children[3]?.bind valueSyntax?).bind optionValue?).map (name, ·)
          modify fun (seen, found) =>
            (seen, { found with constructions := found.constructions.push pair })
      | none =>
        let head := match e.getAppFn with
          | .const c _ => c
          | _ => `«non-constant function»
        modify fun (seen, found) => (seen, { found with readers := found.readers.push head })
    scan e.getAppFn
    for a in args do scan a
  | .lam _ t b _ | .forallE _ t b _ => do scan t; scan b
  | .letE _ t v b _ => do scan t; scan v; scan b
  | .mdata _ b | .proj _ _ b => scan b
  | _ => pure ()

/-- The text of a pair, by which the result sorts the pairs. -/
def pairText (p : Name × RegulaPolicy.Community.OptionValue) : String :=
  s!"{p.1} {p.2.text}"

/-- The search over the environment of the modules `Lean` and `Lake` of the toolchain whose library
is on the search path. A constant is read only when its value holds the string `set_option` or
`setOption`, the last component of each name in `kinds`, which a literal name always holds. -/
private unsafe def searchImpl : IO Result := do
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `Lean }, { module := `Lake }] {}
  let mut pairs : Array (Name × RegulaPolicy.Community.OptionValue) := #[]
  let mut nonLiteral : Array Name := #[]
  let mut readers : Array Name := #[]
  let mut producers : Array Name := #[]
  let mut userOptionCallers : Array Name := #[]
  for (name, c) in env.constants.toList do
    let some value := c.value? (allowOpaque := true) | continue
    if (value.find? (·.isConstOf ``Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions)).isSome then
      userOptionCallers := userOptionCallers.push name
    if !c.isTheorem && !isAuxRecursor env name && !isNoConfusion env name &&
        (value.find? (·.isAppOfArity ``Lean.Elab.OptionInfo.mk 3)).isSome then
      producers := producers.push name
    unless (value.find? fun e => e == mkStrLit "set_option" || e == mkStrLit "setOption").isSome do
      continue
    let (_, _, found) := Id.run ((scan value).run ({}, {}))
    for construction in found.constructions do
      match construction with
      | some pair => pairs := pairs.push pair
      | none => nonLiteral := nonLiteral.push name
    readers := readers ++ found.readers
  let byText (a b : Name) : Bool := a.toString ≤ b.toString
  return {
    pairs := pairs.toList.eraseDups.mergeSort (pairText · ≤ pairText ·)
    nonLiteral := nonLiteral.toList.eraseDups.mergeSort byText
    readers := readers.toList.eraseDups.mergeSort byText
    producers := producers.toList.mergeSort byText
    userOptionCallers := userOptionCallers.toList.mergeSort byText }

/-- `searchImpl`: it imports a second environment, which a safe definition cannot do. -/
@[implemented_by searchImpl]
opaque search : IO Result

/-- The constant that holds the one construction with no literal option: `#where`'s
`describeOptions` (`Lean/Elab/BuiltinCommand.lean` lines 698 to 721), which builds a `set_option`
command for each option the current scope sets and only puts it into the message `#where` prints,
so no elaborator runs it. -/
def nonLiteral : List Name :=
  [.num `_private.Lean.Elab.BuiltinCommand 0 ++ `Lean.Elab.Command.elabWhere.describeOptions]

/-- The other functions that Lean's code applies to a `set_option` kind, none of which builds a
syntax node: the parsers that `leading_parser` and `syntax` declare (`Lean.Parser.leadingNode`,
`Lean.Parser.mkAntiquot`, `Lean.Parser.withCache`, `Lean.ParserDescr.node`), their formatters and
parenthesizers, the registrations of builtin parsers, elaborators, documentation and declaration
ranges, and the comparison of a kind with a node's kind (`BEq.beq`). -/
def readers : List Name :=
  [``BEq.beq, ``Lean.KeyedDeclsAttribute.addBuiltin, ``Lean.Parser.addBuiltinLeadingParser,
    ``Lean.Parser.leadingNode, ``Lean.Parser.leadingNode.formatter, ``Lean.Parser.mkAntiquot,
    ``Lean.Parser.mkAntiquot.formatter, ``Lean.Parser.mkAntiquot.parenthesizer,
    ``Lean.Parser.withCache, ``Lean.Parser.withCache.formatter,
    ``Lean.Parser.withCache.parenthesizer, ``Lean.ParserDescr.node,
    ``Lean.PrettyPrinter.Parenthesizer.leadingNode.parenthesizer, ``Lean.addBuiltinDeclarationRanges,
    ``Lean.addBuiltinDocString].mergeSort (·.toString ≤ ·.toString)

/-- The definitions that construct a `Lean.Elab.OptionInfo`, each of which records an option's name
for `RegulaObserver.settingOf?` to classify: `Lean.Elab.elabSetOption`, which the `set_option`
forms call and which sets the option; the documentation command `{set_option name value}`
(`Lean.Doc.set_option`), which sets it for the rest of the comment; the documentation role
`{option}` (`Lean.Doc.option`), which refers to one and sets none;
`Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions`, which sets it in the configuration of the
tactic that calls it (`userOptionCallers`); `Lean.Elab.Info.setStx`, which copies a recorded name
with other syntax for `Lean.Elab.InfoTree.addTrailing?`; and `Lean.Elab.OptionInfo.mk._flat_ctor`,
the constructor's compiled form, which no constant calls. -/
def producers : List Name :=
  [``Lean.Doc.option, ``Lean.Doc.set_option, ``Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions,
    `Lean.Elab.OptionInfo.mk._flat_ctor, ``Lean.Elab.elabSetOption,
    .num `_private.Lean.Elab.InfoTree.Basic 0 ++ `Lean.Elab.Info.setStx].mergeSort
    (·.toString ≤ ·.toString)

/-- The callers of `Lean.Elab.ConfigEval.EvalConfigItem.evalSetOptions`: the configuration
elaborators of `simp` and `dsimp` (`Lean/Elab/Tactic/Simp.lean` lines 57 and 98), which set a
user option under `tactic.simp.user` in the tactic's own `userConfig`
(`RegulaObserver.simpUserOption`). -/
def userOptionCallers : List Name :=
  [.num `_private.Lean.Elab.Tactic.Simp 0 ++ `Lean.Elab.Tactic.elabDSimpConfigCore.evalConfigItem,
    .num `_private.Lean.Elab.Tactic.Simp 0 ++ `Lean.Elab.Tactic.elabSimpConfigAux.evalConfigItem]

end Regula.Checker.GeneratedSettingSearch
