module

public import Lean.Attributes
public import Lean.Meta.Basic
public import Lean.ResolveName
public import RegulaPolicy.External

/-! # Assumptions, checked operations and observers of external systems

Three attributes declare what Regula's code relies on about a system outside Lean's logic
(`RegulaPolicy.External`):

* `@[regula_assumption <system> <source>+]` on a predicate over a model of the system, which the
  theorems that rest on the property take as a hypothesis;
* `@[regula_checked <system> <contract> <source>+]` on an operation that runs an operation of the
  system, tests the postcondition of that operation on its result and fails when the test fails,
  where `<contract>` is the theorem that states the postcondition;
* `@[regula_observer <system>]` on IO code that supplies the real system: a place where the
  system's primitive operations may be called.

A source is `(lean "<release tag>" "<file below src>#L<line>-L<line>")`, a file below `src` of the
Lean 4 repository at a release tag, `(document <system> "<reference>")`, a document about a system,
or `(trusted "<reason>")`. The words `lean`, `document` and `trusted` are matched as identifiers, so
they do not become keywords of the files that import this module. A `lean` source must be pinned to
the release of the Lean that elaborates the module, `v` and `Lean.versionString`: after a toolchain
upgrade, each assumption whose source was read at the earlier release fails to elaborate until its
source is read again at the new one (`RegulaPolicy.External.Source.stale`). A document about Lean or
Lake, or one whose reference names a place of the Lean 4 repository or of Lean's documentation, is
refused (`RegulaPolicy.External.Source.unpinned`), so a fact about Lean or Lake carries its release.

Each attribute is checked where it is written: an assumption is a definition or an inductive type
whose type ends in `Prop`, read with Lean's reduction; a checked operation is a definition, and its
contract a theorem; an observer is a definition or an opaque constant. A role is given in the
module that declares the constant, and once. Each constant is declared by one module, so no import
can carry a second role for it, and `roles` meets each constant at most once.

A `module` imports this module with `meta import Regula.Assumption`, as it imports
`Regula.Decision`; the extension is an ordinary definition, so the checker reads the roles through
it (`roles`). The attributes record what is written and decide nothing: which assumptions a claim
rests on is read from the constants it uses (`RegulaPolicy.Assumptions`). -/

public section

namespace Regula.Assumption

open Lean RegulaPolicy.External

/-- The declarations the current module gives a role, with the role. Lean saves them with the
module and loads them wherever it is imported, as `Regula.Decision` does for its registrations.
As there, the role of a declaration that is private to its module is saved for importers that load
the module's private data only. -/
initialize roleExtension :
    PersistentEnvExtension (Name × Role) (Name × Role) (NameMap Role) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun _ _ => pure {}
    addEntryFn := fun roles (declaration, role) => roles.insert declaration role
    exportEntriesFnEx := fun env roles =>
      let all := roles.foldl (fun entries name role => entries.push (name, role)) #[]
        |>.qsort (fun a b => Name.quickLt a.1 b.1)
      let exported := all.filter fun (name, _) =>
        (env.setExporting true).contains (skipRealize := false) name
      { exported, server := exported, «private» := all }
    replay? := some fun _ replayed constants roles =>
      constants.foldl (init := roles) fun roles constant =>
        match replayed.find? constant with
        | some role => roles.insert constant role
        | none => roles
  }

/-- The sources of an assumption or a checked operation. -/
declare_syntax_cat regula_source

/-- A file below `src` of the Lean 4 repository at a release tag, with its lines. -/
syntax (name := leanSource) "(" &"lean" str str ")" : regula_source

/-- A document about a system that states the fact and identifies its own version. -/
syntax (name := documentSource) "(" &"document" ident str ")" : regula_source

/-- No source states the fact: it is trusted for the given reason. -/
syntax (name := trustedSource) "(" &"trusted" str ")" : regula_source

/-- `@[regula_assumption <system> <source>+]`: a property of an external system that the theorems
resting on it take as a hypothesis. -/
syntax (name := regula_assumption) "regula_assumption " ident (ppSpace regula_source)+ : attr

/-- `@[regula_checked <system> <contract> <source>+]`: an operation that runs an operation of the
system and tests its postcondition, stated by the theorem `<contract>`, on the result. -/
syntax (name := regula_checked) "regula_checked " ident ppSpace ident (ppSpace regula_source)+ :
  attr

/-- `@[regula_observer <system>]`: IO code that supplies the real system. -/
syntax (name := regula_observer) "regula_observer " ident : attr

/-- The system an identifier names. The name is read without its macro scopes, so a system that a
macro writes in its expansion names that system. -/
private def system (stx : Syntax) : CoreM System := do
  let name := stx.getId.eraseMacroScopes
  match System.parse? name.toString with
  | some system => return system
  | none => throwErrorAt stx "unknown external system `{name}`; the systems are \
      {String.intercalate ", " (System.all.map System.spelling)}"

/-- The source a `regula_source` node writes. -/
private def source (stx : Syntax) : CoreM Source := do
  let text (index : Nat) : CoreM String := do
    let some value := stx[index].isStrLit?
      | throwErrorAt stx[index] "expected a string literal"
    if value.isEmpty then throwErrorAt stx[index] "a source needs a nonempty string"
    return value
  match stx.getKind with
  | ``leanSource =>
    let version ← text 2
    let source := Source.lean version (← text 3)
    let current := s!"v{Lean.versionString}"
    if source.stale current then
      throwErrorAt stx[2] "this source is pinned to Lean {version}, but Lean {current} \
        elaborates this module: read the source again at {current}, and pin it to {current} \
        when it still states the fact"
    return source
  | ``documentSource =>
    let source := Source.document (← system stx[2]) (← text 3)
    if source.unpinned then
      throwErrorAt stx "a document about Lean or Lake, or one in the Lean 4 repository or Lean's \
        documentation, has no release that this module checks: cite the file with \
        `(lean \"v{Lean.versionString}\" \"<file below src>#L<line>-L<line>\")`"
    return source
  | ``trustedSource => return .trusted (← text 2)
  | _ => throwErrorAt stx "expected `(lean \"<tag>\" \"<file>#L<line>\")`, \
      `(document <system> \"<reference>\")` or `(trusted \"<reason>\")`"

/-- Whether a type ends in `Prop`, read with Lean's reduction: after the binders that
`forallTelescopeReducing` exposes, its codomain reduces (`whnf`) to `Sort 0`. So a type written
with an alias of `Prop`, or of a function type that ends in `Prop`, ends in `Prop`. -/
private def endsInProp (type : Expr) : MetaM Bool :=
  Meta.forallTelescopeReducing type fun _ codomain => do
    match ← Meta.whnf codomain with
    | .sort level => return level.normalize.isZero
    | _ => return false

/-- The role an attribute's syntax writes for `declaration`, checked against the declaration. -/
private def role (declaration : Name) (stx : Syntax) : CoreM Role := do
  let info ← getConstInfo declaration
  let shown := privateToUserName declaration
  match stx.getKind with
  | ``regula_assumption =>
    unless (info matches .defnInfo _ | .inductInfo _) && (← (endsInProp info.type).run') do
      throwError "`{shown}` is not a predicate: an assumption is a definition or an inductive \
        type whose type ends in `Prop`, so that a theorem can take it as a hypothesis"
    return .assumption (← system stx[1]) (← stx[2].getArgs.toList.mapM source)
  | ``regula_checked =>
    unless info matches .defnInfo _ do
      throwError "`{shown}` is not a definition: a checked operation is a definition that runs \
        an operation of the system and tests its result"
    let contract ← resolveGlobalConstNoOverload stx[2]
    unless (← getConstInfo contract) matches .thmInfo _ do
      throwErrorAt stx[2] "`{contract}` is not a theorem: the contract of a checked operation \
        is the theorem that states its postcondition"
    return .checked (← system stx[1]) contract (← stx[3].getArgs.toList.mapM source)
  | ``regula_observer =>
    unless info matches .defnInfo _ | .opaqueInfo _ do
      throwError "`{shown}` is not a definition: an observer is IO code that runs"
    return .observer (← system stx[1])
  | _ => throwErrorAt stx "unexpected attribute syntax"

/-- Register one of the three attributes. Each is applied after compilation, as
`@[regula_decision]` is, so that it marks the declaration that carries it and no definition Lean
generates from it. -/
private def register (name : Name) (descr : String) : IO Unit :=
  registerBuiltinAttribute {
    ref := ``roleExtension
    name
    descr
    applicationTime := .afterCompilation
    add := fun declaration stx kind => do
      unless kind == .global do throwAttrMustBeGlobal name kind
      let env ← getEnv
      unless roleExtension.toEnvExtension.asyncMayModify env declaration do
        throwAttrNotInAsyncCtx name declaration env.asyncPrefix?
      if let some index := env.getModuleIdxFor? declaration then
        throwError "`{privateToUserName declaration}` is declared in \
          `{env.header.moduleNames[index.toNat]!}`: a role is given only in the module that \
          declares the constant"
      if let some earlier := (roleExtension.getState env).find? declaration then
        throwError "`{privateToUserName declaration}` already has a role: {repr earlier}"
      let role ← role declaration stx
      modifyEnv fun env => roleExtension.addEntry (asyncDecl := declaration) env (declaration, role)
  }

initialize (register `regula_assumption
  "Declares a property of an external system that the theorems resting on it take as a hypothesis.")

initialize (register `regula_checked
  "Declares an operation that tests the postcondition of an operation of a system on its result.")

initialize (register `regula_observer
  "Declares IO code that supplies an external system, where its primitive operations may be \
    called.")

/-- Every declaration that has a role in `env`, with the role: those of the current module and
those of every loaded module, sorted by name. A role is given only in the module that declares the
constant, and once there (`register`), so no two entries name the same constant. -/
def roles (env : Environment) : Array (Name × Role) :=
  let all := (Array.range env.header.moduleNames.size).foldl
    (init := roleExtension.getState env) fun roles index =>
      (roleExtension.getModuleEntries env index).foldl (init := roles)
        fun roles (declaration, role) => roles.insert declaration role
  all.foldl (fun entries name role => entries.push (name, role)) #[]
    |>.qsort (fun a b => Name.lt a.1 b.1)

end Regula.Assumption
