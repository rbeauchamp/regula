import Lake.Load.Workspace
import Std.Data.HashSet
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Util.CollectAxioms
import Regula.Input
import Regula.Decision
import Regula.Checker.Manifest

/-!
# The loader of the closed input

The shell's one read of a finished build: it fills the closed input (`Regula.Closed.Bundle`)
through the interfaces of Lean and Lake that the specification of the smaller Regula names
(`specification/README.md`, "The closed input"), and refuses, as an error that makes the run
`incomplete` (RG2001), every input that does not have the closed form. A read that fails is a
refusal, never an absent file (#441).

What it reads, and through what:

- The workspace: Lake's own load (`Lake.loadWorkspace`), with the toolchain that `LEAN_SYSROOT`
  names, which `lake lint` and `lake exe` set to the toolchain of the Lake that runs them. The
  inherited `LEAN_PATH` and `LEAN_SRC_PATH` are dropped, so the search path is Lake's
  (`Workspace.augmentedLeanPath`). `Lean.findSysroot` is not used: it can find a toolchain that is
  not the pinned one (the specification's measurement).
  For an implicit workspace, `dispatchedFrom_iff` checks the received `LEAN_PATH` first against
  the loaded root's library directory: Lake does not change the driver's working directory for
  `lake -d DIR lint`. A different dispatch is refused before declaration data is read.
- The targets: the root package's libraries and executables, their modules (`getModuleArray`, an
  executable's root), their options (`leanOptions`, and each `-D` argument of `weakLeanArgs` and
  `leanArgs`), every other argument, plugin and dynamic library as an extra, and whether Lake
  builds each by default (`defaultTargets`).
- The claim: `foundation_manifest.json` through the existing reader `Manifest.parse`. A claim of
  the profile `compiler-trusting` is refused: it is not one of the closed input's profiles.
- The module records: for each module of the root package that Lake builds (each module of a
  target, and each module of the root package that their imports reach), its imports and the names
  of the extensions with entries, from `Lean.readModuleDataParts` of its `.olean` files, found by
  `Lean.findOLean` on Lake's search path. A module of the root package is one whose `.olean` lies
  below the root package's `leanLibDir`; a constant of the toolchain is one whose module's `.olean`
  lies below the toolchain's library directory, which is RG1003's named assumption: Lean finds the
  toolchain's library only below the `lib/lean` directory of the pinned toolchain.
- The constants: `Lean.importModules` with `loadExts := false`, so no extension state is built
  and no initializer of a loaded module runs. Each query reads a constant's `ConstantInfo` or the
  module entries of an extension (`getModuleEntries`, which `importModules` sets whatever
  `loadExts` is): `getImplementedBy?`, `isExtern`, `getInitFnNameFor?`, `isNoncomputable`, the
  compiled code (`IR.findEnvDecl`), the `@[csimp]` entries (`CSimp.ext`'s module entries) and the
  decision registrations (`Regula.decisionExtension`'s module entries). None reads an extension's
  built state, which `loadExts := false` leaves at its initial value.
- The axiom sets: `Lean.collectAxioms` of each constant of a claimed module and of each theorem
  that states a correspondence (`axiomsIn`). Lean's recorded table of each module's axioms is an
  extension's state, which `loadExts := false` leaves empty, so the axioms come from the constants.

Two choices are the implementation's, made on the owner's behalf, and recorded in the shell's
documentation:

- One environment cannot hold two modules that declare one name, such as the `main` of two
  programs. So the root of each executable is loaded in an environment of its own, as the
  specification states, and the other library modules are put in as few environments as hold
  them: each module joins the first environment in which no module of the root package that its
  imports reach declares a name that another module there declares.
- The environments are loaded one after another. Before the next one is loaded, the input of the
  last is copied out of its `.olean` data, and that data is freed (`Environment.freeRegions`), so
  the memory of a run is that of one environment. This is why the loader is `unsafe`.

The compiled code and the departures are read here by a mechanism that #487 replaces or proves
(the specification's open obligation): the constants that `IR.findEnvDecl`'s code calls, with the
code of each auxiliary definition that the compiler adds counted as code of the constant it
serves, and a departure for each runtime replacement, recursion helper and `@[csimp]` replacement
whose target the code runs.
-/

namespace Regula.Load

open Lean System
open Regula.Closed

/-- Refuse the input: the run is `incomplete`. -/
def refuse {α : Type} (why : String) : IO α :=
  throw <| IO.userError why

/-- The Lake environment of the toolchain that `LEAN_SYSROOT` names, with the Lake installed beside
its Lean and no inherited search path. -/
def lakeEnvironment : IO Lake.Env := do
  let some sysroot ← IO.getEnv "LEAN_SYSROOT"
    | refuse "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the \
        checker with `lake lint` or `lake exe`, which set it"
  let lean ← Lake.LeanInstall.get sysroot (collocated := true)
  let lake := Lake.LakeInstall.ofLean lean
  match ← (Lake.Env.compute lake lean (← Lake.findElanInstall?)).toBaseIO with
  | .ok env => return { env with initLeanPath := [], initLeanSrcPath := [] }
  | .error why => refuse s!"Lake could not compute its environment: {why}"

/-- Lake's load of the workspace whose root is `dir`. -/
def loadWorkspace (dir : FilePath) : IO Lake.Workspace := do
  let lakeEnv ← lakeEnvironment
  let wsDir ← IO.FS.realPath dir
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
  match ws? with
  | some ws => return ws
  | none =>
    refuse s!"Lake could not load the workspace at {dir}: \
      {"; ".intercalate (log.entries.map (·.message)).toList}"

/-- The text of a Lake option's value: the string, `true` or `false`, or the numeral. -/
def optionText : LeanOptionValue → String
  | .ofString s => s
  | .ofBool b => toString b
  | .ofNat n => toString n

/-- The option that the text `name=value` of a `-D` argument sets, when its name is a nonempty
name without whitespace. -/
def dOption? (text : String) : Option (Name × String) :=
  match text.splitOn "=" with
  | name :: value :: more =>
    if name.isEmpty || name.any Char.isWhitespace then none
    else some (name.toName, "=".intercalate (value :: more))
  | _ => none

/-- The `-D` options of a list of Lean arguments, and every other argument: an argument
`-Dname=value`, or `-D` followed by `name=value`, is an option, and every other argument is kept
whole as an extra. -/
def splitArgs : List String → List (Name × String) × List String
  | "-D" :: arg :: rest =>
    let (options, extras) := splitArgs rest
    match dOption? arg with
    | some o => (o :: options, extras)
    | none => (options, "-D" :: arg :: extras)
  | arg :: rest =>
    let (options, extras) := splitArgs rest
    match (if arg.startsWith "-D" then dOption? (arg.drop 2).toString else none) with
    | some o => (o :: options, extras)
    | none => (options, arg :: extras)
  | [] => ([], [])

/-- The target of a library as Lake configures it, with `modules` the modules Lake builds for it. -/
def targetOf (ws : Lake.Workspace) (lib : Lake.LeanLib) (kind : TargetKind) (name : Name)
    (modules : List Name) : Target :=
  let (dOptions, args) := splitArgs (lib.weakLeanArgs ++ lib.leanArgs).toList
  { name, kind, modules
    options := lib.leanOptions.values.toList.map (fun (n, v) => (n, optionText v)) ++ dOptions
    extras := args ++ lib.plugins.toList.map (fun t => s!"plugin {t.key}") ++
      lib.dynlibs.toList.map (fun t => s!"dynamic library {t.key}")
    isDefault := ws.root.defaultTargets.contains name }

/-- The root package's library and executable targets. -/
def targets (ws : Lake.Workspace) : IO (List Target) := do
  let mut out := []
  for lib in ws.root.leanLibs do
    let modules ← lib.getModuleArray
    out := out ++ [targetOf ws lib .library lib.name (modules.map (·.name)).toList]
  for exe in ws.root.leanExes do
    out := out ++ [targetOf ws exe.toLeanLib .executable exe.name [exe.root.name]]
  return out

/-- The profile of a claim in the closed input; `compiler-trusting` is not one. -/
def profileOf : Regula.Checker.Policy.Profile → Option Profile
  | .kernelOnly => some .kernelOnly
  | .choiceFree => some .choiceFree
  | .standardLogical => some .standardLogical
  | .compilerTrusting => none

/-- The claim of `foundation_manifest.json` at the root `dir`, read by `Manifest.parse`: each
claimed library and executable with its surface's profile and execution mode, and each excluded
one. -/
def claim (dir : FilePath) : IO (List Entry) := do
  let path := Regula.Checker.Manifest.defaultPath dir
  let text ← try IO.FS.readFile path catch e =>
    refuse s!"the claim {path} cannot be read: {e}"
  let manifest ← match Regula.Checker.Manifest.parse path.toString text with
    | .ok m => pure m
    | .error why => refuse s!"the claim {path} is refused: {why}"
  let name := Regula.Checker.Manifest.targetIdentity
  let mut out := []
  for s in manifest.surfaces do
    let some p := profileOf s.claim
      | refuse s!"the claim of {s.library} is compiler-trusting, which the checker does not check"
    let execution : Execution := match s.execution with
      | .report => .report
      | .checked => .checked
    for t in #[s.library] ++ s.executables do
      out := out ++ [{ target := name t, classification := .claimed p execution }]
  for l in manifest.excludedLibraries do
    out := out ++ [{ target := name l.library, classification := .excluded }]
  for x in manifest.excludedExecutables do
    out := out ++ [{ target := name x.executable, classification := .excluded }]
  return out

/-- Whether `path` lies below the directory `dir`, by their components. -/
def below (dir path : FilePath) : Bool :=
  let parts (p : FilePath) := p.normalize.components.filter (!·.isEmpty)
  (parts dir).isPrefixOf (parts path) && parts dir != parts path

/-- What the loader reads of one module of the root package: its record, and every constant name
it declares. -/
structure ModuleFile where
  /-- The record of the module. -/
  record : ModuleRecord
  /-- Each constant name that its `.olean` files declare. -/
  declares : Array Name

/-- The record of module `m` from its `.olean` files at `olean`: the exported part, and the server
and private parts when it is a `module`. A read that fails refuses. -/
def readModule (m : Name) (olean : FilePath) : IO ModuleFile := do
  let refused {α : Type} (e : IO.Error) : IO α :=
    refuse s!"the .olean files of module {m} cannot be read: {e}"
  let first ← try readModuleDataParts #[olean] catch e => refused e
  let some (main, _) := first[0]? | refuse s!"the .olean of module {m} has no data"
  let parts ← if main.isModule then
      try readModuleDataParts #[olean, OLeanLevel.server.adjustFileName olean,
          OLeanLevel.private.adjustFileName olean]
      catch e => refused e
    else pure first
  let extensions := parts.foldl (init := ([] : List Name)) fun acc (data, _) =>
    data.entries.foldl (init := acc) fun acc (ext, entries) =>
      if entries.isEmpty || acc.contains ext then acc else acc ++ [ext]
  let declares := (parts.back?.map (·.1.constNames)).getD #[]
  return { record := { name := m, imports := (main.imports.map (·.module)).toList, extensions }
           declares }

/-- The modules of the root package that Lake builds for the targets `ts`: each module of a
target, whose `.olean` must lie in the root package's build, and each module of the root package
that their imports reach. Lean's search path must be Lake's. -/
def rootModules (ws : Lake.Workspace) (ts : List Target) : IO (NameMap ModuleFile) := do
  let rootDir := ws.root.leanLibDir
  let mut files : NameMap ModuleFile := {}
  let mut work : List (Name × Bool) := ts.flatMap fun t => t.modules.map (·, true)
  while true do
    let (m, ofTarget) :: rest := work | break
    work := rest
    if files.contains m then continue
    let olean ← try findOLean m catch e =>
      if ofTarget then refuse s!"the module {m} of a target has no .olean on Lake's search \
        path: {e}" else throw e
    unless below rootDir olean do
      if ofTarget then
        refuse s!"the module {m} of a target has its .olean at {olean}, outside the root \
          package's build {rootDir}"
      continue
    let file ← readModule m olean
    files := files.insert m file
    work := file.record.imports.map (·, false) ++ work
  return files

/-- The modules of the root package that `m` reaches through imports, `m` included. -/
def reachOf (files : NameMap ModuleFile) (m : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := [m]
  while true do
    let n :: rest := work | break
    work := rest
    if seen.contains n then continue
    let some file := files.find? n | continue
    seen := seen.insert n
    work := file.record.imports ++ work
  return seen

/-- One environment that the loader imports: its modules, the modules of the root package they
reach, and the module that declares each name those declare. -/
structure Group where
  /-- The modules that the environment imports. -/
  imports : Array Name := #[]
  /-- The modules of the root package that they reach. -/
  reach : NameSet := {}
  /-- The module that declares each name that those modules declare. -/
  owner : NameMap Name := {}

/-- The group with `m` added, when no module of the root package that `m` reaches declares a name
that another module of the group declares. -/
def Group.add? (g : Group) (files : NameMap ModuleFile) (m : Name) : Option Group := do
  let mut g := g
  for x in (reachOf files m).toList do
    if g.reach.contains x then continue
    let some file := files.find? x | continue
    for c in file.declares do
      if let some y := g.owner.find? c then
        if y != x then failure
      g := { g with owner := g.owner.insert c x }
    g := { g with reach := g.reach.insert x }
  return { g with imports := g.imports.push m }

/-- The environments of a run: the root of each executable alone, and the other modules of the
library targets in as few groups as hold them (`Group.add?`). -/
def groups (files : NameMap ModuleFile) (ts : List Target) : IO (List Group) := do
  let roots := (ts.filter (·.kind == .executable)).flatMap (·.modules)
  let mut out : List Group := []
  for r in roots do
    let some g := ({} : Group).add? files r
      | refuse s!"the modules that the executable root {r} imports declare one name twice"
    out := out ++ [g]
  let mut libs : List Group := []
  for t in ts.filter (·.kind == .library) do
    for m in t.modules do
      if (out ++ libs).any (·.reach.contains m) then continue
      let mut placed := false
      let mut next := []
      for g in libs do
        if !placed then
          if let some g' := g.add? files m then
            next := next ++ [g']
            placed := true
            continue
        next := next ++ [g]
      libs := next
      unless placed do
        let some g := ({} : Group).add? files m
          | refuse s!"the modules that the module {m} imports declare one name twice"
        libs := libs ++ [g]
  return out ++ libs

/-- The kind of a constant: its `ConstantInfo` constructor. -/
def kindOf : ConstantInfo → Kind
  | .axiomInfo _ => .axiom
  | .defnInfo _ => .definition
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .quotInfo _ => .quotient
  | .inductInfo _ => .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor

/-- The constants a constant mentions, as `Lean.collectAxioms` walks them: the type and value of a
definition, theorem or opaque constant, the type of an axiom, constructor or recursor, the type and
constructors of an inductive type, and nothing of a quotient (`Lean/Util/CollectAxioms.lean`). -/
def usesOf (info : ConstantInfo) : Array Name :=
  let all := match info with
    | .axiomInfo v => v.type.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .quotInfo _ => #[]
    | .ctorInfo v => v.type.getUsedConstants
    | .recInfo v => v.type.getUsedConstants
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  all.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]

/-- The body of `e` under its binders of functions. -/
def lambdaBody : Expr → Expr
  | .lam _ _ b _ => lambdaBody b
  | .mdata _ b => lambdaBody b
  | e => e

/-- The decision kind of a contract's condition, and the constants its specification and its
acceptance predicate mention. The condition is `Decides accepts spec`, `DecidesSoundly accepts spec`
or `DecidesCompletely accepts spec`, possibly under a function binder and applied to a form of the
implementation, whose constants count as the acceptance predicate's. -/
def decisionOf (condition : Expr) : ContractKind × List Name × List Name :=
  let body := lambdaBody condition
  let args := body.getAppArgs
  let kind : ContractKind :=
    if body.isAppOf ``Regula.Decides then .decides
    else if body.isAppOf ``Regula.DecidesSoundly then .decidesSoundly
    else if body.isAppOf ``Regula.DecidesCompletely then .decidesCompletely
    else .other
  match kind, args[2]?, args[3]? with
  | .other, _, _ => (.other, [], [])
  | k, some accepts, some spec =>
    let more := (args.extract 4 args.size).flatMap (·.getUsedConstants)
    (k, spec.getUsedConstants.toList, (accepts.getUsedConstants ++ more).toList)
  | _, _, _ => (.other, [], [])

/-- The contract that the theorem `thm` of type `type` states, when its type, under its binders,
is `ExecutableContract implementation condition`. -/
def contractOf (thm : Name) (type : Expr) : Option Contract := do
  let body := type.getForallBody.consumeMData
  guard (body.isAppOfArity ``Regula.ExecutableContract 3)
  let args := body.getAppArgs
  let impl := args[1]!.consumeMData
  let (kind, spec, accept) := decisionOf args[2]!
  return { theorem_ := thm, impl := impl.getAppFn.consumeMData.constName?.getD .anonymous
           fixedArgs := impl.getAppNumArgs, kind, spec, accept }

/-- The correspondence that the theorem `thm` of type `type` states, when its type is `@f = @g`
for constants `f` and `g`. -/
def correspondenceOf (thm : Name) (type : Expr) : Option Correspondence := do
  let t := type.consumeMData
  guard (t.isAppOfArity ``Eq 3)
  let .const f _ := t.appFn!.appArg!.consumeMData | none
  let .const g _ := t.appArg!.consumeMData | none
  return { reference := f, runs := g, theorem_ := thm }

/-- Whether the value `value` of a definition is a field's projection function: under its binders,
the primitive projection of its last binder. The test reads the kernel-checked value, not Lean's
record of projection functions. -/
def projectionValue (value : Expr) : Bool :=
  go value false
where
  /-- The test under the binders opened so far: `bound` when there is one. -/
  go : Expr → Bool → Bool
    | .lam _ _ body _, _ => go body true
    | .mdata _ e, bound => go e bound
    | .proj _ _ (.bvar 0), bound => bound
    | _, _ => false

/-- Whether a constant is a Boolean test: its type, under its binders, is `Bool` or `BEq _`, and
it is no field's projection function (`projectionValue`). A projection reads a field of data,
which no definition of the project computes, so the two sides of a contract that read one field
share no test. -/
def boolTest (info : ConstantInfo) : Bool :=
  let r := info.type.getForallBody.consumeMData
  (r.isConstOf ``Bool || r.isAppOf ``BEq) && !(info.value?.map projectionValue).getD false

/-- The constants that the compiled code of `n` calls, the code of each auxiliary definition that
the compiler adds and that is no constant of `env` counted as code of `n`
(`IR.findEnvDecl`, `IR.collectUsedDecls`). A name with no constant and no code is kept: it is code
that the input cannot resolve. -/
def compiledOf (env : Environment) (n : Name) : Array Name := Id.run do
  let some decl := IR.findEnvDecl env n | return #[]
  let mut out : Array Name := #[]
  let mut seen : NameSet := NameSet.empty.insert n
  let mut work := (IR.collectUsedDecls env [decl]).toList
  while true do
    let c :: rest := work | break
    work := rest
    if seen.contains c then continue
    seen := seen.insert c
    if env.contains c then
      out := out.push c
    else match IR.findEnvDecl env c with
      | some aux => work := (IR.collectUsedDecls env [aux]).toList ++ work
      | none => out := out.push c
  return out

/-- A replacement that a module registers: `@[implemented_by]`, or a `@[csimp]` lemma, with the
module's place in the toolchain. -/
structure Replacement where
  /-- The constant that the kernel value has. -/
  reference : Name
  /-- The constant that compiled code runs in its place. -/
  runs : Name
  /-- Whether a module of the toolchain's library registers it. -/
  inToolchain : Bool
  /-- The `@[csimp]` lemma, for a `@[csimp]` replacement. -/
  lemma? : Option Name

/-- What the loader knows of one loaded environment. -/
structure Facts where
  /-- The loaded environment. -/
  env : Environment
  /-- Whether each module, by its index, lies in the toolchain's library. -/
  inToolchain : Array Bool
  /-- The claimed modules. -/
  claimed : NameSet
  /-- The modules of the root package. -/
  root : NameSet
  /-- Each replacement a loaded module registers, by the constant it runs. -/
  byRuns : NameMap (List Replacement)

/-- The module whose `.olean` holds constant `n`. -/
def Facts.moduleOf (f : Facts) (n : Name) : Option Name :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.env.header.moduleNames[idx.toNat]?

/-- Whether constant `n` is a constant of the toolchain's library. -/
def Facts.toolchain (f : Facts) (n : Name) : Bool :=
  ((f.env.getModuleIdxFor? n).bind fun idx => f.inToolchain[idx.toNat]?).getD false

/-- The facts of `env`: where each module's `.olean` lies, and each replacement each module
registers, read from the module entries of `implementedByAttr` and `CSimp.ext`. -/
def facts (env : Environment) (toolchainDir : FilePath) (claimed root : NameSet) : IO Facts := do
  let mut inToolchain := #[]
  for m in env.header.moduleNames do
    let olean ← try findOLean m catch e => refuse s!"the module {m} was loaded and has no \
      .olean on Lake's search path: {e}"
    inToolchain := inToolchain.push (below toolchainDir olean)
  let mut byRuns : NameMap (List Replacement) := {}
  for idx in [0:env.header.moduleNames.size] do
    let tc := inToolchain[idx]!
    let mut here : Array Replacement := #[]
    for (reference, runs) in Compiler.implementedByAttr.ext.getModuleEntries env idx do
      here := here.push { reference, runs, inToolchain := tc, lemma? := none }
    for e in Compiler.CSimp.ext.ext.getModuleEntries env idx do
      let e := match e with
        | .global e => e
        | .scoped _ e => e
      here := here.push { reference := e.fromDeclName, runs := e.toDeclName, inToolchain := tc,
                          lemma? := some e.thmName }
    for r in here do
      byRuns := byRuns.insert r.runs (r :: (byRuns.find? r.runs).getD [])
  return { env, inToolchain, claimed, root, byRuns }

/-- The name of the recursion helper of `n`, when the environment holds one. -/
def Facts.helper? (f : Facts) (n : Name) : Option Name :=
  let h := Name.str n "_unsafe_rec"
  if f.env.contains h then some h else none

/-- The constant `n` as the closed input states it. -/
def Facts.decl (f : Facts) (n : Name) (info : ConstantInfo) : Decl :=
  let env := f.env
  let compiled := compiledOf env n
  let implementedBy := Compiler.getImplementedBy? env n
  let own := (implementedBy.toList ++ (f.helper? n).toList).map fun runs =>
    ({ reference := n, runs, inToolchain := f.toolchain n } : Departure)
  let atCalls := compiled.toList.flatMap fun g => ((f.byRuns.find? g).getD []).filterMap fun r =>
    if r.reference == g then none
    else some ({ reference := r.reference, runs := g, inToolchain := r.inToolchain } : Departure)
  { name := n, module := (f.moduleOf n).getD .anonymous, kind := kindOf info
    isUnsafe := info.isUnsafe, isPartial := info.isPartial, uses := (usesOf info).toList
    axioms := none
    implementedBy, compiled := compiled.toList, departures := own ++ atCalls
    isExtern := isExtern env n, isInitialized := (getInitFnNameFor? env n).isSome
    isNoncomputable := isNoncomputable env n, isBoolTest := boolTest info
    inToolchain := f.toolchain n }

/-- The environment as the one state that `Lean.collectAxioms` reads. -/
local instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv f := modify f

/-- The transitive axiom set of constant `n` in `env`, as `Lean.collectAxioms` computes it, in the
order it returns. The loader imports each environment with `loadExts := false`, so the table of
axioms that Lean records for each module (`exportedAxiomsExt`) keeps its initial, empty state
(`Lean/Environment.lean:2404` and `2428-2433` at v4.35.0), and `collectAxioms` walks the type and
value of each constant that `n` reaches, as `usesOf` lists them (`Lean/Util/CollectAxioms.lean` at
v4.35.0). Each call starts from an empty cache, so its answer for `n` holds every axiom that `n`
reaches: a constant that the walk meets again while it is on the walk's stack adds nothing there,
but its whole set reaches `n` through the constants below `n` on the stack. -/
def axiomsIn (env : Environment) (n : Name) : List Name :=
  ((collectAxioms n : StateM Environment (Array Name)).run' env).toList

/-- The axiom set of each constant of `names` in `env` (`axiomsIn`). The walks are independent, so
they run in tasks of Lean's task manager, a slice of `names` to each task; every task ends before
the table is returned, so none reads `env` after its caller frees it. -/
def axiomTable (env : Environment) (names : Array Name) : NameMap (List Name) :=
  let slice := max 1 ((names.size + 63) / 64)
  let tasks := (List.range ((names.size + slice - 1) / slice)).map fun k =>
    Task.spawn fun _ => (names.extract (k * slice) ((k + 1) * slice)).map fun n =>
      (n, axiomsIn env n)
  tasks.foldl (fun table task => task.get.foldl (fun table (n, axs) => table.insert n axs) table)
    {}

/-- The axiom sets that the loader computed, by the module of the constant and the constant. A
constant's set depends only on the constants of its module's import closure, which each
environment of a run loads from the same `.olean` files, so an environment reuses the set that an
earlier one computed. The key holds the module, because two environments can hold two constants of
one name, such as the `main` of two programs. -/
abbrev AxiomSets := Std.HashMap (Name × Name) (List Name)

/-- The constants the rules can reach from `seeds`: the seeds, each constant a constant of the set
mentions, and, from `runs`, the execution closure: each constant that compiled code of a constant
of it runs, with the code its departures run. -/
def Facts.closure (f : Facts) (seeds runs : List Name) (known : NameMap Decl) : NameMap Decl :=
  Id.run do
  let mut out := known
  let mut executed : NameSet := {}
  let mut work : List (Name × Bool) := seeds.map (·, false) ++ runs.map (·, true)
  while true do
    let (n, exec) :: rest := work | break
    work := rest
    if out.contains n && (!exec || executed.contains n) then continue
    let some info := f.env.find? n | continue
    let d := (out.find? n).getD (f.decl n info)
    out := out.insert n d
    work := d.uses.map (·, false) ++ work
    if exec then
      executed := executed.insert n
      work := (d.compiled ++ d.departures.map (·.runs)).map (·, true) ++ work
  return out

/-- The closed input of the environment that `f` describes, for the project's targets `ts`,
claim `manifest` and module records `records`. `known` holds the axiom sets that the environments
loaded before this one computed, by module and constant (`AxiomSets`). -/
def Facts.input (f : Facts) (ts : List Target) (manifest : List Entry)
    (records : List ModuleRecord) (known : AxiomSets := {}) : Input := Id.run do
  let env := f.env
  let mut seeds : List Name := []
  let mut lemmas : List Correspondence := []
  for (n, info) in env.constants.map₁.toList do
    let some m := f.moduleOf n | continue
    if f.claimed.contains m then seeds := n :: seeds
    if f.root.contains m then
      if let .thmInfo v := info then
        if let some c := correspondenceOf n v.type then lemmas := c :: lemmas
  for (_, rs) in f.byRuns.toList do
    for r in rs do
      if let some thm := r.lemma? then
        lemmas := { reference := r.reference, runs := r.runs, theorem_ := thm } :: lemmas
  let mains := if env.contains `main then [`main] else []
  let first := f.closure seeds mains {}
  -- The correspondences that a departure of the input needs, with their theorems' closure.
  let needed : Std.HashSet (Name × Name) := first.foldl (init := {}) fun s _ d =>
    d.departures.foldl (fun s x => s.insert (x.reference, x.runs)) s
  let proved := lemmas.filter fun c => needed.contains (c.reference, c.runs)
  let all := f.closure (proved.map (·.theorem_)) [] first
  -- The axiom sets that the rules read: those of the constants of claimed modules (RG1001 to
  -- RG1005) and of the theorems that state a correspondence (RG3002).
  let theorems : NameSet := proved.foldl (fun s c => s.insert c.theorem_) {}
  let reads (d : Decl) : Bool := f.claimed.contains d.module || theorems.contains d.name
  let fresh := all.foldl (init := #[]) fun acc n d =>
    if reads d && !known.contains (d.module, n) then acc.push n else acc
  let table := axiomTable env fresh
  let decls := all.toList.map fun (_, d) =>
    { d with axioms := if reads d then
        (table.find? d.name).orElse fun _ => known[(d.module, d.name)]? else none }
  let mut decisions : List Name := []
  for idx in [0:env.header.moduleNames.size] do
    unless f.claimed.contains env.header.moduleNames[idx]! do continue
    for n in Regula.decisionExtension.getModuleEntries env idx do
      unless decisions.contains n do decisions := decisions ++ [n]
  let decidableResults := decisions.filter fun n =>
    (env.find? n).any (·.type.getForallBody.consumeMData.isAppOf ``Decidable)
  let contracts := decls.filterMap fun d =>
    if d.kind == .theorem && f.claimed.contains d.module then
      (env.find? d.name).bind (contractOf d.name ·.type)
    else none
  return { targets := ts, manifest, modules := records, decls
           loads := env.header.moduleNames.toList, contracts, decisions, decidableResults, proved }

/-- A copy of `n` made of new objects, none of them in an `.olean`'s data. -/
def freshName : Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (freshName p) (String.ofList s.toList)
  | .num p k => .num (freshName p) (k + 0)

/-- Copying names out of an environment's data, each distinct name once. -/
abbrev CopyM := StateT (Std.HashMap Name Name) IO

/-- The copy of `n`. -/
def copy (n : Name) : CopyM Name := do
  if let some c := (← get)[n]? then return c
  let c := freshName n
  modify (·.insert n c)
  return c

/-- The copy of each name of a list. -/
def copyAll (ns : List Name) : CopyM (List Name) := ns.mapM copy

/-- The input `i` with each name that came from an environment copied, so that nothing of it
lies in that environment's `.olean` data. The targets, the claim and the module records come
from Lake, the claim's file and reads of their own, so they are kept. -/
def copyInput (i : Input) : CopyM Input := do
  let decls ← i.decls.mapM fun d => do
    let departures ← d.departures.mapM fun x => do
      return { x with reference := ← copy x.reference, runs := ← copy x.runs }
    return { d with
      name := ← copy d.name, module := ← copy d.module, uses := ← copyAll d.uses
      axioms := ← d.axioms.mapM copyAll, implementedBy := ← d.implementedBy.mapM copy, compiled := ← copyAll d.compiled
      departures }
  let contracts ← i.contracts.mapM fun k => do
    return { k with
      theorem_ := ← copy k.theorem_, impl := ← copy k.impl
      spec := ← copyAll k.spec, accept := ← copyAll k.accept }
  let proved ← i.proved.mapM fun c => do
    return {
      reference := ← copy c.reference, runs := ← copy c.runs
      theorem_ := ← copy c.theorem_ }
  return { i with
    decls, loads := ← copyAll i.loads, contracts
    decisions := ← copyAll i.decisions, decidableResults := ← copyAll i.decidableResults
    proved }

/-- How the caller selects the workspace: Lake's dispatch, or an explicit directory. -/
inductive WorkspaceSelection where
  /-- The current directory, admitted only when Lake dispatched its workspace. -/
  | dispatched
  /-- The directory the caller explicitly selected. -/
  | named (dir : FilePath)

/-- The directory selected by the caller, before filesystem resolution. -/
def WorkspaceSelection.directory : WorkspaceSelection → FilePath
  | .dispatched => "."
  | .named dir => dir

/-- Whether `root` is the last workspace library directory before Lake's library in the
received search path. Lake v4.35.0 `Package.lint` runs the driver without changing its directory
(`Lake/CLI/Actions.lean`), and `Workspace.augmentedLeanPath` supplies workspace libraries, then
the collocated Lake library, then inherited entries. The root package is first in Lake's package
array, so `Workspace.leanPath` puts its library last.

Assumes: Lake supplies that composition; its library is not a workspace library; and distinct
packages do not configure a shared library directory. Under those assumptions the theorem below
identifies the dispatching root, whatever search path the caller inherited. -/
def dispatchedFrom (root lakeLib : String) (leanPath : List String) : Bool :=
  decide ((leanPath.takeWhile (· ≠ lakeLib)).getLast? = some root) &&
    decide (lakeLib ∈ leanPath)

/-- For every search path of Lake's composition, the dispatch check accepts exactly the last
workspace library directory. Inherited entries cannot make a different root pass. -/
theorem dispatchedFrom_iff {root lakeLib : String} {dispatching inherited : List String}
    (h : lakeLib ∉ dispatching) :
    dispatchedFrom root lakeLib (dispatching ++ lakeLib :: inherited) = true ↔
      dispatching.getLast? = some root := by
  have hall : ∀ a ∈ dispatching, decide (a ≠ lakeLib) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    exact fun hal => h (hal ▸ ha)
  have htake : (dispatching ++ lakeLib :: inherited).takeWhile (fun a => decide (a ≠ lakeLib)) =
      dispatching := by
    rw [List.takeWhile_append_of_pos hall]
    simp
  simp only [dispatchedFrom, htake, Bool.and_eq_true, decide_eq_true_eq]
  simp

/-- The closed input of the selected finished build, or an error that refuses it. An implicit
selection must match Lake's dispatch (`dispatchedFrom_iff`). Each environment is imported, read
into the input, copied out of its data, and freed before the next one is imported. -/
unsafe def loadBundle (selection : WorkspaceSelection) : IO Bundle := do
  let dir := selection.directory
  let ws ← loadWorkspace dir
  match selection with
  | .dispatched =>
    let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
    unless dispatchedFrom ws.root.leanLibDir.toString ws.lakeEnv.lake.libDir.toString
        received do
      refuse "the current directory is not the workspace Lake dispatched; run `lake lint` \
        from that workspace's directory"
  | .named _ => pure ()
  searchPathRef.set ws.augmentedLeanPath
  let ts ← targets ws
  let manifest ← claim dir
  let files ← rootModules ws ts
  let records := files.toList.map (·.2.record)
  let claimedTargets := manifest.filterMap fun e => match e.classification with
    | .claimed .. => some e.target
    | .excluded => none
  let claimed : NameSet := ts.foldl (init := {}) fun s t =>
    if claimedTargets.contains t.name then t.modules.foldl (·.insert ·) s else s
  let root : NameSet := files.foldl (fun s m _ => s.insert m) {}
  let mut envs := []
  let mut known : AxiomSets := {}
  for g in ← groups files ts do
    let env ← try importModules (g.imports.map ({ module := · })) {} (loadExts := false)
      catch e => refuse s!"Lean could not load the modules {g.imports.toList}: {e}"
    let f ← facts env ws.lakeEnv.lean.leanLibDir claimed root
    let raw := f.input ts manifest records known
    let input ← (copyInput raw).run' {}
    env.freeRegions
    for d in input.decls do
      if let some axs := d.axioms then known := known.insert (d.module, d.name) axs
    envs := envs ++ [input]
  return { envs }

end Regula.Load
