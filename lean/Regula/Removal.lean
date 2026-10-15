import Regula.Filesystem
import Regula.Process
import Regula.Specialization
import RegulaPolicy.Domain
import Lake.Build.Actions
import Lake.Util.Proc
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr
import Lean.Elab.Command

/-! # The observer reach check of a program

The single table `boundaries` gives the primitives of three external systems: the filesystem's
removals and writes, process starts and environment observations. Each row names the Lean
operations at which the walk stops, the runtime symbols that an `extern` of another name can bind,
and the one module whose declarations may have its observer's role: `Regula.Filesystem` or
`Regula.Process`. The role given in another module admits nothing, and the check of a program
refuses it (`foreignRoles`).

A removal primitive of Lean's library is an operation that removes or replaces an entry
(`primitives`, `removalSymbols`). `filesystemReach` follows the compiled code of a program from
every compiled declaration of the modules it links outside Lean's toolchain, its `main` and the
code that initializes the modules that it links (`rawRemovals`, `initializersOf`). It finds each
call of a removal primitive that a declaration makes other than a declaration of
`Regula.Filesystem` with the filesystem observer's role (`@[regula_observer filesystem]`,
`filesystemObservers`) or a call of Lean's library that `libraryRemovals` or `tacticRemovals`
lists. The observer's removals and its move are private to `Regula.Filesystem`. Its exported
operations `removeOwn`, `removeFound`, `replace` and `withOwnTempDir` observe the place and act only
on what the decisions of `RegulaCore.Removal` decide. `moveAside` moves an entry into a directory
that it makes new, so it replaces and removes nothing, with no `ownPath` resolution and no
`Regula.Removal.replacement` decision: a symbolic link or a `..` among the components above the
entry is followed as the operating system resolves it, as a run of Verso writes through it too.

The same walk finds each call of a primitive that writes a file or makes an entry
(`writePrimitives`, `writeSymbols`). An opening of a file by `IO.FS.Handle.mk` is such a call when
its mode is not the literal `IO.FS.Mode.read` (`opensToWrite`), and a call of any other declaration
bound to its C function always is (`readableOpening`). It admits such a call, as it admits a
removal, only in a declaration with the filesystem observer's role, in the writer of
`Regula.Filesystem` (`writers`), at a call that `libraryWrites`, `tacticWrites` or `packageWrites`
lists, or at a call that the program names to `checkProgram`, each by its source declaration
(`sourceDeclaration`). A call in code that Lean's compiler made in one declaration and may give to
others, a specialization, a lifted lambda or a closed term (`auxiliarySource`), is the call of each
declaration that reaches that code from outside the code of the one that made it too, and is
admitted only when it is admitted for each of them (`attributions`). So a later declaration that
reuses the specialization of a named caller is not admitted by that caller's pair. A pair that a
program names and that admits no call fails the check, so the list of each program is exact.

The process and environment rows are decided on the path (`pathReach`). Their walk starts at the
program's `main` and the initializer actions of the modules that it links (`initActionsOf`), and
follows the compiled code in a context (`PathContext`). A start or a read is admitted in a
declaration of `Regula.Process` with its row's observer role, below a listed public library entry
as that entry admits (`Entry`), on a path from an initializer of the toolchain's modules for its
row's startup pairs, or in the copy of the process source that a driver which cannot import
`Regula.Process` elaborates (`bootstrap`). A library's process start or environment read on any
other path is refused, whoever owns the module that makes it. The cold drivers elaborate the same
process source as the compiled observer, with no second policy.

`checkProgram` runs the check for the program whose `main` the environment declares, fails the
build of the module that runs it when the check finds a call, and records the program in the
module (`reached`). Each program of the package runs it: at the end of the root module of each
`lean_exe`, or in a module of `Regula.ProgramCheck` that imports a program that `lean --run` runs
and that cannot import this module. `lake exe qualify observers` refuses a program of the package
that no module records, and checks itself the one root that no library module can import,
`auditApp`'s `Main` (`Regula.Qualification.Observers`). It remains in self-audit shard 4/4.

## What the check guarantees

The criterion is honest code, as `SECURITY.md` and `CONTEXT.md` define it: code that does not
deliberately change Lean's environment, compiler or build to make a check pass. Honest code in a
checked program cannot reach a removal outside the observer, except the library removals that
`libraryRemovals` lists, each a trusted exemption of Lake or resting on an assumption, as it states,
the removals of `bv_decide` that `tacticRemovals` lists, trusted active effects of a program that
runs the tactic (see "Programs that elaborate"), and the removals of the two programs that
`scripts/verify.sh` and `scripts/provision.sh` run, which are admitted by name where they are
checked (`Regula.ProgramCheck.Verification`, `Regula.ProgramCheck.Provision`). Deliberate
circumvention by Regula's own authors is outside it
(issue 286), for example a hand-written `extern` bound to a C function of the runtime that removes
other than `removalSymbols`, or a use of the private declarations of `Regula.Filesystem`. Honest
code in a checked program writes a file or makes an entry only at the calls that these lists and
its own list name, each again as a whole for its caller and primitive. It starts a process or
reads the environment only through `Regula.Process`, below a listed entry, on a startup path of
the toolchain or in a driver's copy of the process source, each as its row states.

The check admits a removal or a write of a list or of a driver by the pair of its caller and the
primitive that it calls (`admitted`), not by its path, by the call site in the caller or by the
path through which the program reaches the caller. So each admitted pair is a trusted exception as
a whole. It admits any further call of the same primitive inside the same caller: a second
`IO.FS.removeDirAll` in a removal of the verification driver passes the check. It admits the call
whoever calls the caller, `main`, an initializer or the program's own code: a program that calls
`Lake.Manifest.saveEntries` or `Std.Tactic.BVDecide.LRAT.dumpLRATProof` itself writes where it
asks, admitted by the pair of `libraryWrites` or `tacticWrites`. The caller of a call in code that
the compiler may share between declarations is each declaration that reaches that code
(`attributions`), so a call there is admitted for its caller's pair only while that caller's own
code alone reaches it. Issue 389 tracks deciding the drivers' removals with a decision that a
theorem relates to `RegulaCore.Removal`. A listed process or environment entry admits, on every
path below its call, the pairs of its `below` or, when its `below` is `none`, every primitive of its
row; `some []` admits no pair. Lake's source configuration, builds and dependent programs remain
trusted library behavior.

## Programs that elaborate

The check of a program states whether the program elaborates (`checkProgram`), and fails when the
statement is wrong (`elaborationRefusal`). The statement is about the compiled code that the
program may run: every compiled declaration of the modules that it links outside Lean's toolchain,
and `main` (`programRoots`). Those hold its initializers and the constants that it computes when it
starts. The program elaborates when that code reaches Lean's elaborator (`elaborationEntries`) or a
declaration that makes a write or a removal of a tactic (`tacticWrites`, `tacticRemovals`). This is
conservative reachability in the compiled code, not a proof that elaboration runs: a declaration
that the program never runs counts, and `Lean.IR.collectUsedDecls` collects a constant and a partial
application too, so a reference to an elaborator that the program never calls counts. The compiled
code of Lean's toolchain is followed from those roots, and its own initializers are not roots. Each
registers what its module defines, and the registration of an elaborator or a tactic refers to it,
so a walk of them would reach every tactic in every program that links Lean's elaborator. They are
trusted to run none. A module is the toolchain's by its name, under the hypothesis that
`toolchainModules` states and `lake exe qualify observers` checks.

Nine programs elaborate, and their checks state it: `axiomGate`, `lint`, `ruleExamples`,
`freshChecker`, `docFenceAudit`, `checkerSelftest`, `qualify`, `regula` and `site`. Each elaborates
the Lake configuration of a project when it loads its workspace (`Lake.importConfigFile`). Some also
elaborate the project's modules in Regula's frontend, in their own process or in a worker of
`axiomGate`, or regenerate the recursion of a declaration that they audit, which runs its
`decreasing_by` tactics. Three more state it by the conservative reachability alone: they link code
that elaborates and that their `main` does not run. `ruleExampleQualification`, and the registry
checks that the first acceptance step runs with `lean --run`, link Regula's frontend
(`Regula.Checker.Frontend`) and Lake's loader of a configuration. `regula-markdown` links
`Regula.Collect` through the guard of Lean's task manager (`Regula.TaskManager`, which imports
`Regula.Probe`), where the regeneration of a declaration's recursion runs its `decreasing_by`
tactics. So the check classes every program that starts through that guard as one that
elaborates.

Elaboration runs the commands, terms and tactics of the source, with their effects, as `lake
build` runs them on the same source. They are trusted active effects of the program, which the
check neither finds nor bounds. Such an effect writes or removes what the source or the tactic
names, as the process may, also through a symbolic link and also at a destination of the program:
the writer of `Regula.Filesystem` does not protect a destination against it, as it does not
against `lake build` on the same source. Such are the writes and removals of `bv_decide`, whose
compiled code Lean's library holds, so that the check finds and admits them by their pairs in every
program: the `aig.gv` that its option `graphviz` writes in the working directory, through a
symbolic link there too, the LRAT proof that `bv_decide?` writes beside the source file, and the
temporary files that it removes. In a program that does not elaborate, no compiled declaration of
its modules outside the toolchain reaches them. The initializers of the toolchain reach them by
registering the tactic, which only an elaborator runs.

A program elaborates in the working directory in which it was started. Each worker that a program
of Regula starts runs in the program's working directory or in the project's root, and writes its
packet in a directory that the program made for the run below it: a scratch directory below
`.lake/regula-scratch` (`Regula.Scratch.withScratch`), or `tmp/fence-build` of the workspace of a
documentation audit. So no worker's working directory is the directory of its packet. A
destination of the program that started it may be in that working directory, where an effect of
the elaboration reaches it as above.

## Boundaries

The C functions of the runtime are not followed: `removalSymbols` lists the ones that remove or
replace an entry, `writeSymbols` the ones that write a file or make an entry, and
`environmentSymbols` and the process row the ones that read or change the process environment or
start a process. A new native binding outside these lists needs a sourced entry before this check
can say anything about its effects. A removal or a write by another program that a program starts,
such as `rm`, is not a call that the check finds, nor a write through a handle that an admitted
opening made or that the runtime gave as a standard stream. The check reads the compiled code that
the environment holds; a declaration whose compiled code it does not hold is unknown, and the
check fails, as it does when a walk stops at its bound.

The walk of the process and environment rows starts at `main` and at the initializer actions, not
at every compiled declaration of the program's modules: a value with no parameter that a module
computes when it starts, and that no path from those roots refers to, is outside it. The honest-code
boundary of `SECURITY.md` and `CONTEXT.md` holds here too: deliberate compiler or environment
mutation, private-declaration access and arbitrary trusted plugins remain outside it.

Assumes: this check guards Regula's own executables built from its committed lakefile and
lake-manifest.json. The build configuration, package selection, module naming and artifact loading
are trusted input, not an adversarial authentication claim. Lean v4.34.1 ModuleData stores no
compiled-as module name (Lean/Environment.lean:109-129); imports record the requested name
(:2225-2228) and the environment flattens artifact regions (:2371). Renamed or substituted
artifacts are outside this boundary. Exempted external dependencies must retain the committed
manifest selection; the renderer refuses override selectors before Lake resolves them. -/

namespace Regula.Removal

open Lean IR

/-- The bound on the number of declarations that each walk of `rawRemovalsFrom` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- The removal primitives of Lean's library, each of which removes or replaces a file or a
directory: the three removals, `IO.FS.rename`, which replaces the entry at its destination, and the
three writers of a module. Each file of a module is written to a temporary file, renamed over the
file, and the temporary file is removed when the write fails (`src/library/module.cpp:403` and
`:408`). -/
def primitives : List Name :=
  [``IO.FS.removeFile, ``IO.FS.removeDir, ``IO.FS.removeDirAll, ``IO.FS.rename,
    ``Lean.writeModule, ``Lean.saveModuleData, ``Lean.saveModuleDataParts]

/-- The declarations of Lean's library that write a file or make a directory for their caller,
each through a C function of `writeSymbols`. The check finds a call of one by its name, so it
names the caller, not the declaration of the library. A call of `IO.FS.withFile` is a write
whatever its mode, which the check does not read there; the compiler copies its body into each
caller (`@[inline]`), where the check reads the mode of its opening (`opensToWrite`). -/
def writePrimitives : List Name :=
  [``IO.FS.writeFile, ``IO.FS.writeBinFile, ``IO.FS.createDirAll, ``IO.FS.withFile]

/-- The C functions of the Lean 4.34.1 runtime that write a file or make an entry, by a search of
the `extern` declarations of its library (`src/lean`) for the functions of the filesystem: the
opening of a file (`IO.FS.Handle.mk`), the truncation of an open file (`IO.FS.Handle.truncate`), the
making of a directory (`IO.FS.createDir`) and of a hard link (`IO.FS.hardLink`), and the writes of
LLVM's output. A declaration of any name that is bound to one of them writes. Those not on this
list: `lean_chmod`, which changes the access rights of an entry and not its contents;
`lean_io_create_tempfile` and `lean_io_create_tempdir`, which make an entry at a new name in the
system's temporary directory, so no entry that a program names; and the writes through a handle,
which an opening of `IO.FS.Handle.mk` made or the runtime gave as a standard stream. -/
def writeSymbols : List String :=
  ["lean_io_prim_handle_mk", "lean_io_prim_handle_truncate", "lean_io_create_dir",
    "lean_io_hard_link", "lean_emit_llvm", "lean_llvm_print_module_to_file",
    "lean_llvm_target_machine_emit_to_file", "lean_llvm_write_bitcode_to_file"]

/-- The C function of `writeSymbols` that opens a file in the mode that its second argument
gives (`IO.FS.Handle.mk`). Only the mode `IO.FS.Mode.read`, the number 0, opens it without
writing. -/
def openSymbol : String := "lean_io_prim_handle_mk"

/-- The C functions of the Lean 4.34.1 runtime that remove or replace an entry, by a search of its
sources (`src/runtime`, `src/library`) for `unlink`, `rmdir`, `rename` and `remove`. They are the
functions that `IO.FS.removeFile`, `IO.FS.removeDir` and `IO.FS.rename` are bound to
(`Init/System/IO.lean`), and the one that `Lean.CompactedRegion.save` is bound to, which writes a
module. A declaration of any name that is bound to one of them is a removal primitive. A C function
that writes to a file or makes an entry, without removing or replacing one, is not on this list. -/
def removalSymbols : List String :=
  ["lean_io_remove_file", "lean_io_remove_dir", "lean_io_rename", "lean_compacted_region_save"]

/-- Whether the entry of an `extern` attribute calls the C function `symbol`: by its name, or in
the C text of an inline entry. -/
def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

/-- The C function of `symbols` that `name` is bound to, when it is an `extern` declaration bound
to one. -/
def boundAmong (env : Environment) (symbols : List String) (name : Name) : Option String :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) =>
    symbols.find? fun symbol => data.entries.any (bindsTo symbol)
  | _ => none

/-- The C function of `removalSymbols` that `name` is bound to, when it is an `extern`
declaration bound to one. -/
def boundRemoval (env : Environment) (name : Name) : Option String :=
  boundAmong env removalSymbols name

/-- The C function of `writeSymbols` that `name` is bound to, when it is an `extern` declaration
bound to one. -/
def boundWrite (env : Environment) (name : Name) : Option String :=
  boundAmong env writeSymbols name

/-- What the check reads of a compiled body: each variable that the body binds to a literal
number, with the number, and each call that it makes, with its arguments and whether it is a
partial application. -/
abbrev Calls := Array (VarId × Nat) × Array (Name × Array Arg × Bool)

/-- The facts of two parts of a body, together. -/
def Calls.join (first second : Calls) : Calls :=
  (first.1 ++ second.1, first.2 ++ second.2)

mutual
/-- The facts that the check reads of the compiled body `body` (`Calls`), from each of its
branches and join points. -/
def bodyCalls : FnBody → Calls
  | .vdecl x _ e rest =>
    let (literals, calls) := bodyCalls rest
    match e with
    | .lit (.num n) => (literals.push (x, n), calls)
    | .fap f ys => (literals, calls.push (f, ys, false))
    | .pap f ys => (literals, calls.push (f, ys, true))
    | _ => (literals, calls)
  | .jdecl _ _ v rest => (bodyCalls v).join (bodyCalls rest)
  | .set _ _ _ rest | .setTag _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest
  | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => bodyCalls rest
  | .case _ _ _ alts => altsCalls alts
  | .ret _ | .jmp _ _ | .unreachable => (#[], #[])
/-- The facts of the branches `alts` of a `case`. -/
def altsCalls : Array Alt → Calls
  | ⟨alts⟩ => altListCalls alts
/-- The facts of the branches `alts`, in order. -/
def altListCalls : List Alt → Calls
  | [] => (#[], #[])
  | alt :: rest => (altCalls alt).join (altListCalls rest)
/-- The facts of the body of the branch `alt`. -/
def altCalls : Alt → Calls
  | .ctor _ rest | .default rest => bodyCalls rest
end

/-- The binding of `IO.FS.Handle.mk` whose C call the check has read, as Lean 4.34.1 declares it
(`Init/System/IO.lean:795`): one standard entry for every backend, which calls `openSymbol` with
the arguments of the declaration in order. -/
def readableOpen : ExternAttrData := { entries := [.standard `all openSymbol] }

/-- The compiled parameters of that binding in Lean 4.34.1: the path, borrowed, the mode as one
byte, and the world, which the C function does not take. -/
def readableOpenParams : Array IRType := #[.object, .uint8, .void]

/-- Whether the check reads the mode of a call of `name` (`opensToWrite`): `name` is
`IO.FS.Handle.mk`, bound as `readableOpen` with the parameters `readableOpenParams`, so that its
second argument is the mode that the C function receives. Any other declaration bound to
`openSymbol` opens a file to write it at each call: one with an inline pattern can give the C
function a mode of its own whatever its arguments, and one of another name or with other
parameters has an order of arguments that the check has not read. -/
def readableOpening (env : Environment) (name : Name) : Bool :=
  name == ``IO.FS.Handle.mk && match findEnvDecl env name with
    | some (.extern _ params _ data) =>
      data == readableOpen && params.map (·.ty) == readableOpenParams &&
        (params[0]?.map (·.borrow)).getD false
    | _ => false

/-- Whether the call of `IO.FS.Handle.mk` (`readableOpening`) with the arguments `args` opens a file
to write it: the call is a partial application, or its mode, the second argument, is not a variable
that the body binds to the literal 0 (`IO.FS.Mode.read`), among `literals`. -/
def opensToWrite (literals : Array (VarId × Nat)) (args : Array Arg) (partialCall : Bool) : Bool :=
  match args[1]? with
  | some (Arg.var mode) => partialCall || !literals.contains (mode, 0)
  | _ => true

/-- The calls of `IO.FS.Handle.mk` (`readableOpening`) that the compiled body `body` makes to write
a file (`opensToWrite`), each by its callee. -/
def writingOpens (env : Environment) (body : FnBody) : Array Name :=
  let (literals, calls) := bodyCalls body
  calls.filterMap fun (callee, args, partialCall) =>
    if readableOpening env callee && opensToWrite literals args partialCall then some callee
    else none

/-- The suffixes that Lean's compiler appends to the name of a declaration for the compiled
variants it makes of it: one without its irrelevant arguments, and the boxed form of each. -/
def compilerSuffixes : List Name :=
  [.anonymous, `_redArg, `_boxed, `_redArg ++ `_boxed]

/-- The module whose declarations may have the filesystem observer's role: `Regula.Filesystem`,
whose exported operations remove only what the decisions of `RegulaCore.Removal` decide. -/
def observerModule : Name := `Regula.Filesystem

/-- The module of `env` that declares `name`: the module of the environment's own commands when no
imported module declares it. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- The declarations of `env` with the observer's role of `system`
(`@[regula_observer ...]`, `Regula.Assumption.roles`), split by whether `owner` declares them:
those it declares, and those of every other module. -/
def observerRoles (env : Environment) (system : RegulaPolicy.External.System := .filesystem)
    (owner : Name := observerModule) : Array Name × Array Name :=
  (Regula.Assumption.roles env).foldl (init := (#[], #[])) fun (own, foreign) (name, role) =>
    if role != .observer system then (own, foreign)
    else if moduleOf env name == owner then (own.push name, foreign)
    else (own, foreign.push name)

/-- The filesystem observers that the check admits: the declarations of `observerModule` with the
observer's role (`observerRoles`). A role given in another module admits nothing. -/
def filesystemObservers (env : Environment) : Array Name :=
  (observerRoles env).1

/-- The declarations of other modules than `observerModule` with the filesystem observer's role,
each of which the check of a program refuses (`programRefusal`). -/
def foreignObservers (env : Environment) : Array Name :=
  (observerRoles env).2

/-- Whether `name` is one of `observers` or a compiled variant that the compiler made of one: a
name of `compilerSuffixes` after its name, which is not the name of a declaration that a source
defines. -/
def observerVariant (env : Environment) (observers : Array Name) (name : Name) : Bool :=
  observers.any fun observer => compilerSuffixes.any fun suffix =>
    name == observer ++ suffix && (suffix.isAnonymous || !env.contains name)

/-- The primitives that the check finds by name: those that remove (`primitives`) and those that
write (`writePrimitives`). -/
def watched : List Name := primitives ++ writePrimitives

/-- Whether the check finds a call of `name` as a call of a primitive: `name` is one of `watched`,
or is bound to a C function of `removalSymbols` or, unless `writes` is false, of `writeSymbols`
(`boundRemoval`, `boundWrite`). -/
def isPrimitive (env : Environment) (watched : List Name) (name : Name) (writes : Bool := true) :
    Bool :=
  watched.contains name || (boundRemoval env name).isSome ||
    (writes && (boundWrite env name).isSome)

/-- The primitive that a call of `name` calls, if it calls one (`isPrimitive`): `name` itself, or
the primitive that `name` is a compiled variant of (`observerVariant`), such as the boxed form that
a program calls when it passes the primitive as a value. -/
def calledPrimitive (env : Environment) (watched : List Name) (name : Name)
    (writes : Bool := true) : Option Name :=
  if isPrimitive env watched name writes then some name
  else
    let base := if name matches .str _ "_boxed" then name.getPrefix else name
    let base := if base matches .str _ "_redArg" then base.getPrefix else base
    if base != name && observerVariant env #[base] name && isPrimitive env watched base writes then
      some base
    else none

/-- Whether `component` is a name that Lean's compiler appends to a declaration for a part of its
compiled code: `_redArg`, `_boxed`, or `_lam_`, `_elam_`, `_closed_` or `spec_` with a number. -/
def compiledPart (component : Name) : Bool :=
  match component with
  | .str .anonymous text =>
    text == "_redArg" || text == "_boxed" || ["_lam_", "_elam_", "_closed_", "spec_"].any
      fun stem => text.startsWith stem && text.length > stem.length &&
        (text.toList.drop stem.length).all Char.isDigit
  | _ => false

/-- The name after the last `_at_` of the compiled declaration `name`, a specialization made in
that declaration, without the parts that `compiledPart` names: `D` for the loop
`Array.forIn'Unsafe.loop._at_.D.spec_5` and for the function `D._lam_2`. It reads the name alone,
not the environment, and joins its parts as they stand (`Name.appendCore`): `++` moves the macro
scopes of a hygienic part, and panics when both of its arguments have some. -/
def compiledSource (name : Name) : Name :=
  let made := (name.components.reverse.takeWhile (· != `_at_)).reverse
  (made.reverse.dropWhile compiledPart).reverse.foldl Name.appendCore .anonymous

/-- The declaration of a source in whose compiled code Lean's compiler made the compiled declaration
`name`: `name` when a source declares it, and otherwise its `compiledSource` when a source declares
that. So the loop `Array.forIn'Unsafe.loop._at_.D.spec_5` and the function `D._lam_2` are the code
of `D`. A name of another form is its own. -/
def sourceDeclaration (env : Environment) (name : Name) : Name :=
  if env.contains name then name
  else
    let source := compiledSource name
    if env.contains source then source else name

/-- Whether the compiled declaration `name` is code that Lean's compiler may give to more than one
declaration: a specialization (`spec_`), a lifted lambda (`_lam_`, `_elam_`) or a closed term
(`_closed_`), or a variant `_redArg` or `_boxed` of one, that no source declares. The compiler gives
a specialization to each later declaration that needs the same one, from a cache of every module
that the environment imports (`Lean/Compiler/LCNF/Specialize.lean:416-418`), and a lifted lambda
and a closed term from a cache of the module (`Lean/Compiler/LCNF/LambdaLifting.lean:105`,
`Lean/Compiler/LCNF/ExtractClosed.lean:223-224`). The variants `_redArg` and `_boxed` of a
declaration of a source are its own code, which each caller of the declaration calls, so they are
not such code. -/
def shareable (env : Environment) (name : Name) : Bool :=
  let base := if name matches .str _ "_boxed" then name.getPrefix else name
  let base := if base matches .str _ "_redArg" then base.getPrefix else base
  match base with
  | .str _ part => compiledPart (.mkSimple part) && !env.contains name
  | _ => false

/-- The declaration in whose compiled code Lean's compiler made the compiled declaration `name`
(`sourceDeclaration`), when the compiler may give `name` to other declarations too (`shareable`).
-/
def auxiliarySource (env : Environment) (name : Name) : Option Name :=
  if shareable env name then some (sourceDeclaration env name) else none

/-- The private declaration `name` of `Regula.Checker.Workspace`. -/
def workspace (name : Name) : Name :=
  mkPrivateNameCore `Regula.Checker.Workspace (`Regula.Checker.Workspace ++ name)

/-- The calls of a removal primitive in Lean's library that a program of the package reaches, each
with the declaration that makes it, for Lean 4.34.1. The check admits each of them without
establishing what it removes.

Lake's entries are trusted exemptions. Lake makes these removals and moves itself when a program
loads a workspace or builds in its own process (`Regula.Checker.Workspace`). Each acts on the
workspace that the program asked Lake to load or build, as `lake build` or `lake update` would
there. Its safety rests on that workspace's own contents: its configuration and targets, the clones
of its dependencies and the release archives that it fetches, which its adopter trusts as Lake
does. The same reason holds where a program runs Lake in a copy of a project that it made, such as
`Regula.Checker.Lake.copyProject`'s or the verification driver's: Lake acts on the copy as it would
on the workspace it was given. Regula's shared constructor refuses source links and special entries
and creates only directories and regular files (`Regula.Filesystem.observer_copy`,
`observer_construct`, under their native primitive hypotheses). It places no packages link: an
ordinary load uses a retained manifest and typed dependency path overrides. Thus this exemption
no longer needs a limit for links preserved or placed by Regula's copies. Dependency originals,
Lake-generated entries and deliberately planted diagnostic aliases remain trusted inputs. The
provisioning registration link in the original integration workspace is separate from constructing
a copy. `RegulaProvision.installLinkWith` makes it in a directory that `mkdir` creates, which
refuses an entry already at its place (`RegulaProvision.installLink_refused`).

- `Lake.importConfigFile`, with `IO.FS.removeFile` and with `Lean.writeModule`. Trusted exemption,
  for the reason above: it removes the stale compiled configuration of a package and its trace in
  `.lake/config/<index>`, and writes the new one and its siblings, each through a temporary file
  that it renames over the file and removes when the write fails (`Lake/Load/Lean/Elab.lean:244`,
  `:256` and `:262`, `src/library/module.cpp:311-314`, `:403` and `:408`).
  `Regula.Checker.Workspace.withRootPackage` keeps its own check of `.lake/config/0` too
  (`Regula.Filesystem.requireNoLinkedEntries`).
- `Lake.removeFileIfExists`, `Lake.downloadArtifactCore`, `Lake.download`. Trusted exemption, for
  the reason above: in a build, they remove stale artifacts, their `.hash` files and no-build
  traces, and a downloaded archive before it is fetched again and unpacked into a package's build
  directory (`Lake/Util/IO.lean:23`, `Lake/Build/Common.lean:313-326`,
  `Lake/Build/Package.lean:140-150`, `Lake/Build/Actions.lean:178`, `Lake/Config/Cache.lean:558`).
  Regula's builds turn off Lake's artifact cache
  (`Regula.Checker.Workspace.uncachedWorkspace_unreadable`, `uncachedWorkspace_unwritable`), not
  the fetch of a release archive.
- `Lake.updateGitRepo`, specialized at `Lake.materializeGitRepo`, with `IO.FS.removeDirAll`.
  Trusted exemption, for the reason above: it removes the clone of a dependency,
  `<workspace>/<packages>/<name>`, when a directory is there whose remote is not the dependency's
  URL (`Lake/Load/Materialize.lean:64-82` and `:251-261`). Unless the two are the same text, it
  compares their real paths and reads each failure of `IO.FS.realPath`, whatever its error, as a
  different URL (`:67-70`), so a remote that names an unreadable path is removed too (issue #441).
  The declarations that materialize a Git dependency reach that removal through specializations
  that Lake's compiler shares, so each makes it too (`attributions`): `Lake.Dependency.materialize`,
  its local `materializeGit`, and `Lake.PackageEntry.materialize`
  (`Lake/Load/Materialize.lean:174-260`).
- `Lake.reuseManifest`, specialized at `Lake.Workspace.updateAndMaterializeCore`, with
  `IO.FS.rename`. Trusted exemption, for the reason above: it moves the packages directory that a
  loaded manifest names to the workspace's (`Lake/Load/Resolve.lean:252-283`).
  `Lake.Workspace.updateAndMaterialize` reaches that move through its specialization of
  `Lake.Workspace.updateAndMaterializeCore`, so it makes it too (`Lake/Load/Resolve.lean:551-560`).
  Regula's wrapper of `Lake.loadWorkspace` in `Regula.Checker.Workspace` makes it too: the compiler
  specializes `Lake.loadWorkspace`'s call of `Lake.Workspace.updateAndMaterialize`
  (`Lake/Load/Workspace.lean:61-69`) at the wrapper, so the specialization is the wrapper's code
  (`sourceDeclaration`).

The removals of a tactic of Lean's library are listed apart (`tacticRemovals`). -/
def libraryRemovals : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.removeFile),
    (`Lake.importConfigFile, ``Lean.writeModule),
    (`Lake.removeFileIfExists, ``IO.FS.removeFile),
    (`Lake.downloadArtifactCore, ``IO.FS.removeFile),
    (`Lake.download, ``IO.FS.removeFile),
    (mkPrivateNameCore `Lake.Load.Materialize `Lake.updateGitRepo ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Materialize `Lake.materializeGitRepo ++ `spec_0,
      ``IO.FS.removeDirAll),
    (`Lake.Dependency.materialize, ``IO.FS.removeDirAll),
    (mkPrivateNameCore `Lake.Load.Materialize `Lake.Dependency.materialize.materializeGit,
      ``IO.FS.removeDirAll),
    (`Lake.PackageEntry.materialize, ``IO.FS.removeDirAll),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.reuseManifest ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore ++ `spec_3,
      ``IO.FS.rename),
    (`Lake.Workspace.updateAndMaterialize, ``IO.FS.rename),
    (workspace `loadWorkspace, ``IO.FS.rename)]

/-- The removals of `bv_decide`, a tactic of Lean's library, for Lean 4.34.1: the three variants of
`IO.FS.withTempFile` in its frontends, each of which removes the temporary file that `withTempFile`
made in the system's temporary directory (`Init/System/IO.lean:1353`), holding the problem that it
gives a SAT solver or the proof that the solver writes. The tactic's initializers reach them, so
every program that links the tactic reaches them. The check admits them in every program, as
trusted active effects of a program that runs the tactic, and the class of the program states
whether it may (`elaborationRefusal`): a program that elaborates runs the tactics of the source
that it elaborates. In one that does not, only the initializers of Lean's toolchain reach them, by
registering the tactic, which only an elaborator runs (`programRoots`). -/
def tacticRemovals : List (Name × Name) :=
  [(`IO.FS.withTempFile._at_.Lean.Meta.Tactic.BVDecide.runExternal.spec_3._redArg._lam_0,
      ``IO.FS.removeFile),
    ((`IO.FS.withTempFile._at_._private.Lean.Elab.Tactic.Grind.BVDecide).num 0 ++
        `Lean.Elab.Tactic.Grind.evalBvDecide.spec_1._redArg._lam_0, ``IO.FS.removeFile),
    (`IO.FS.withTempFile._at_.Lean.Elab.Tactic.BVDecide.evalBvDecide.spec_1._redArg._lam_0,
      ``IO.FS.removeFile)]

/-- The writes of the writer of `Regula.Filesystem`, which the check admits in every program: the
opening of the new file beside a destination in `Regula.Filesystem.writeReplacing`, the making of
the directory of a destination in `Regula.Filesystem.ownRoot`, the making of the new directory
into which `Regula.Filesystem.moveAside` moves an entry, in `Regula.Filesystem.runAside`, and the
making of each file and directory of a constructed tree in
`Regula.Filesystem.Construction.writeNew` and `Regula.Filesystem.Construction.createDirectory`.
The last three are exclusive: each fails when anything is at the path, as their assumptions state,
so none of them replaces or writes into an entry. -/
def writers : List (Name × Name) :=
  [(``Regula.Filesystem.writeReplacing, ``IO.FS.Handle.mk),
    (``Regula.Filesystem.ownRoot, ``IO.FS.createDirAll),
    (`Regula.Filesystem.runAside, ``IO.FS.createDir),
    (``Regula.Filesystem.Construction.writeNew, ``IO.FS.Handle.mk),
    (``Regula.Filesystem.Construction.createDirectory, ``IO.FS.createDir)]

/-- The calls of a primitive that writes in Lean's library that a program of the package reaches,
each with the declaration of a source that makes it (`sourceDeclaration`), for Lean 4.34.1. The
check admits each of them without establishing what it writes.

- Lake's writes, a trusted exemption for the reason of Lake's removals in `libraryRemovals`: each
  acts on the workspace that the program asked Lake to load or build, as `lake build` or
  `lake update` would there. They write a compiled configuration and its lock
  (`Lake.importConfigFile`, `Lake/Load/Lean/Elab.lean:180`), a manifest and the overrides of its
  packages (`Lake.Manifest.save`, `Lake.Manifest.saveEntries`, `Lake/Load/Manifest.lean:275` and
  `:308`), the toolchain file of an update (`Lake.Workspace.updateAndMaterializeCore`, and
  `Lake.Workspace.updateAndMaterialize` through its specialization of it,
  `Lake/Load/Resolve.lean:551-560`, and Regula's wrapper of `Lake.loadWorkspace` through the
  specialization of that call at it, as for the move in `libraryRemovals`), and in a build its
  outputs, traces, hashes and metadata, the arguments of a compiler or an archiver, the entries of
  its artifact cache and an unpacked release archive (`Lake/Build/Actions.lean:29`, `:121` and `:186`, `Lake/Build/Common.lean:177`, `:376`,
  `:401`, `:454` and `:648`, `Lake/Build/Library.lean`, whose two facets of a static library share
  compiled code, `:119-124`, `Lake/Config/Cache.lean:183` and `:434`, `Lake/Util/IO.lean:18`,
  `:31`, `:41` and `:70`). Regula's own code also calls `Lake.Manifest.saveEntries` and
  `Lake.Manifest.save`, to write the overrides of the packages and the manifest of a project that
  it made for its run (`Regula.Checker.LintQualification`, `Regula.Qualification.CopyRelocation`),
  which the same pairs admit, as they admit every caller (`admitted`).

The writes of a tactic of Lean's library are listed apart (`tacticWrites`). -/
def libraryWrites : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.Handle.mk),
    (`Lake.importConfigFile, ``IO.FS.Handle.truncate),
    (`Lake.importConfigFile, ``IO.FS.createDirAll),
    (`Lake.Manifest.save, ``IO.FS.writeFile),
    (`Lake.Manifest.saveEntries, ``IO.FS.writeFile),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore,
      ``IO.FS.writeFile),
    (`Lake.Workspace.updateAndMaterialize, ``IO.FS.writeFile),
    (workspace `loadWorkspace, ``IO.FS.writeFile),
    (`Lake.compileLeanModule, ``IO.FS.writeFile),
    (`Lake.mkArgs, ``IO.FS.Handle.mk),
    (`Lake.untar, ``IO.FS.createDirAll),
    (`Lake.BuildMetadata.writeFile, ``IO.FS.writeFile),
    (`Lake.writeFileHash, ``IO.FS.writeFile),
    (`Lake.fetchFileHash, ``IO.FS.writeFile),
    (`Lake.Cache.saveArtifact, ``IO.FS.hardLink),
    (`Lake.restoreArtifact, ``IO.FS.hardLink),
    (`Lake.LeanLib.staticFacetConfig, ``IO.FS.Handle.mk),
    (`Lake.LeanLib.staticExportFacetConfig, ``IO.FS.Handle.mk),
    (`Lake.CacheMap.writeFile, ``IO.FS.Handle.mk),
    (mkPrivateNameCore `Lake.Config.Cache `Lake.Cache.writeOutputsCore, ``IO.FS.writeFile),
    (`Lake.createParentDirs, ``IO.FS.createDirAll),
    (`Lake.writeFileIfNew, ``IO.FS.Handle.mk),
    (`Lake.writeBinFileIfNew, ``IO.FS.Handle.mk),
    (`Lake.copyFile, ``IO.FS.writeBinFile)]

/-- The writes of `bv_decide`, a tactic of Lean's library, for Lean 4.34.1, admitted as its
removals are (`tacticRemovals`):

- the graph of a problem, which `lratBitblaster` writes at `aig.gv` in the working directory of the
  process when the proof sets the option `graphviz`
  (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:75`), with `IO.FS.writeFile`, which follows a
  symbolic link at that name, so that it writes the file at the link's target, a destination of
  the program too;
- the LRAT proof that `bv_decide?` trims, which `dumpLRATProof` writes over the one that the SAT
  solver wrote (`Std/Tactic/BVDecide/LRAT/Parser.lean:420`, `Lean/Elab/Tactic/BVDecide.lean:181`),
  in the directory of the source file that the process elaborates, named after that file, the
  declaration and the position of the tactic (`Lean/Elab/Tactic/BVDecide.lean:113-148`).

Each is outside the protection of the writer of `Regula.Filesystem`, as every effect of an
elaboration is (`Regula.Removal`, "Programs that elaborate"). The SAT solver is a program that the
tactic starts, outside the check. -/
def tacticWrites : List (Name × Name) :=
  [(`Std.Tactic.BVDecide.LRAT.dumpLRATProof, ``IO.FS.writeBinFile),
    (`Lean.Meta.Tactic.BVDecide.lratBitblaster, ``IO.FS.writeFile)]

/-- The writes of Regula's own declarations that more than one program reaches, each with the
declaration of a source that makes it (`sourceDeclaration`). Each writes below a directory that the
program made for its own run, never at a destination that its arguments name:

- the lock of the scratch area, the marker of a scratch directory and the directory, in
  `Regula.Scratch.withScratch`;
- the identity document of an acceptance link, below the scratch directory, which it removes after
  reading its digest, in `Regula.Checker.AcceptanceLink.identity`;
- the directories of the copy's `.lake/build`, which did not exist, where the observer moves the
  retained build output of an acceptance link, in `Regula.Checker.AcceptanceLink.placeRetained`;
- the scratch of a project's fences, below the copy, in
  `Regula.Checker.Documentation.auditBuiltProject`;
- the claim of a memoized history worker's output and the directories of a probe's overlay, below
  the directories of the run, in `Regula.Checker.Environment.historyWorkerOutput` and
  `Regula.Checker.Environment.linkProbeOverlay`;
- the running observer library, with its trace and hash files, in the build directory of a copy of
  Regula's package, in `Regula.Checker.Observer.Snapshot.write`;
- the directory of a module root in the build output of a control's project, in
  `Regula.Checker.exposeToolchainRoot`.

The copies of projects and the sources of the modules that an audit compiles are written by the
shared constructor, whose writes are those of the writer of `Regula.Filesystem` (`writers`). -/
def packageWrites : List (Name × Name) :=
  [(`Regula.Scratch.withScratch, ``IO.FS.Handle.mk),
    (`Regula.Scratch.withScratch, ``IO.FS.createDir),
    (`Regula.Checker.AcceptanceLink.identity, ``IO.FS.writeFile),
    (`Regula.Checker.AcceptanceLink.placeRetained, ``IO.FS.createDirAll),
    (`Regula.Checker.Documentation.auditBuiltProject, ``IO.FS.createDirAll),
    (mkPrivateNameCore `Regula.Checker.Environment
        `Regula.Checker.Environment.historyWorkerOutput, ``IO.FS.Handle.mk),
    (mkPrivateNameCore `Regula.Checker.Environment `Regula.Checker.Environment.linkProbeOverlay,
      ``IO.FS.createDirAll),
    (`Regula.Checker.Observer.Snapshot.write, ``IO.FS.createDirAll),
    (`Regula.Checker.Observer.Snapshot.write, ``IO.FS.writeBinFile),
    (`Regula.Checker.exposeToolchainRoot, ``IO.FS.createDirAll)]

/-- The pair of `pairs` that admits the call of `primitive` by `caller`, if one does: the pair of
`caller`, of the declaration of a source in whose compiled code it is (`sourceDeclaration`), or of
that declaration's name without its private prefix, a private declaration of another module having
no name that a source can write, and `primitive`. -/
def admittingPair (env : Environment) (pairs : List (Name × Name)) (caller primitive : Name) :
    Option (Name × Name) :=
  let source := sourceDeclaration env caller
  let callers := [caller, source] ++ (privateToUserName? source).toList
  pairs.find? fun (named, called) => called == primitive && callers.contains named

/-- The removals and the writes that the check admits in every program: `libraryRemovals`,
`tacticRemovals`, `writers`, `libraryWrites`, `tacticWrites` and `packageWrites`. -/
def sharedPairs : List (Name × Name) :=
  libraryRemovals ++ tacticRemovals ++ writers ++ libraryWrites ++ tacticWrites ++ packageWrites

/-- The filesystem row's admission decision: whether the call of `primitive` by `caller` is a
removal or a write that the check admits, a call by one of `observers` or a compiled variant of one
(`observerVariant`), or a call that a pair of `sharedPairs` or of `named` admits (`admittingPair`).
It does not depend on the path through which the program reaches the call. -/
def admitted (env : Environment) (observers : Array Name) (named : List (Name × Name))
    (caller primitive : Name) : Bool :=
  observerVariant env observers caller ||
    (admittingPair env (sharedPairs ++ named) caller primitive).isSome

/-- A listed public library entry of a process or environment row: a Regula declaration, the
library declaration that it calls, and what a path through that call admits below it. -/
structure Entry where
  /-- The Regula declaration that alone calls `callee`. -/
  caller : Name
  /-- The public library declaration. -/
  callee : Name
  /-- The library caller and primitive pairs admitted below the call, each up to the compiled
  variants of its two declarations; `none` admits every primitive of the row. -/
  below : Option (List (Name × Name))

/-- One system's primitive boundary. -/
structure Boundary where
  /-- The external system whose primitive calls are controlled. -/
  system : RegulaPolicy.External.System
  /-- Lean operations at which traversal stops and checks their caller. -/
  primitives : List Name
  /-- Runtime symbols that a differently named extern can bind. -/
  symbols : List String
  /-- The only module that can supply an observer for this boundary. -/
  observer : Name
  /-- Listed public library entries (`Entry`). -/
  entries : List Entry := []
  /-- Library caller and primitive pairs admitted only on a path from an initializer of a module of
  the toolchain (`toolchainCaller`). -/
  startup : List (Name × Name) := []

/-- The workspace loads of Lake that Regula runs in its own process, each with the private
declaration of `Regula.Checker.Workspace` that alone calls it, with a configuration of its
`loadConfig`, computed by `Regula.Process.lakeEnvironment`. Below them Lake starts Git to clone,
fetch and test a dependency's repository, `curl` (or the program that CURL names) and `tar` to
fetch and unpack a release archive, `lean` to compile a module, and Elan to restart in a
dependency's toolchain. It reads CURL and the variables of `Lake.Env`. Trusted exemption: each
acts on the workspace that the caller asked Lake to load, as `lake build` or `lake update` would
there, and rests on its own configuration and dependencies, which its adopter trusts as Lake does.
Regula's load supplies no lakeArgs for the toolchain restart.
Sources: Lean v4.34.1 `Lake/Load/Workspace.lean:31-67`, `Lake/Load/Resolve.lean:369-430` and
`:587-625`, `Lake/Util/Git.lean:95-100`, `Lake/Util/Proc.lean:29-72`, `Lake/Util/Url.lean:105-150`,
`Lake/Build/Actions.lean:29` and `:174-185`. Each admits every primitive of its row below it. -/
def workspaceEntries : List Entry :=
  [⟨workspace `loadWorkspace, `Lake.loadWorkspace, none⟩,
    ⟨workspace `loadWorkspaceRoot, `Lake.loadWorkspaceRoot, none⟩,
    ⟨workspace `materializeDeps, `Lake.Workspace.materializeDeps, none⟩]

/-- Lake's installation and environment detection, called by `Regula.Process.lakeEnvironment` with
the identity-checked installation (`Regula.Process.lakeSysroot`). Trusted exemption:
`Lake.LeanInstall.get` with `collocated := true` takes the commit from Lake's own build and does
not start the `lean --githash` that its compiled code holds
(`Lake/Config/InstallPath.lean:272-287`).
It reads LEAN_AR, AR, LEAN_CC and CC (`:289-310`), whose values `lakeSysroot` admits first.
`Lake.findElanInstall?` reads ELAN_HOME and ELAN (`:212-225`), and `Lake.Env.compute` reads the
variables of Lake's environment (`Lake/Config/Env.lean:90-215`), as the toolchain's `lake` does.
Each admits every primitive of its row below it. -/
def installationEntries : List Entry :=
  [⟨`Regula.Process.lakeEnvironment, `Lake.LeanInstall.get, none⟩,
    ⟨`Regula.Process.lakeEnvironment, `Lake.findElanInstall?, none⟩,
    ⟨`Regula.Process.lakeEnvironment, `Lake.Env.compute, none⟩]

/-- Lean's search paths and Lake's build runner, each with the Regula declaration that alone calls
it. Trusted exemption, as the `lean` and `lake` commands read the same variables:
`Lean.initSearchPath` at the identity-checked installation reads LEAN_PATH
(`Lean/Util/Path.lean:98-110`). `Lean.getSrcSearchPath` reads LEAN_SRC_PATH and the directory of
the running executable (`:137-143`, `Init/System/IO.lean:1305-1309`). `Lake.Workspace.runBuild`
reads MACOSX_DEPLOYMENT_TARGET on macOS (`Lake/Build/Run.lean:335-349`, `:427-435`). The build
function is its caller's, so the reach check follows it from that caller. Each admits every
primitive of its row below it. -/
def searchPathEntries : List Entry :=
  [⟨`Regula.Process.initSearchPath, `Lean.initSearchPath, none⟩,
    ⟨`Regula.Process.srcSearchPath, `Lean.getSrcSearchPath, none⟩,
    ⟨`Regula.Checker.Workspace.runBuild, `Lake.Workspace.runBuild, none⟩]

/-- The process start below Verso's renderer: it fetches remote cross-reference data with its fixed
curl command. Trusted exemption: this is the imported library's download mechanism, not a checked
toolchain selection.
Assumes: pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/multi-verso/MultiVerso.lean:398-408` fixes the program to curl and varies its URL and working
directory; `:580-674` selects remote sources from Verso's configuration. -/
def rendererStarts : List (Name × Name) :=
  [(mkPrivateNameCore `MultiVerso `Verso.Multi.fetchRemote, ``IO.Process.output)]

/-- The environment reads below Verso's renderer. Trusted exemption: they admit no other variable
and no tool selection.
Assumes: pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/multi-verso/MultiVerso.lean:384-396` reads the current directory to find the project, from its
own `updateRemotes` (`:580-581`). Lean v4.34.1 `Std/Time/Zoned/Database/TZdb.lean:123-139` and
`:153-158` read only TZ and TZDIR to resolve timezone files. -/
def rendererEnvironment : List (Name × Name) :=
  [(mkPrivateNameCore `MultiVerso `Verso.Multi.findProject, ``IO.currentDir),
    (`Std.Time.Database.TZdb.resolveLocalPath, ``IO.getEnv),
    (`Std.Time.Database.TZdb.resolveZonesPaths, ``IO.getEnv)]

/-- Verso's renderer, `manualMain`, each with the declaration of a renderer's root module that alone
calls it, admitting only the pairs `below` below it: `rendererStarts` in the process row and
`rendererEnvironment` in the environment row. Any other start or read below it is refused. The
renderer refuses override selectors for Verso before Lake resolves them
(`Regula.ProgramCheck.Renderer.requireCommittedSelection`).
Assumes: pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/verso-manual/VersoManual.lean:750`, `:839` and `:1049-1075` connect rendering to those pairs.
The imported library, its configuration and its download behavior remain trusted. -/
def rendererEntries (below : List (Name × Name)) : List Entry :=
  [`renderSite, `renderManual].map (⟨·, `Verso.Genre.Manual.manualMain, some below⟩)

/-- The process start that a path from an initializer of the toolchain reaches: Lean's builtin
`bv_decide`, which the initializer that registers it reaches, starts its SAT solver
(`Lean/Meta/Tactic/BVDecide/External.lean:98-122`). Regula supplies its checked cadical through the
initial `sat.solver` before in-process source elaboration (`Regula.Process.leanOptions`), covering
the default solver only while source leaves that option unset. A source setting it, including
resetting it to empty, selects its own program and remains uncovered (issue 411, after issue 279's
observer). -/
def processStartup : List (Name × Name) :=
  [(`Lean.Meta.Tactic.BVDecide.External.runInterruptible, ``IO.Process.spawn)]

/-- The environment reads that a path from an initializer of the toolchain reaches. The initializer
of `Lean.manualRoot` reads LEAN_MANUAL_ROOT (`Lean/DocString/Links.lean:35-37`). Without a
`sat.solver`, `bv_decide` looks for cadical beside the running executable
(`Lean/Meta/Tactic/BVDecide/TacticContext.lean:55-66`). `Lean.getSrcSearchPath` reads
LEAN_SRC_PATH (`Lean/Util/Path.lean:137-143`), and `IO.appDir`, which it calls to find Lean's
sources, reads the path of the running executable (`Init/System/IO.lean:1305-1309`). -/
def environmentStartup : List (Name × Name) :=
  [(`Lean.manualRoot, ``IO.getEnv),
    (mkPrivateNameCore `Lean.Meta.Tactic.BVDecide.TacticContext
      `Lean.Meta.Tactic.BVDecide.TacticContext.new.determineSolver, ``IO.appPath),
    (`Lean.getSrcSearchPath, ``IO.getEnv),
    (`IO.appDir, ``IO.appPath)]

/-- The runtime symbols of Lean 4.34.1 that read or change the process environment: its variables,
working directory and executable path. Lean binds the first five in `Init/System/IO.lean` (`:951`,
`:955`, `:959`, `:1383` and `:1386`). `Std.Internal.UV.System` binds the others to libuv
(`Std/Internal/UV/System.lean:134-152`, `:170-188` and `:236`). Its only callers are the public
`@[inline]` wrappers of `Std.Async.System` (`Std/Async/System.lean:250-287`) and `Std.IO.Process`
(`Std/Async/Process.lean:156-164` and `:209-210`), so a project call of a wrapper reaches the
binding, inlined or through the wrapper.
Assumes: on POSIX, the toolchain's libuv reads HOME for the home directory and TMPDIR, TMP, TEMP or
TEMPDIR for the temporary directory before any other source, so those two bindings observe
variables. The C bodies are not followed: a variable that a different runtime function reads in C
is outside this list. -/
def environmentSymbols : List String :=
  ["lean_io_getenv", "lean_io_current_dir", "lean_io_process_get_current_dir", "lean_io_app_path",
    "lean_io_process_set_current_dir", "lean_uv_cwd", "lean_uv_chdir", "lean_uv_os_homedir",
    "lean_uv_os_tmpdir", "lean_uv_os_environ", "lean_uv_os_getenv", "lean_uv_os_setenv",
    "lean_uv_os_unsetenv", "lean_uv_exepath"]

/-- The single primitive table: filesystem removals and writes, process starts and environment
observations. The filesystem row is decided by the pairs of its caller and primitive (`admitted`,
`filesystemReach`); the process and environment rows on the path (`pathAdmitted`, `pathReach`). A
wrapper around output or run is controlled at that operation, while an extern alias is controlled
by its runtime binding, as are `Std`'s libuv environment bindings and their public wrappers. A
library's own process start or environment read is admitted only below a listed entry, as that
entry admits, or on a path from the toolchain's initializers. -/
def boundaries : List Boundary :=
  [{ system := .filesystem, primitives := watched, symbols := removalSymbols ++ writeSymbols,
      observer := observerModule },
    { system := .process, primitives := [``IO.Process.spawn, ``IO.Process.output, ``IO.Process.run],
      symbols := ["lean_io_process_spawn"], observer := `Regula.Process,
      entries := workspaceEntries ++ installationEntries ++ rendererEntries rendererStarts,
      startup := processStartup },
    { system := .environment,
      primitives := [``IO.getEnv, ``IO.currentDir, ``IO.Process.getCurrentDir, ``IO.appPath,
        ``IO.Process.setCurrentDir],
      symbols := environmentSymbols, observer := `Regula.Process,
      entries := workspaceEntries ++ installationEntries ++ searchPathEntries ++
        rendererEntries rendererEnvironment,
      startup := environmentStartup }]

/-- The rows of `boundaries` that are decided on the path: every row but the filesystem's. -/
def pathBoundaries : List Boundary :=
  boundaries.filter (·.system != .filesystem)

/-- The declarations with the observer's role of a row of `boundaries` outside the module that the
row names, each with its system, each of which the check of a program refuses
(`programRefusal`). -/
def foreignRoles (env : Environment) : Array (RegulaPolicy.External.System × Name) :=
  boundaries.foldl (fun found boundary =>
    found ++ ((observerRoles env boundary.system boundary.observer).2.map
      fun name => (boundary.system, name))) #[]

/-- The cold-start source's native boundaries, instantiated for the driver module and namespace.
Each driver elaborates the same `ProcessSource.inc`, uses its typed selection and override
decision, and imports no package artifact. They stand for that copy's observers, which cannot carry
the observer's role: admitted on every path, as the observers of `Regula.Process` are, and, like
them, not required to be reached. They are not a second process policy. Their compiler identity
reports, Elan resolution and process effects stay trusted. -/
def bootstrap (scope : Name) : List (Name × Name) :=
  [(scope ++ `identified, ``IO.Process.output),
    (scope ++ `spawn, ``IO.Process.spawn),
    (scope ++ `output, ``IO.Process.output),
    (scope ++ `readEnv, ``IO.getEnv),
    (scope ++ `currentDir, ``IO.currentDir),
    (scope ++ `appPath, ``IO.appPath),
    (scope ++ `setCurrentDir, ``IO.Process.setCurrentDir)]

/-- Index the named primitives of the path rows and their authenticated compiled variants from the
same table. No second primitive list or admission rule is written here. -/
def primitiveIndex (env : Environment) : Std.HashMap Name Boundary := Id.run do
  let mut index := {}
  for boundary in pathBoundaries do
    for primitive in boundary.primitives do
      for suffix in compilerSuffixes do
        let variant := primitive ++ suffix
        if observerVariant env #[primitive] variant then index := index.insert variant boundary
  return index

/-- The path row of a primitive or an extern alias. The compiled declaration is read once, and
the runtime symbol is compared against the same per-system table. -/
def boundaryOf (env : Environment) (index : Std.HashMap Name Boundary) (name : Name) :
    Option Boundary :=
  if let some boundary := index[name]? then some boundary
  else pathBoundaries.find? fun boundary => (boundAmong env boundary.symbols name).isSome

/-- Whether the module that declares `caller` is a module of Lean's toolchain by its name
(`RegulaPolicy.ToolchainRoot`, as `toolchainModules` decides it). A declaration of the environment's
own commands is not.
Assumes: Regula's committed build configuration selects the toolchain's libraries, and module naming
and artifact loading are trusted. Lean v4.34.1 Environment.lean:2225-2228 records the requested
import name, not a certified compiled-as name. This predicate does not authenticate artifacts. -/
def toolchainCaller (env : Environment) (caller : Name) : Bool :=
  match env.getModuleIdxFor? caller with
  | some index => decide (RegulaPolicy.ToolchainRoot env.header.moduleNames[index.toNat]!.getRoot)
  | none => false

/-- Whether the call of `callee` by `caller` is one of `pairs`, each up to the compiled variants of
its two declarations. A first component that has an initializer stands for that initializer. -/
def listed (env : Environment) (pairs : List (Name × Name)) (caller callee : Name) : Bool :=
  pairs.any fun (source, target) =>
    observerVariant env #[(getInitFnNameFor? env source).getD source] caller &&
      observerVariant env #[target] callee

/-- What a path from a root has entered: the systems whose listed entries it passed through, each
with what its entry admits below it (`Entry.below`), and whether it starts at an initializer of the
toolchain (`toolchainCaller`). -/
structure PathContext where
  /-- The systems of the listed entries on the path, each with the pairs that its entry admits. -/
  entered : List (RegulaPolicy.External.System × Option (List (Name × Name))) := []
  /-- Whether the path starts at an initializer of a module of the toolchain. -/
  startup : Bool := false
  deriving BEq, Hashable

/-- Index each specialization that Lean's compiler recorded (`Regula.Specialization.origins`), and
its compiled variants, by the declaration that it specializes, through a specialization of a
specialization. A declaration that a source defines is none of them. -/
def specializationIndex (env : Environment) : Std.HashMap Name Name := Id.run do
  let origins := Regula.Specialization.origins env
  let root (name : Name) : Name := Id.run do
    let mut root := name
    for _ in [:origins.size] do
      let some origin := origins[root]? | break
      root := origin
    return root
  let mut index := {}
  for (specialization, _) in origins do
    for suffix in compilerSuffixes do
      let variant := specialization ++ suffix
      if observerVariant env #[specialization] variant then
        index := index.insert variant (root specialization)
  return index

/-- Index the listed entries by their library declaration and its compiled variants, each with its
row's system. No second entry list is written here. -/
def entryIndex (env : Environment) :
    Std.HashMap Name (List (RegulaPolicy.External.System × Entry)) := Id.run do
  let mut index := {}
  for boundary in pathBoundaries do
    for entry in boundary.entries do
      for suffix in compilerSuffixes do
        let variant := entry.callee ++ suffix
        if observerVariant env #[entry.callee] variant then
          index := index.insert variant ((boundary.system, entry) :: index.getD variant [])
  return index

/-- The context of the call of `callee` by `caller` on a path in `context`: each row that lists the
call as an entry (`entryIndex`) adds its system with what the entry admits below it. A
specialization that the compiler recorded of the entry or of its caller (`specializationIndex`) is
that declaration, made for the caller's arguments. -/
def PathContext.enter (env : Environment)
    (index : Std.HashMap Name (List (RegulaPolicy.External.System × Entry)))
    (specializations : Std.HashMap Name Name) (context : PathContext)
    (caller callee : Name) : PathContext :=
  (index.getD (specializations.getD callee callee) []).foldl (init := context)
    fun context (system, entry) =>
      if !context.entered.any (·.1 == system) &&
          observerVariant env #[entry.caller] (specializations.getD caller caller) then
        { context with entered := context.entered ++ [(system, entry.below)] }
      else context

/-- The admission decision of a path row for a caller and primitive on a path in `context`: the
row's observers, a pair of a driver's copy of the process source (`bootstrap`), a path below a
listed entry of the row as that entry admits, or a startup pair on a path from the toolchain's
initializers. -/
def pathAdmitted (env : Environment) (boundary : Boundary) (observers : Array Name)
    (cold : List (Name × Name)) (context : PathContext) (caller primitive : Name) : Bool :=
  observerVariant env observers caller || listed env cold caller primitive ||
    context.entered.any (fun (system, below) => system == boundary.system &&
      below.all fun pairs => listed env pairs caller primitive) ||
    (context.startup && listed env boundary.startup caller primitive)

/-- The modules that a program whose `main` is in the module `root` links: `root` and each module
that it imports, directly or through another. -/
def linked (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  for h : position in [:env.header.moduleNames.size] do
    index := index.insert env.header.moduleNames[position] position
  let importsOf (module : Name) : Array Name :=
    if module == env.mainModule then env.header.imports.map (·.module)
    else match index[module]? with
      | some position =>
        (env.header.moduleData[position]?.map (·.imports.map (·.module))).getD #[]
      | none => #[]
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut work := #[root]
  for _ in [:env.header.moduleNames.size + 1] do
    let some module := work.back? | break
    work := work.pop
    for imported in importsOf module do
      unless seen.contains imported do
        seen := seen.insert imported
        work := work.push imported
  return seen

/-- The actions that run when a program that links the modules `modules` initializes them: each
declaration of each of them with an `[init]` or `[builtin_init]` attribute when it is the action
that runs, and otherwise the function that computes its value. Each name appears once. -/
def initActionsOf (env : Environment) (modules : Std.HashSet Name) : Array Name := Id.run do
  let current := modules.contains env.mainModule
  let mut roots := #[]
  let mut seen : Std.HashSet Name := {}
  for attr in [regularInitAttr, builtinInitAttr] do
    let mut entries := if current then (attr.ext.getState env).2.toList.toArray else #[]
    for h : index in [:env.header.moduleNames.size] do
      if modules.contains env.header.moduleNames[index] then
        entries := entries ++ attr.ext.getModuleEntries env index
          ++ attr.ext.getModuleIREntries env index
    for (decl, initDecl) in entries do
      let root := if initDecl.isAnonymous then decl else initDecl
      unless seen.contains root do
        seen := seen.insert root
        roots := roots.push root
  return roots

/-- The declarations whose compiled code runs when a program that links the modules `modules`
initializes them, by the rule with which the compiler emits the initializer of a module: the
actions of `initActionsOf`, and each compiled declaration of each of them with no parameter, whose
value the initializer computes. Each name appears once.

The rule also takes a closed term and a ground value, which the initializer does not compute: the
code that first reads a closed term computes it, and a ground value is static data. So the
declarations are a superset of those that the initializers run.

Assumes: Lean v4.34.1 `src/Lean/Compiler/LCNF/EmitC.lean:986-1004` emits, for each compiled
declaration of the module in turn (`:1047-1049`), a call of the action of an `[init]` or
`[builtin_init]` declaration, a call of the initialization function that a declaration with no
parameter names, and otherwise the evaluation of a declaration with no parameter that is neither
a closed term nor a ground value; a closed term is computed when it is first read (`:476-477`,
`:629-635`), and a ground value is static data (`:474-475`). The compiled declarations of an
imported module are its entries of `Lean.IR.declMapExt`, and those of the module being elaborated
are `Lean.IR.getDecls`. -/
def initializersOf (env : Environment) (modules : Std.HashSet Name) : Array Name := Id.run do
  let mut roots := initActionsOf env modules
  let mut seen : Std.HashSet Name := roots.foldl (·.insert ·) {}
  let mut decls := if modules.contains env.mainModule then (getDecls env).toArray else #[]
  for h : index in [:env.header.moduleNames.size] do
    if modules.contains env.header.moduleNames[index] then
      decls := decls ++ declMapExt.getModuleEntries env index
        ++ declMapExt.getModuleIREntries env index
  for decl in decls do
    if decl.params.isEmpty && !seen.contains decl.name then
      seen := seen.insert decl.name
      roots := roots.push decl.name
  return roots

/-- The modules of `env`, with the module of its own commands. -/
def allModules (env : Environment) : Std.HashSet Name :=
  env.header.moduleNames.foldl (·.insert ·) (({} : Std.HashSet Name).insert env.mainModule)

/-- The actions that run when a program built from `env` starts, of every module of `env`
(`initActionsOf`). -/
def initActions (env : Environment) : Array Name :=
  initActionsOf env (allModules env)

/-- The declarations that run when a program built from `env` starts, of every module of `env`
(`initializersOf`). -/
def initializers (env : Environment) : Array Name :=
  initializersOf env (allModules env)

/-- The initializer actions `initializers`, split into those of the toolchain's modules
(`toolchainCaller`), which start paths with the rows' `startup` pairs, and the others, which start
ordinary paths. -/
def splitInitializers (env : Environment) (initializers : Array Name) : Array Name × Array Name :=
  initializers.partition (toolchainCaller env)

/-- A raw call retains its system with the caller and primitive by construction. -/
structure Call where
  /-- The system whose observer was bypassed. -/
  system : RegulaPolicy.External.System
  /-- The declaration that called the primitive. -/
  caller : Name
  /-- The primitive or runtime binding reached. -/
  primitive : Name

/-- What the compiled code of a set of roots reaches. -/
structure Reach where
  /-- Every primitive call the check refuses, with its system. -/
  calls : Array Call
  /-- Each reached declaration whose compiled code the environment does not hold. -/
  unknown : Array Name
  /-- Each observer role outside the module named by its system's row (`foreignRoles`). -/
  foreign : Array (RegulaPolicy.External.System × Name) := #[]
  /-- Each pair of the calls that the program names that admits no call that it reaches. -/
  unused : Array (Name × Name) := #[]

/-- The caller and primitive of each refused call, of every system. -/
def Reach.raw (reach : Reach) : Array (Name × Name) :=
  reach.calls.map fun call => (call.caller, call.primitive)

/-- The declarations that make a call of a primitive in the compiled declaration `caller`, each of
which the check admits the call for (`filesystemReach`): `caller`, and when the compiler may give
its code to other declarations too (`auxiliarySource`), each declaration that reaches that code,
directly or through more such code of its own declaration (`reachers`), other than that
declaration's own code (its `sourceDeclaration`), with those that make the call for each of them
in turn. So a call in the code of `D` is the call of `D` alone only while `D`'s own code alone
reaches it. `reachers` maps each such compiled declaration to the declarations whose compiled code
uses it.

Only a declaration that has reachers is followed, so each followed declaration after `caller` is
a different key of `reachers`, and the bound of one more than their number lets each be
followed. -/
def attributions (env : Environment) (reachers : Std.HashMap Name (Array Name)) (caller : Name) :
    Array Name := Id.run do
  let mut points := #[caller]
  let mut followed : Std.HashSet Name := ({} : Std.HashSet Name).insert caller
  let mut work := #[caller]
  for _ in [:reachers.size + 1] do
    let some current := work.back? | break
    work := work.pop
    let some source := auxiliarySource env current | continue
    for reacher in reachers.getD current #[] do
      unless sourceDeclaration env reacher == source || points.contains reacher do
        points := points.push reacher
      if reachers.contains reacher && !followed.contains reacher then
        followed := followed.insert reacher
        work := work.push reacher
  return points

/-- The filesystem row's walk: each call of a primitive that the compiled code of `roots` reaches
and that `admitted` does not admit, with a declaration that makes it (`attributions`); and each
reached declaration whose compiled body `env` does not hold, so that what it calls is unknown. A
primitive is a declaration of `watched`, or an `extern` declaration bound to a C function of
`removalSymbols` or `writeSymbols`, whatever its name (`isPrimitive`), or a compiled variant of one
(`calledPrimitive`). A call of `IO.FS.Handle.mk` (`readableOpening`) is found only when it opens a
file to write it (`writingOpens`); a call of its variant, or of any other declaration bound to
`openSymbol`, always is. A call is admitted only when it is admitted for each declaration that
makes it, so a call in a specialization that a declaration shares with the one that made it is
admitted for both, or refused. As a root, a primitive bound to a C function is raw. Every compiled
declaration is followed, of this package, of Lean's library and of each other package; a C function
of the runtime is not. When `writes` is false, the walk finds removals alone (`primitives`,
`removalSymbols`). -/
def filesystemReach (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) (writes : Bool := true) : Reach :=
  Id.run do
  let found := if writes then watched else primitives
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut calls : Array (Name × Name) := #[]
  let mut reachers : Std.HashMap Name (Array Name) := {}
  let mut raw := #[]
  let mut unknown := #[]
  -- Each declaration is added to `work` at most once. The bound is far above the number of
  -- compiled declarations that a program of this toolchain reaches (about 200,000); a declaration
  -- left in `work` at the bound is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some name := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl (body := body) ..) =>
      let opens := writingOpens env body
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        match calledPrimitive env found used writes with
        | some primitive =>
          unless readableOpening env used && !opens.contains used do
            calls := calls.push (name, primitive)
        | none =>
          if shareable env used then
            reachers := reachers.alter used fun callers => some ((callers.getD #[]).push name)
          if !seen.contains used then
            seen := seen.insert used
            work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
      let bound := (boundRemoval env name).orElse fun _ =>
        if writes then boundWrite env name else none
      if let some symbol := bound then
        raw := raw.push (name, Name.mkSimple symbol)
    | none => unknown := unknown.push name
  let mut exercised : Array (Name × Name) := #[]
  for (caller, primitive) in calls do
    for point in attributions env reachers caller do
      unless admitted env observers named point primitive || raw.contains (point, primitive) do
        raw := raw.push (point, primitive)
      if let some pair := admittingPair env named point primitive then
        unless exercised.contains pair do exercised := exercised.push pair
  return {
    calls := raw.map fun (caller, primitive) => ⟨.filesystem, caller, primitive⟩
    unknown := unknown ++ work, unused := named.toArray.filter (!exercised.contains ·) }

/-- The walk of the process and environment rows (`pathBoundaries`): every primitive call reached
from `roots`, and from `startup` on paths from the toolchain's initializers, that the row's decision
(`pathAdmitted`) refuses, plus missing compiled bodies. `cold` admits the pairs of a driver's copy
of the process source (`bootstrap`). A declaration is followed once in each context in which a path
reaches it (`PathContext`), so a call of a listed entry by another caller admits nothing below it.
A constant with an initializer is not followed where it is referenced: the reference reads the
value that its initializer, a root of the program, stored when the program started. Runtime-bound
aliases use the same table as named primitives. Native C bodies are not followed. -/
def pathReach (env : Environment) (roots : Array Name) (startup : Array Name := #[])
    (cold : List (Name × Name) := []) : Reach :=
  Id.run do
  let index := primitiveIndex env
  let entries := entryIndex env
  let specializations := specializationIndex env
  let mut classified : Std.HashMap Name (Option Boundary) := {}
  let own := pathBoundaries.foldl (fun own boundary =>
    own.insert boundary.system (observerRoles env boundary.system boundary.observer).1)
    ({} : Std.HashMap RegulaPolicy.External.System (Array Name))
  let mut work := roots.map ((·, ({} : PathContext))) ++ startup.map ((·, { startup := true }))
  let mut seen : Std.HashSet (Name × PathContext) := work.foldl (·.insert ·) {}
  let mut calls : Array Call := #[]
  let mut unknown := #[]
  -- Each declaration is added to `work` at most once in each context. The bound is far above the
  -- number of compiled declarations that a program of this toolchain reaches (about 200,000) in its
  -- few contexts; a declaration left in `work` at the bound is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some (name, context) := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl ..) =>
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        let boundary := match classified[used]? with
          | some boundary => boundary
          | none => boundaryOf env index used
        classified := classified.insert used boundary
        if let some boundary := boundary then
          let observers := own[boundary.system]?.getD #[]
          unless pathAdmitted env boundary observers cold context name used ||
              calls.any (fun call => call.caller == name && call.primitive == used) do
            calls := calls.push ⟨boundary.system, name, used⟩
        else if (getInitFnNameFor? env used).isNone then
          let next := (used, context.enter env entries specializations name used)
          unless seen.contains next do
            seen := seen.insert next
            work := work.push next
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) && !unknown.contains name then
        unknown := unknown.push name
      for boundary in pathBoundaries do
        if let some symbol := boundAmong env boundary.symbols name then
          let primitive := Name.mkSimple symbol
          unless calls.any (fun call => call.caller == name && call.primitive == primitive) do
            calls := calls.push ⟨boundary.system, name, primitive⟩
    | none => unless unknown.contains name do unknown := unknown.push name
  return { calls, unknown := unknown ++ work.map (·.1) }

/-- Both walks of the check: the filesystem row's (`filesystemReach`) from `roots`, `startup` and
`compiled`, with `observers` and the calls `named`, and the process and environment rows'
(`pathReach`) from `roots` and, on paths from the toolchain's initializers, `startup`, with the
pairs `cold`. Each pair of
`named` that admits no call of the filesystem row is unused. `writes` is that of
`filesystemReach`. -/
def rawRemovalsFrom (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) (startup : Array Name := #[])
    (compiled : Array Name := #[]) (cold : List (Name × Name) := []) (writes : Bool := true) :
    Reach :=
  let files := filesystemReach env observers (roots ++ startup ++ compiled) named writes
  let paths := pathReach env roots startup cold
  { files with
    calls := files.calls ++ paths.calls
    unknown := files.unknown ++ paths.unknown.filter (!files.unknown.contains ·) }

/-- The modules among `modules` under a root of the packages that Lean's toolchain ships as its own
code, `Init`, `Std`, `Lean` and `Lake` (`RegulaPolicy.ToolchainRoot`), decided by the module's
name: Lean 4.34.1 keeps no record of the file from which it read a module, so the check cannot
read where an imported module came from (`EnvironmentHeader` holds no path, and the frontend
passes the artifacts of `--setup` to the import alone, `Lean/Elab/Frontend.lean:294-304`).

Assumes:
- No package of the workspace that builds the checked program provides a module under these roots
  by Lake's module lookup, and the library directory of none has the directory or the `.olean`
  file of such a root. Lake supplies the artifact of an import only when the import is a module of
  a package of the workspace (`Lake/Build/Module.lean:35-37` and `:243-276`). The `lean` process
  of a module's build reads every other module through its search path
  (`Lean/Environment.lean:2229-2246`): the library directory of each package of the workspace,
  which Lake sets as `LEAN_PATH` (`Lake/Config/Monad.lean:138-139`,
  `Lake/Build/Actions.lean:63`), then the toolchain's `lib/lean` (`Lean/Util/Path.lean:95-96`,
  `:108-110`). It reads a module from the first of them that has its root's directory or `.olean`
  file (`Lean/Util/Path.lean:61-65`). So a module under these roots is read from the toolchain's
  `lib/lean`. `lake exe qualify observers` checks this hypothesis for three workspaces of this
  repository whose builds run the check: the root package's, the `markdown/` package's and the
  `audit/` package's. It loads each with Lake, and refuses a module under these roots that a
  package of it provides, the root package or a dependency, and such an entry of a package's
  library directory (`Regula.Qualification.Observers.checkToolchainWorkspaces`). A build of a
  checked program in another workspace, the Mathlib integration's or an adopter's, rests on the
  hypothesis unchecked.
- The content of the toolchain's `lib/lean`, as the toolchain's release installs it, is the
  toolchain's own code (`RegulaPolicy.ToolchainRoot`): trusted installation, not checked here. -/
def toolchainModules (modules : Std.HashSet Name) : Std.HashSet Name :=
  modules.filter fun module => decide (RegulaPolicy.ToolchainRoot module.getRoot)

/-- The compiled declarations of the module `module` of `env`: each declaration whose compiled
code the module holds (`Lean.IR.declMapExt`), the code of the environment's own commands for
`env.mainModule`. -/
def compiledDeclarations (env : Environment) (module : Name) : Array Name :=
  if module == env.mainModule then (getDecls env).toArray.map (·.name)
  else match env.getModuleIdx? module with
    | some index =>
      (declMapExt.getModuleIREntries env index ++ declMapExt.getModuleEntries env index).map
        (·.name)
    | none => #[]

/-- The declarations from which the filesystem row's walk and the class of a program start for the
program whose `main` is in the module `root` (`rawRemovals`, `elaborationRefusal`): every compiled
declaration of every module that the program links (`linked`) outside the toolchain
(`toolchainModules`), and `main`. They hold every compiled code of the program's own modules and of
its other dependencies that may run: `main`, what it calls, the initializers that the program's
modules declare (`initializersOf`), and the zero-argument declarations whose values the compiled
module computes when it starts (`Lean/Compiler/LCNF/EmitC.lean:1003-1005` and `:1047-1049`). So
those walks need no model of which of them runs: they over-approximate it. The compiled code of the
toolchain's modules is followed from these roots, and only its own roots are left out. -/
def programRoots (env : Environment) (root : Name) : Array Name :=
  let modules := linked env root
  let toolchain := toolchainModules modules
  (modules.toArray.filter (!toolchain.contains ·)).flatMap (compiledDeclarations env) |>.push `main

/-- `rawRemovalsFrom` for a program whose `main` is `main` in the module `root`. The filesystem
row's walk starts at every compiled declaration of its modules outside the toolchain
(`programRoots`) and at the code that initializes the modules that it links (`linked`,
`initializersOf`). The path rows' walk starts at `main` and at the initializer actions of those
modules (`initActionsOf`), split by `splitInitializers`. Each row supplies its own observers and
sourced exemptions; `named` supplies the program's explicit filesystem pairs and `cold` the pairs of
a driver's copy of the process source (`bootstrap`). Roles outside each row's boundary module are
retained as foreign declarations (`foreignRoles`). -/
def rawRemovals (env : Environment) (root : Name) (named : List (Name × Name) := [])
    (cold : List (Name × Name) := []) (writes : Bool := true) : Reach :=
  let modules := linked env root
  let (startup, ordinary) := splitInitializers env (initActionsOf env modules)
  { rawRemovalsFrom env (filesystemObservers env) (ordinary.push `main) named startup
      (programRoots env root ++ initializersOf env modules) cold writes with
    foreign := foreignRoles env }

/-- The path rows' part of `rawRemovals` alone (`pathReach`), with the foreign roles of every row:
the process starts and environment reads of the program whose `main` is in the module `root`. -/
def pathRemovals (env : Environment) (root : Name) (cold : List (Name × Name) := []) : Reach :=
  let (startup, ordinary) := splitInitializers env (initActionsOf env (linked env root))
  { pathReach env (ordinary.push `main) startup cold with foreign := foreignRoles env }

/-- The declarations of Lean 4.34.1's library through which a program runs Lean's elaborator on
source that it reads: its frontends (`Lean.Elab.runFrontend`, `Lean.Elab.IO.processCommands`,
`Lean.Elab.Frontend.processCommand`, `Lean.Language.Lean.process`) and the dispatchers of its
elaborators (`Lean.Elab.Command.elabCommandTopLevel`, `Lean.Elab.Command.elabCommand`,
`Lean.Elab.Term.elabTerm`, `Lean.Elab.Term.elabTermAndSynthesize`,
`Lean.Elab.Term.synthesizeSyntheticMVars`, `Lean.Elab.Term.runTactic`,
`Lean.Elab.Tactic.evalTactic`). Assumes: Lean runs an elaborator of a command, a term or a tactic,
each of which its initializers register, only from one of these dispatchers, which find it by the
syntax that it elaborates. -/
def elaborationEntries : List Name :=
  [`Lean.Elab.runFrontend, `Lean.Elab.IO.processCommands, `Lean.Elab.Frontend.processCommand,
    `Lean.Language.Lean.process, `Lean.Elab.Command.elabCommandTopLevel,
    `Lean.Elab.Command.elabCommand, `Lean.Elab.Term.elabTerm,
    `Lean.Elab.Term.elabTermAndSynthesize, `Lean.Elab.Term.synthesizeSyntheticMVars,
    `Lean.Elab.Term.runTactic, `Lean.Elab.Tactic.evalTactic]

/-- The declarations that the compiled code of `roots` reaches (`programRoots`), through which
the program elaborates or a tactic writes or removes: each declaration of `elaborationEntries`, and
each declaration that is, or whose `compiledSource` is, a declaration of `tacticRemovals` or
`tacticWrites` that makes the call. This finds each declaration whose `sourceDeclaration` is one of
them without a lookup in the environment for each declaration that the walk visits. Then the
declarations that the walk left at its bound, each of which may reach one. A declaration is reached
when the compiled code of one that is reached uses it (`collectUsedDecls`): a call, a constant or a
partial application, so a reference that a run never calls is reached too. -/
def elaborationReached (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let tacticCallers := (tacticRemovals ++ tacticWrites).map (·.1)
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut found := #[]
  -- Each declaration is added to `work` at most once, as in `filesystemReach`.
  for _ in [:maxDeclarations] do
    let some name := work.back? | break
    work := work.pop
    if elaborationEntries.contains name || tacticCallers.contains name ||
        tacticCallers.contains (compiledSource name) then
      found := found.push name
    if let some decl@(.fdecl ..) := findEnvDecl env name then
      for used in collectUsedDecls env [decl] do
        unless seen.contains used do
          seen := seen.insert used
          work := work.push used
  return found ++ work

/-- The reason to refuse the program whose `main` the environment declares, in the module `root`,
when its check states the wrong class. `elaborates` states whether the compiled code of the
program's own modules and of its dependencies outside the toolchain (`programRoots`) reaches Lean's
elaborator or a tactic's write or removal: whether `elaborationReached` finds a declaration. This
is conservative reachability in the compiled code, not a proof that the program elaborates: every
compiled declaration of those modules is a root, run or not, and a reference to the elaborator
that no run calls counts. A program that may run it states `elaborates := true`, so that the
tactics of the source that it elaborates, with their writes, are trusted effects of the program. -/
def elaborationRefusal (env : Environment) (root : Name) (elaborates : Bool) : Option String :=
  let found := elaborationReached env (programRoots env root)
  if elaborates && found.isEmpty then
    some s!"the check of the program of {root} states that it elaborates source, but no compiled \
      declaration of its modules outside Lean's toolchain reaches one of {elaborationEntries} or \
      a tactic's write or removal: its check states `elaborates := false`"
  else if !elaborates && !found.isEmpty then
    some s!"the program of {root} reaches Lean's elaborator or a tactic's write or removal from \
      a compiled declaration of its modules outside Lean's toolchain \
      ({found.toList.take 5}), so the tactics of the source that it elaborates may run in its \
      process: its check states `elaborates := true`, which makes their writes trusted effects of \
      the program (`Regula.Removal`)"
  else none

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `reached ++ root` of type `Unit`, where `root` is the program's root module. `lake exe
qualify observers` reads the markers from the module data of the package's modules. -/
def reached : Name := `Regula.Removal.reached

/-- Why the check refuses the program whose root module is `root`, by what its compiled code
reaches (`rawRemovals`): each call of a primitive that the check does not admit, with its system
and the declaration of a source of its caller (`sourceDeclaration` at `env`); each pair that the
program names and that admits no call (`Reach.unused`), so that its list is exact; each reached
declaration whose compiled code is unknown; and each observer role outside its system's boundary
module. It is `none` when there is none of them. -/
def programRefusal (env : Environment) (root : Name) (reach : Reach) : Option String :=
  if !reach.calls.isEmpty then
    some s!"the program of {root} acts without its observer and outside the places that its \
      check names: \
      {reach.calls.toList.map fun call =>
        let source := sourceDeclaration env call.caller
        if source == call.caller then
          s!"{call.system.spelling}: {call.caller} calls {call.primitive}"
        else s!"{call.system.spelling}: {call.caller}, of {source}, calls {call.primitive}"}"
  else if !reach.unused.isEmpty then
    some s!"the check of the program of {root} names calls that the program does not make: \
      {reach.unused.toList}"
  else if !reach.unknown.isEmpty then
    some s!"the program of {root} reaches declarations whose compiled code is not available, so \
      their primitive effects are unknown: {reach.unknown.toList}"
  else if !reach.foreign.isEmpty then
    some s!"an observer's role is given outside its boundary module: \
      {reach.foreign.toList.map fun (system, name) => s!"{system.spelling}: {name}"}"
  else none

/-- Check the program whose `main` the environment declares: fail with the refusal of the
program (`programRefusal`) or of its class (`elaborationRefusal`) when there is one, and otherwise
record the program (`reached`). `named` admits the removals and the writes of the program that no
list of this module admits, each as the pair of its caller and the primitive that it calls
(`admitted`), so a call of a primitive at another place fails the build. `elaborates` states
whether the compiled code of the program's modules outside the toolchain reaches Lean's elaborator
(`elaborationRefusal`). `bootstrap` is the namespace in which a driver that cannot import
`Regula.Process` elaborates its copy of the process source, whose pairs (`bootstrap`) the path rows
admit. A program that writes through a library whose writes this module does not list, Verso's
renderer, states `writes := false`: its check finds removals alone (`filesystemReach`), and its
writes are trusted effects of that library, outside this check.
Assumes: Regula's own executables use its committed lakefile/manifest, with trusted package
selection, module naming and artifact loading. Lean v4.34.1 Environment.lean:109-129,2225-2228
stores requested import names without certified compiled-as identities. The renderer refuses
override selection for its exempted dependency; malicious build inputs are outside this check. -/
def checkProgram (named : List (Name × Name) := []) (elaborates : Bool := false)
    (bootstrap : Option Name := none) (writes : Bool := true) :
    Elab.Command.CommandElabM Unit :=
  withExporting (isExporting := false) do
    let env ← getEnv
    unless env.contains `main do
      throwError "no `main` is declared here, so there is no program to check"
    let root := moduleOf env `main
    let cold := (bootstrap.map Regula.Removal.bootstrap).getD []
    if let some refused := programRefusal env root (rawRemovals env root named cold writes) then
      throwError refused
    if let some refused := elaborationRefusal env root elaborates then
      throwError refused
    Elab.Command.liftCoreM <| addDecl (.defnDecl {
      name := reached ++ root, levelParams := [], type := mkConst ``Unit,
      value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

end Regula.Removal
