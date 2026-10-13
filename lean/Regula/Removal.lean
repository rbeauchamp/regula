import Regula.Filesystem
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr
import Lean.Elab.Command

/-! # The check that every removal of a program goes through the observer, and of its writes

A removal primitive of Lean's library is an operation that removes or replaces an entry
(`primitives`, `removalSymbols`). `rawRemovalsFrom` follows the compiled code of a program from its
`main` and the initializers of the modules it links, and finds each call of a removal primitive
that a declaration makes other than a declaration of `Regula.Filesystem` with the filesystem
observer's role (`@[regula_observer filesystem]`, `filesystemObservers`) or a call of Lean's library
that `libraryRemovals` lists. The role given in another module admits nothing, and the check of a
program refuses it (`foreignObservers`). The observer's removals and its move are private to
`Regula.Filesystem`. Its exported operations `removeOwn`, `removeFound`, `replace` and
`withOwnTempDir` observe the place and act only on what the decisions of `RegulaCore.Removal`
decide. `moveAside` moves an entry into a directory that it makes new, so it replaces and removes
nothing, with no `ownPath` resolution and no `Regula.Removal.replacement` decision: a symbolic link
or a `..` among the components above the entry is followed as the operating system resolves it, as
a run of Verso writes through it too.

The same walk finds each call of a primitive that writes a file or makes an entry
(`writePrimitives`, `writeSymbols`), and each opening of a file whose mode is not the literal
`IO.FS.Mode.read` (`opensToWrite`). It admits such a call only in the writer of
`Regula.Filesystem` (`writers`), at a call that `libraryWrites` or `packageWrites` lists, or at a
call that the program names to `checkProgram`, each by its source declaration
(`sourceDeclaration`). A pair that a program names and that admits no call fails the check, so the
list of each program is exact.

`checkProgram` runs the check for the program whose `main` the environment declares, fails the
build of the module that runs it when the check finds a call, and records the program in the
module (`reached`). Each program of the package runs it: at the end of the root module of each
`lean_exe`, or in a module of `Regula.ProgramCheck` that imports a program that `lean --run` runs
and that cannot import this module. `lake exe qualify observers` refuses a program of the package
that no module records, and checks itself the one root that no library module can import,
`auditApp`'s `Main` (`Regula.Qualification.Observers`).

## What the check guarantees

The criterion is honest code, as `SECURITY.md` and `CONTEXT.md` define it: code that does not
deliberately change Lean's environment, compiler or build to make a check pass. Honest code in a
checked program cannot reach a removal outside the observer, except the library removals that
`libraryRemovals` lists, each a trusted exemption of Lake or resting on an assumption, as it states,
and the removals of the two programs that `scripts/verify.sh` and `scripts/provision.sh` run, which
are admitted by name where they are checked (`Regula.ProgramCheck.Verification`,
`Regula.ProgramCheck.Provision`). Deliberate circumvention by Regula's own authors is outside it
(issue 286), for example a hand-written `extern` bound to a C function of the runtime that removes
other than `removalSymbols`, or a use of the private declarations of `Regula.Filesystem`. Honest
code in a checked program writes a file or makes an entry only at the calls that these lists and
its own list name, each again as a whole for its caller and primitive.

The check admits a removal of `libraryRemovals` or of a driver by the pair of its caller and the
primitive that it calls (`admitted`), not by its path or by the call site in the caller. So each
admitted pair is a trusted exception as a whole, together with any further call of the same
primitive inside the same caller: a second `IO.FS.removeDirAll` in a removal of the verification
driver passes the check. Issue 389 tracks deciding the drivers' removals with a decision that a
theorem relates to `RegulaCore.Removal`.

## Boundaries

The C functions of the runtime are not followed: `removalSymbols` lists the ones that remove or
replace an entry, and `writeSymbols` the ones that write a file or make an entry. A removal or a
write by another program that a program starts, such as `rm`, is not a call that the check finds,
nor a write through a handle that an admitted opening made or that the runtime gave as a standard
stream. The check reads the compiled code that the environment holds; a declaration
whose compiled code it does not hold is unknown, and the check fails. -/

namespace Regula.Removal

open Lean IR

/-- The bound on the number of declarations that `rawRemovalsFrom` reads. -/
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

/-- Whether the call of `callee` with the arguments `args` opens a file to write it, when `callee`
is bound to `openSymbol`: the call is a partial application, or its mode is not a variable that the
body binds to the literal 0 (`IO.FS.Mode.read`), among `literals`. The mode is the second argument
that is not erased, the second argument of the C function. -/
def opensToWrite (env : Environment) (literals : Array (VarId × Nat)) (callee : Name)
    (args : Array Arg) (partialCall : Bool) : Bool :=
  match findEnvDecl env callee with
  | some (.extern _ params _ _) =>
    let relevant := (List.range params.size).filter fun index =>
      !(params[index]?.map (·.ty.isErased)).getD true
    match relevant[1]?.bind (args[·]?) with
    | some (Arg.var mode) => partialCall || !literals.contains (mode, 0)
    | _ => true
  | _ => true

/-- The declarations bound to `openSymbol` that the compiled body `body` calls to write a file
(`opensToWrite`). -/
def writingOpens (env : Environment) (body : FnBody) : Array Name :=
  let (literals, calls) := bodyCalls body
  calls.filterMap fun (callee, args, partialCall) =>
    if boundAmong env [openSymbol] callee |>.isSome then
      if opensToWrite env literals callee args partialCall then some callee else none
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

/-- The declarations of `env` with the observer's role of the filesystem
(`@[regula_observer filesystem]`, `Regula.Assumption.roles`), split by whether `observerModule`
declares them: those it declares, and those of every other module. -/
def observerRoles (env : Environment) : Array Name × Array Name :=
  (Regula.Assumption.roles env).foldl (init := (#[], #[])) fun (own, foreign) (name, role) =>
    if role != .observer .filesystem then (own, foreign)
    else if moduleOf env name == observerModule then (own.push name, foreign)
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

/-- Whether the check finds a call of `name` as a call of a primitive: `name` is one of `watched`,
or is bound to a C function of `removalSymbols` or `writeSymbols` (`boundRemoval`, `boundWrite`). -/
def isPrimitive (env : Environment) (watched : List Name) (name : Name) : Bool :=
  watched.contains name || (boundRemoval env name).isSome || (boundWrite env name).isSome

/-- The primitive that a call of `name` calls, if it calls one (`isPrimitive`): `name` itself, or
the primitive that `name` is a compiled variant of (`observerVariant`), such as the boxed form that
a program calls when it passes the primitive as a value. -/
def calledPrimitive (env : Environment) (watched : List Name) (name : Name) : Option Name :=
  if isPrimitive env watched name then some name
  else
    let base := if name matches .str _ "_boxed" then name.getPrefix else name
    let base := if base matches .str _ "_redArg" then base.getPrefix else base
    if base != name && observerVariant env #[base] name && isPrimitive env watched base then
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

/-- The declaration of a source in whose compiled code Lean's compiler made the compiled declaration
`name`: `name` when a source declares it, and otherwise the name after the last `_at_` of `name`, a
specialization made in that declaration, without the parts that `compiledPart` names, when a source
declares it. So the loop `Array.forIn'Unsafe.loop._at_.D.spec_5` and the function `D._lam_2` are
the code of `D`. A name of another form is its own. -/
def sourceDeclaration (env : Environment) (name : Name) : Name :=
  if env.contains name then name
  else
    let made := (name.components.reverse.takeWhile (· != `_at_)).reverse
    let source := (made.reverse.dropWhile compiledPart).reverse.foldl (· ++ ·) .anonymous
    if env.contains source then source else name

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
  URL (`Lake/Load/Materialize.lean:64-82` and `:251-261`).
- `Lake.reuseManifest`, specialized at `Lake.Workspace.updateAndMaterializeCore`, with
  `IO.FS.rename`. Trusted exemption, for the reason above: it moves the packages directory that a
  loaded manifest names to the workspace's (`Lake/Load/Resolve.lean:252-283`).
- The three variants of `IO.FS.withTempFile` in `bv_decide`. Assumes: the program elaborates no
  `bv_decide` proof, so these, which the tactic's initializers reach, do not run; each removes the
  temporary file that `withTempFile` made (`Init/System/IO.lean:1353`). -/
def libraryRemovals : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.removeFile),
    (`Lake.importConfigFile, ``Lean.writeModule),
    (`Lake.removeFileIfExists, ``IO.FS.removeFile),
    (`Lake.downloadArtifactCore, ``IO.FS.removeFile),
    (`Lake.download, ``IO.FS.removeFile),
    (mkPrivateNameCore `Lake.Load.Materialize `Lake.updateGitRepo ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Materialize `Lake.materializeGitRepo ++ `spec_0,
      ``IO.FS.removeDirAll),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.reuseManifest ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore ++ `spec_3,
      ``IO.FS.rename),
    (`IO.FS.withTempFile._at_.Lean.Meta.Tactic.BVDecide.runExternal.spec_3._redArg._lam_0,
      ``IO.FS.removeFile),
    ((`IO.FS.withTempFile._at_._private.Lean.Elab.Tactic.Grind.BVDecide).num 0 ++
        `Lean.Elab.Tactic.Grind.evalBvDecide.spec_1._redArg._lam_0, ``IO.FS.removeFile),
    (`IO.FS.withTempFile._at_.Lean.Elab.Tactic.BVDecide.evalBvDecide.spec_1._redArg._lam_0,
      ``IO.FS.removeFile)]

/-- The writes of the writer of `Regula.Filesystem`, which the check admits in every program: the
opening of the new file beside a destination in `Regula.Filesystem.writeReplacing`, and the making
of the directory of a destination in `Regula.Filesystem.ownRoot`. -/
def writers : List (Name × Name) :=
  [(``Regula.Filesystem.writeReplacing, ``IO.FS.Handle.mk),
    (``Regula.Filesystem.ownRoot, ``IO.FS.createDirAll)]

/-- The calls of a primitive that writes in Lean's library that a program of the package reaches,
each with the declaration of a source that makes it (`sourceDeclaration`), for Lean 4.34.1. The
check admits each of them without establishing what it writes.

- Lake's writes, a trusted exemption for the reason of Lake's removals in `libraryRemovals`: each
  acts on the workspace that the program asked Lake to load or build, as `lake build` or
  `lake update` would there. They write a compiled configuration and its lock
  (`Lake.importConfigFile`, `Lake/Load/Lean/Elab.lean:180`), a manifest and the overrides of its
  packages (`Lake.Manifest.save`, `Lake.Manifest.saveEntries`, `Lake/Load/Manifest.lean:275` and
  `:308`), the toolchain file of an update (`Lake.Workspace.updateAndMaterializeCore`), and in a
  build its outputs, traces, hashes and metadata, the arguments of a compiler or an archiver, the
  entries of its artifact cache and an unpacked release archive (`Lake/Build/Actions.lean:29`,
  `:121` and `:186`, `Lake/Build/Common.lean:177`, `:376`, `:401`, `:454` and `:648`,
  `Lake/Build/Library.lean`, `Lake/Config/Cache.lean:183` and `:434`, `Lake/Util/IO.lean:18`,
  `:31`, `:41` and `:70`).
- Lean's `bv_decide`: the LRAT proof (`Std/Tactic/BVDecide/LRAT/Parser.lean:420`) and the files
  of a proof that `lratBitblaster` writes (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:63`).
  Assumes, as for its removals in `libraryRemovals`: the program elaborates no `bv_decide` proof,
  so these, which the tactic's initializers reach, do not run. -/
def libraryWrites : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.Handle.mk),
    (`Lake.importConfigFile, ``IO.FS.Handle.truncate),
    (`Lake.importConfigFile, ``IO.FS.createDirAll),
    (`Lake.Manifest.save, ``IO.FS.writeFile),
    (`Lake.Manifest.saveEntries, ``IO.FS.writeFile),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore,
      ``IO.FS.writeFile),
    (`Lake.compileLeanModule, ``IO.FS.writeFile),
    (`Lake.mkArgs, ``IO.FS.Handle.mk),
    (`Lake.untar, ``IO.FS.createDirAll),
    (`Lake.BuildMetadata.writeFile, ``IO.FS.writeFile),
    (`Lake.writeFileHash, ``IO.FS.writeFile),
    (`Lake.fetchFileHash, ``IO.FS.writeFile),
    (`Lake.Cache.saveArtifact, ``IO.FS.hardLink),
    (`Lake.restoreArtifact, ``IO.FS.hardLink),
    (`Lake.LeanLib.staticFacetConfig, ``IO.FS.Handle.mk),
    (`Lake.CacheMap.writeFile, ``IO.FS.Handle.mk),
    (mkPrivateNameCore `Lake.Config.Cache `Lake.Cache.writeOutputsCore, ``IO.FS.writeFile),
    (`Lake.createParentDirs, ``IO.FS.createDirAll),
    (`Lake.writeFileIfNew, ``IO.FS.Handle.mk),
    (`Lake.writeBinFileIfNew, ``IO.FS.Handle.mk),
    (`Lake.copyFile, ``IO.FS.writeBinFile),
    (`Std.Tactic.BVDecide.LRAT.dumpLRATProof, ``IO.FS.writeBinFile),
    (`Lean.Meta.Tactic.BVDecide.lratBitblaster, ``IO.FS.writeFile)]

/-- The writes of Regula's own declarations that more than one program reaches, each with the
declaration of a source that makes it (`sourceDeclaration`). Each writes below a directory that the
program made for its own run, never at a destination that its arguments name:

- the lock of the scratch area, the marker of a scratch directory and the directory, in
  `Regula.Scratch.withScratch`;
- the copy of a project below the directory that the caller gives, and the overrides of its
  packages, in `Regula.Checker.Lake.copyProject` and `Regula.Checker.Lake.relocateDependencies`;
- the sources of the modules that an audit compiles, below its scratch directory, in
  `Regula.Checker.SourceAudit.compileBatch` and `Regula.Checker.SourceAudit.compileIn`;
- the identity document of an acceptance link, below the scratch directory, which it removes after
  reading its digest, in `Regula.Checker.AcceptanceLink.identity`;
- the copy of a project's Markdown and the scratch of its fences, below the copy, in
  `Regula.Checker.Documentation.snapshotMarkdown` and
  `Regula.Checker.Documentation.auditBuiltProject`;
- the claim of a memoized history worker's output and the directories of a probe's overlay, below
  the directories of the run, in `Regula.Checker.Environment.historyWorkerOutput` and
  `Regula.Checker.Environment.linkProbeOverlay`. -/
def packageWrites : List (Name × Name) :=
  [(`Regula.Scratch.withScratch, ``IO.FS.Handle.mk),
    (`Regula.Scratch.withScratch, ``IO.FS.createDir),
    (`Regula.Checker.Lake.copyProject, ``IO.FS.createDirAll),
    (`Regula.Checker.Lake.copyProject, ``IO.FS.writeBinFile),
    (`Regula.Checker.Lake.relocateDependencies, ``IO.FS.createDirAll),
    (`Regula.Checker.SourceAudit.compileBatch, ``IO.FS.writeFile),
    (mkPrivateNameCore `Regula.Checker.SourceAudit `Regula.Checker.SourceAudit.compileIn,
      ``IO.FS.writeFile),
    (`Regula.Checker.AcceptanceLink.identity, ``IO.FS.writeFile),
    (`Regula.Checker.Documentation.snapshotMarkdown, ``IO.FS.createDirAll),
    (`Regula.Checker.Documentation.snapshotMarkdown, ``IO.FS.writeFile),
    (`Regula.Checker.Documentation.auditBuiltProject, ``IO.FS.createDirAll),
    (mkPrivateNameCore `Regula.Checker.Environment
        `Regula.Checker.Environment.historyWorkerOutput, ``IO.FS.Handle.mk),
    (mkPrivateNameCore `Regula.Checker.Environment `Regula.Checker.Environment.linkProbeOverlay,
      ``IO.FS.createDirAll)]

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
`writers`, `libraryWrites` and `packageWrites`. -/
def sharedPairs : List (Name × Name) :=
  libraryRemovals ++ writers ++ libraryWrites ++ packageWrites

/-- Whether the call of `primitive` by `caller` is a removal or a write that the check admits: a
call by one of `observers` or a compiled variant of one (`observerVariant`), or a call that a pair
of `sharedPairs` or of `named` admits (`admittingPair`). -/
def admitted (env : Environment) (observers : Array Name) (named : List (Name × Name))
    (caller primitive : Name) : Bool :=
  observerVariant env observers caller ||
    (admittingPair env (sharedPairs ++ named) caller primitive).isSome

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

/-- The declarations that run when a program that links the modules `modules` starts: each
declaration of each of them with an `[init]` or `[builtin_init]` attribute when it is the action
that runs, and otherwise the function that computes its value. -/
def initializersOf (env : Environment) (modules : Std.HashSet Name) : Array Name := Id.run do
  let mut roots := #[]
  for attr in [regularInitAttr, builtinInitAttr] do
    let mut entries := if modules.contains env.mainModule then
      (attr.ext.getState env).2.toList.toArray else #[]
    for h : index in [:env.header.moduleNames.size] do
      if modules.contains env.header.moduleNames[index] then
        entries := entries ++ attr.ext.getModuleEntries env index
          ++ attr.ext.getModuleIREntries env index
    for (decl, initDecl) in entries do
      roots := roots.push (if initDecl.isAnonymous then decl else initDecl)
  return roots

/-- The declarations that run when a program built from `env` starts, of every module of `env`
(`initializersOf`). -/
def initializers (env : Environment) : Array Name :=
  initializersOf env (env.header.moduleNames.foldl (·.insert ·)
    (({} : Std.HashSet Name).insert env.mainModule))

/-- What the compiled code of a set of roots reaches. -/
structure Reach where
  /-- Each call of a primitive that the check does not admit, with its caller. -/
  raw : Array (Name × Name)
  /-- Each reached declaration whose compiled code the environment does not hold. -/
  unknown : Array Name
  /-- Each declaration of another module than `observerModule` with the filesystem observer's role
  (`foreignObservers`). -/
  foreign : Array Name := #[]
  /-- Each pair of the calls that the program names that admits no call that it reaches. -/
  unused : Array (Name × Name) := #[]

/-- The primitives that the check finds by name: those that remove (`primitives`) and those that
write (`writePrimitives`). -/
def watched : List Name := primitives ++ writePrimitives

/-- Each call of a primitive that the compiled code of `roots` reaches and that `admitted` does not
admit, with the declaration that makes it; and each reached declaration whose compiled body `env`
does not hold, so that what it calls is unknown. A primitive is a declaration of `watched`, or an
`extern` declaration bound to a C function of `removalSymbols` or `writeSymbols`, whatever its name
(`isPrimitive`), or a compiled variant of one (`calledPrimitive`). A call of one bound to
`openSymbol` is found only when it opens a file to write it (`writingOpens`), and a call of its
variant always is. As a root, a primitive bound to a C function is raw. Every compiled declaration
is followed, of this package, of Lean's library and of each other package; a C function of the
runtime is not. -/
def rawRemovalsFrom (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) : Reach :=
  Id.run do
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut raw := #[]
  let mut unknown := #[]
  let mut exercised : Array (Name × Name) := #[]
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
        match calledPrimitive env watched used with
        | some primitive =>
          let reads := (boundAmong env [openSymbol] used).isSome && !opens.contains used
          unless reads || admitted env observers named name primitive do
            raw := raw.push (name, primitive)
          if let some pair := admittingPair env named name primitive then
            unless reads || exercised.contains pair do exercised := exercised.push pair
        | none =>
          if !seen.contains used then
            seen := seen.insert used
            work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
      if let some symbol := (boundRemoval env name).orElse fun _ => boundWrite env name then
        raw := raw.push (name, Name.mkSimple symbol)
    | none => unknown := unknown.push name
  return {
    raw, unknown := unknown ++ work, unused := named.toArray.filter (!exercised.contains ·) }

/-- `rawRemovalsFrom` for a program whose `main` is `main` in the module `root`: from `main` and
from each initializer of the modules that it links (`linked`, `initializersOf`), with the
filesystem observers of `env` and the calls `named`, and with the declarations of other modules
that have the filesystem observer's role (`foreignObservers`). -/
def rawRemovals (env : Environment) (root : Name) (named : List (Name × Name) := []) : Reach :=
  let roots := (initializersOf env (linked env root)).push `main
  { rawRemovalsFrom env (filesystemObservers env) roots named with
    foreign := foreignObservers env }

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `reached ++ root` of type `Unit`, where `root` is the program's root module. `lake exe
qualify observers` reads the markers from the module data of the package's modules. -/
def reached : Name := `Regula.Removal.reached

/-- Why the check refuses the program whose root module is `root`, by what its compiled code
reaches (`rawRemovals`): each call of a primitive that the check does not admit, with the
declaration of a source of its caller (`sourceDeclaration` at `env`); each pair that the program
names and that admits no call (`Reach.unused`), so that its list is exact; each reached declaration
whose compiled code is unknown; and each declaration of another module than `observerModule` with
the filesystem observer's role. It is `none` when there is none of them. -/
def programRefusal (env : Environment) (root : Name) (reach : Reach) : Option String :=
  if !reach.raw.isEmpty then
    some s!"the program of {root} removes or writes without the observer `Regula.Filesystem` \
      and outside the places that its check names: \
      {reach.raw.toList.map fun (caller, primitive) =>
        let source := sourceDeclaration env caller
        if source == caller then s!"{caller} calls {primitive}"
        else s!"{caller}, of {source}, calls {primitive}"}"
  else if !reach.unused.isEmpty then
    some s!"the check of the program of {root} names calls that the program does not make: \
      {reach.unused.toList}"
  else if !reach.unknown.isEmpty then
    some s!"the program of {root} reaches declarations whose compiled code is not available, so \
      their removals and writes are unknown: {reach.unknown.toList}"
  else if !reach.foreign.isEmpty then
    some s!"the filesystem observer's role is given outside `{observerModule}`, the only module \
      whose declarations remove: {reach.foreign.toList}"
  else none

/-- Check the program whose `main` the environment declares: fail with the refusal of the
program (`programRefusal`) when there is one, and otherwise record the program (`reached`).
`named` admits the removals and the writes of the program that no list of this module admits,
each as the pair of its caller and the primitive that it calls (`admitted`), so a call of a
primitive at another place fails the build. -/
def checkProgram (named : List (Name × Name) := []) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless env.contains `main do
    throwError "no `main` is declared here, so there is no program to check"
  let root := moduleOf env `main
  if let some refused := programRefusal env root (rawRemovals env root named) then
    throwError refused
  Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := reached ++ root, levelParams := [], type := mkConst ``Unit,
    value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

end Regula.Removal
