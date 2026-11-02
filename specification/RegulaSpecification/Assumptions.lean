import Lean.Elab.Command
import RegulaSpecification.Proofs.Behaviour
import RegulaSpecification.Proofs.Occurrences
import RegulaSpecification.Safety

/-!
# The assumptions

The one list of what a verdict of Regula relies on and no proof here discharges: each behaviour of Lean, Lake or the
operating system, named once, with its pinned source. `Assumption` is the list. Anything else of Lean, Lake or the operating system
that a verdict could depend on is outside the contract, as `README.md` in this directory says under "The trusted base".

The list is complete by construction for three classes, each closed by the compiler or the kernel:

- **Operations.** `Assumption.ofOp` gives the entries that each operation of `Regula.Effect.Op` relies on, by a `match`
  over the closed type, so a new operation fails this build until it has its entries.
- **Routes.** `Route` names each published way to start the checker, and `Route.relies` gives its entries.
  `RegulaSpecification.Meaning.run_route` proves that every run of `Regula.Shell.run` is a refusal or a run of a `Route`, so a
  new mode of the program fails the build until it is a route with its entries.
- **Premises.** `RegulaSpecification.Meaning.Meaning` states once each theorem that says what a verdict means, and each premise
  of those statements about Lean, Lake or the operating system is the formal statement of an entry (`Assumption.formal`).
  A premise added to one of those theorems, or to a lemma that one uses, either is proved there or changes that theorem's
  statement, which then differs from `Meaning`, and `RegulaSpecification.Meaning.meaning` fails. A premise written into
  `Meaning` itself changes the contract, which review judges, and no check classifies it.

Each entry records the Lean release at which its sources were read (`Assumption.readAt`). `readAt_pinned` proves each equal
to `Regula.Closed.pinnedLean`, the one release the checker reads, and the command at the end of this file fails the build of
this package under any other Lean. So a change of the pinned toolchain fails the build until each entry is read again and
its record changed.

A source is a path below the root of the tag `v4.35.0` of Lean with its lines, the source directory there of a component that
the owner's account trusts whole, or a page of the platform's own documentation (`Source`).
-/

namespace RegulaSpecification.Assumptions

open Lean (Name)

/-- Who holds an assumption: Lean, Lake, or the operating system. -/
inductive Owner where
  /-- Lean: its kernel, compiler, runtime and library. -/
  | lean
  /-- Lake, the build system of the toolchain. -/
  | lake
  /-- The operating system. -/
  | os
  deriving DecidableEq, Repr

/-- The platforms on which an assumption was observed. The claim holds on these alone. -/
inductive Platform where
  /-- macOS 27.2 on Apple silicon (arm64). -/
  | macOS
  deriving DecidableEq, Repr

/-- Where an assumption is stated. -/
inductive Source where
  /-- Lines of a file of Lean's repository at the tag of the pinned release, by its path from the repository's root. -/
  | file (path : String) (lines : String)
  /-- The source directory, in Lean's repository at the tag of the pinned release and by its path from the repository's
  root, of a component that the owner's account trusts whole. -/
  | component (dir : String)
  /-- A page of the platform's own documentation, as installed on the platform. -/
  | manual (page : String)
  deriving DecidableEq, Repr

/-- The list of assumptions. Each constructor is one behaviour of Lean, Lake or the operating system that a verdict
relies on, stated in its docstring. -/
inductive Assumption where
  /-- Lean's kernel accepts a constant only when it type-checks, at the safety of the constant. -/
  | kernel
  /-- H6: the kernel refuses a safe constant that mentions an unsafe or a partial one (`SafeMentionsSafe`), and checking a
  constant runs no compiled code. So it holds of the input that a proof verdict reads of a build that `lake check` replayed. -/
  | h6
  /-- Lean's compiler and runtime run the checker as its definitions say: `Prog.interpret` asks each operation once, in
  order, through `Regula.Effect.table`, each function with `@[extern]` or `@[implemented_by]` computes what its definition
  or its documentation says, and the exit code is the value that `main` returns. -/
  | compiler
  /-- H1: the trees that the check read of a file of an admitted reading are the trees that Lean's frontend elaborates
  (`LeanBehaviour.h1`). The parser reads of the elaborator's state only scoped parser entries and tokens, namespace and open
  declarations, and the options `internal.parseQuotWithCurrentStage`, `doc.verso` and `doc.verso.module`; none of these
  options is in the admitted `options`, so an admitted file is parsed with each of them unset, as the reader parses it. -/
  | h1
  /-- H2: elaborating trees that the closed set admits runs no code that the project wrote and installs nothing that replaces
  what the compiler runs for a definition (`LeanBehaviour.h2`). -/
  | h2
  /-- `Expr.getUsedConstants` lists each constant that occurs in an expression (`UsedConstantsComplete`). Its body is an
  `opaque` that `@[implemented_by]` replaces. -/
  | usedConstants
  /-- What Lean's import and search give. `Lean.importModules` with `loadExts := false` at the level `.private` loads the
  `.olean` files of the build, runs no initializer, and gives each constant of a `module` file with its body;
  `Environment.constants.map₁` holds the constants that the import keeps; `header.moduleData` holds each module's own
  constants as its `.olean` states them, built from the same array as `header.moduleNames` (`ModuleDataComplete`); and
  `find?`, `getModuleIdxFor?`, `getImplementedBy?` and `isExtern` report what their names say. Lean refuses an `.olean` of
  another release. `Lean.findOLean` finds the `.olean` of a module on the search path that its row sets, and finds the
  toolchain's library only below the toolchain's `lib/lean`. The import for the parser, with `loadExts := true` at the level
  `.exported`, runs the toolchain's initializers and gives its parser extension's state. -/
  | leanImport
  /-- `Lean.versionString` and `Lean.githash` are the release and the commit of the Lean that compiled the checker. -/
  | leanVersion
  /-- On the named platforms Lean's runtime gives `System.Platform.isWindows = false` and `isOSX = true`, so the functions of
  `System.FilePath` read a path as POSIX does, and the full gate replays with `lake check --inadvisably-no-sandbox`. -/
  | platform
  /-- What Lake's loads give, and what `Regula.Load.rootOf` selects of them: `Lake.loadWorkspace` of a directory with Lake's
  default configuration name, and `Lake.loadWorkspaceRoot` with `relConfigFile := "lakefile.toml"`, which loads that file
  alone, with no dependency and no preference for `lakefile.lean`; the source directories, libraries with their `globs`,
  default targets, the libraries and executables of a name, the targets' names, the file of an import (`findModule?`), the
  workspace's search path, and the toolchain's and the root package's library directories; the modules of a library of
  single modules, for which `Glob.one` lists no directory; Lake's TOML parser; the Lake beside the Lean of a system root;
  and a Lake environment with no inherited search path. -/
  | lakeLoad
  /-- H3: what `lake build` compiles for the default targets of an admitted reading is what `Compiled` states, and Lake
  reads each such file, and the tree's configuration, as it stands when it runs (`LakeBehaviour`). Neither Lake's load nor
  `findModule?` reads a module's file, so the reader can load before it writes one. -/
  | h3
  /-- H5: Lake's command line takes `lakefile.lean` as the configuration of a directory when that name resolves, and
  otherwise `lakefile.toml` (`LakeSelection`). -/
  | h5
  /-- `lake build --wfail` builds the default targets and fails on a warning, and `lake check` builds them, exports them,
  replays the export in Lean's kernel in a process that loads no `.olean` of the project, and refuses each axiom other than
  `propext`, `Quot.sound` and `Classical.choice` that a constant of the export mentions. Each works in the directory it is
  started in, reads and writes no file of a project whose path it is not given, and with `LAKE_ARTIFACT_CACHE=false` restores nothing without
  compiling it. -/
  | lakeCommands
  /-- How Lake starts the checker. `lake lint` builds the executable that `lintDriver` names and starts it with
  `lintDriverArgs` as its arguments, and `lake exe lint` starts the same program through the same call: in Lake's working
  directory, with the environment that Lake inherited and `Workspace.augmentedEnvVars` over it, which sets `LEAN_SYSROOT` and
  `LEAN_PATH`, with the workspace's libraries first, and holds no `REGULA_FULL`. `lakefile.toml` has no key that sets a
  variable. With no option of Lake's, Lake loads the workspace in `.` with the configuration `lakefile`. -/
  | lakeStart
  /-- H4: `IO.FS.realPath` answers as `realpath(3)`. A path that crosses a link, or names a component in another case than
  the volume stores it, gets other components (`RealPathBehaviour`); an absolute path with no `.`, `..` or empty component
  that crosses neither keeps its components; and a path asked twice in one run, with no other process changing the file
  system, gets one answer (`OneRealPath`). -/
  | h4
  /-- The file system. `IO.FS.readFile` gives the bytes that a name holds, decoded as UTF-8, and fails on anything else;
  `symlinkMetadata` reports what a name holds, following no link; `writeFile` and `createDirAll` act at the path given;
  `createTempDir` makes a new, empty directory that only this user can use, or answers with an error; `removeDirAll` follows
  no link. Two path strings with the same components, as `Regula.Load.parts` reads them, name one place, so a read and a
  Lake command through one path name one file. -/
  | files
  /-- Processes. `IO.getEnv` gives a variable as the process inherited it; `IO.println` and a flush write to standard
  output; `IO.Process.spawn` starts `/usr/bin/env` in the directory given, with standard input null, and waiting for the child gives
  its exit code; `env -i` starts the program with the variables given and no other; `/usr/bin:/bin` holds the programs
  that Lake asks for by name; and the dynamic loader loads no library that a project placed below its own directory. -/
  | processes
  deriving DecidableEq, Repr

/-- Why no input that the language check admits reaches a file that an entry's stated search matches and that the entry
does not cite. Each was read in Lean's source at the pinned tag. -/
inductive Unreached where
  /-- Each match is a comment, a docstring or a local name, and evaluates nothing. -/
  | noEvaluation
  /-- The file defines an evaluation function. Each call of it is by its name, so the search finds it in a file that the
  entry cites or that this list names. -/
  | definition
  /-- Reached only through a command, an attribute, a syntax or a file that the language check refuses, which the detail
  names. -/
  | refused
  /-- Reached only from a Verso doc comment, which needs the option `doc.verso` or `doc.verso.module`, and neither is in the
  admitted `options`. -/
  | verso
  /-- Code of the language server or the infoview, which a build does not run. -/
  | server
  /-- Reached by Lake's built-in lint, which the full gate does not run, for checks that an attribute the language check
  refuses registers. -/
  | lakeLint
  /-- Evaluates only constants that the toolchain declares, because declaring one in a project needs a construct that the
  language check refuses, which the detail names. -/
  | toolchainOnly
  deriving DecidableEq, Repr

/-- A file that an entry's stated search matches and that the entry does not cite. -/
structure Exclusion where
  /-- The file, by its path from the root of Lean's repository at the tag of the pinned release. -/
  path : String
  /-- The lines that the search matches in it. -/
  lines : String
  /-- Why no admitted input reaches them. -/
  reason : Unreached
  /-- What reaches them, by name. -/
  detail : String
  deriving DecidableEq, Repr

namespace Assumption

/-- Who holds each entry. -/
def owner : Assumption → Owner
  | kernel | h6 | compiler | h1 | h2 | usedConstants | leanImport | leanVersion | platform => .lean
  | lakeLoad | h3 | h5 | lakeCommands | lakeStart => .lake
  | h4 | files | processes => .os

/-- The platforms on which each entry that depends on a platform was observed. -/
def platforms : Assumption → List Platform
  | platform | h4 | files | processes => [.macOS]
  | _ => []

/-- Each entry of the operating system is tied to a named platform. -/
theorem os_on_platform (a : Assumption) (h : a.owner = .os) : a.platforms ≠ [] := by
  cases a <;> simp_all [owner, platforms]

/-- What `leanImport` states of the facts of a load: the header of the environment holds the data of each of its modules.
Lean builds both arrays from one (`Lean/Environment.lean:2313-2317`, `2367-2370`). It is the premise of
`Loader.claimedConstants_complete`, by another name. -/
def ModuleDataComplete (f : Regula.Load.Facts) : Prop :=
  f.env.header.moduleData.size = f.modules.size

/-- The pinned sources of each entry. -/
def sources : Assumption → List Source
  | kernel => [.component "src/kernel/"]
  | h6 => [.file "src/kernel/type_checker.cpp" "110-117", .file "src/kernel/type_checker.h" "127-128",
      .file "src/kernel/environment.cpp" "156, 181, 196, 215"]
  | compiler => [.component "src/Lean/Compiler/", .component "src/runtime/", .file "src/Init/System/IO.lean" "39"]
  | h1 => [.file "src/Lean/Language/Lean.lean" "595-601", .file "src/Lean/Parser/Extension.lean" "607-612, 765",
      .file "src/Lean/Parser/Module.lean" "124, 135, 146", .file "src/Lean/Elab/Open.lean" "83, 89, 101",
      .file "src/Lean/Elab/BuiltinCommand.lean" "60", .file "src/Lean/Environment.lean" "2108-2190",
      .file "src/Lean/Elab/Frontend.lean" "287", .file "src/Lean/Shell.lean" "519", .file "src/Lean/Language/Lean.lean" "451",
      .file "src/Lean/DocString/Parser.lean" "1375-1376, 1400-1407", .file "src/Lean/Parser/Term.lean" "92",
      .file "src/Lean/Parser/Command.lean" "61", .file "src/Lean/DocString/Extension.lean" "115, 120"]
  | h2 => [.file "src/Lean/Elab/BuiltinEvalCommand.lean" "194, 200, 225, 226",
      .file "src/Lean/Elab/BuiltinNotation.lean" "588, 594",
      .file "src/Lean/Elab/BuiltinTerm.lean" "432", .file "src/Lean/Elab/Tactic/BuiltinTactic.lean" "683",
      .file "src/Lean/Elab/Tactic/Guard.lean" "163", .file "src/Lean/Meta/Native.lean" "57, 67",
      .file "src/Lean/Elab/Tactic/Config.lean" "24, 151", .file "src/Lean/Elab/ConfigEval.lean" "54",
      .file "src/Lean/Elab/ConfigEval/Basic.lean" "24, 27, 42, 48, 53", .file "src/Lean/Elab/ConfigEval/Commands.lean" "42",
      .file "src/Lean/Elab/ConfigEval/DeriveEvalExpr.lean" "48, 61, 68, 109, 113, 125",
      .file "src/Lean/Elab/ConfigEval/DeriveEvalTerm.lean" "101, 117, 124",
      .file "src/Lean/Elab/ConfigEval/Instances.lean"
        "118, 122, 126, 130, 134, 138, 142, 146, 150, 154, 251, 255, 259, 263, 267, 271, 275, 279, 283",
      .file "src/Lean/Elab/ConfigEval/Types.lean" "40, 46, 66, 73",
      .file "src/Lean/Elab/Tactic/Try.lean" "1033", .file "src/Lean/Elab/Util.lean" "108",
      .file "src/Lean/KeyedDeclsAttribute.lean" "66, 125, 166, 170", .file "src/Lean/Meta/Tactic/Simp/Simproc.lean" "130, 132",
      .file "src/Lean/Attributes.lean" "450", .file "src/Lean/Elab/DocString.lean" "1193, 1200, 1250, 1273, 1292, 1310",
      .file "src/Lean/Linter/MissingDocs.lean" "43, 46", .file "src/Lean/Linter/UnusedVariables.lean" "143",
      .file "src/Lean/Compiler/LCNF/Simp/ConstantFold.lean" "648", .file "src/Lean/Compiler/LCNF/PassManager.lean" "217",
      .file "src/Lean/Compiler/IR/Meta.lean" "52, 56-59", .file "src/Lean/Environment.lean" "2537, 2618, 2620, 2627"]
  | usedConstants => [.file "src/Lean/Util/FoldConsts.lean" "51-56"]
  | leanImport => [.file "src/Lean/Environment.lean" "1871, 2079-2080, 2094-2095, 2183, 2313-2317, 2367-2370",
      .file "src/Lean/Util/Path.lean" "117-125", .file "src/Lean/Elab/Import.lean" "141-149",
      .file "src/Lean/Parser/Extension.lean" "348", .file "src/Lean/ScopedEnvExtension.lean" "26-31"]
  | leanVersion => [.file "src/Init/Meta/Defs.lean" "37, 57"]
  | platform => [.file "src/Init/System/Platform.lean" "39, 44", .file "src/Init/System/FilePath.lean" "127"]
  | lakeLoad => [.file "src/lake/Lake/Load/Workspace.lean" "31-47, 61", .file "src/lake/Lake/Load/Package.lean" "100-105",
      .file "src/lake/Lake/Load/Config.lean" "31, 44", .file "src/lake/Lake/Config/Module.lean" "62-65, 87-90",
      .file "src/lake/Lake/Config/LeanLib.lean" "24, 34-35", .file "src/lake/Lake/Config/LeanLibConfig.lean" "46, 140",
      .file "src/lake/Lake/Config/LeanExe.lean" "22-23, 30, 46, 49-51, 72", .file "src/lake/Lake/Config/Package.lean" "68, 356-357, 364-365",
      .file "src/lake/Lake/Config/Workspace.lean" "279-280, 356-357, 391-392", .file "src/lake/Lake/Config/Glob.lean" "53-59",
      .file "src/lake/Lake/Config/InstallPath.lean" "128, 196-200, 272", .file "src/lake/Lake/Config/Env.lean" "74-76, 165, 186-187, 255, 263",
      .file "src/lake/Lake/Toml/Load.lean" "20"]
  | h3 => [.file "src/lake/Lake/Build/Package.lean" "45-61", .file "src/lake/Lake/Build/Module.lean" "30-38",
      .file "src/lake/Lake/Config/Workspace.lean" "279-280", .file "src/lake/Lake/Config/Module.lean" "41-42"]
  | h5 => [.file "src/lake/Lake/CLI/Main.lean" "48, 138", .file "src/lake/Lake/Load/Config.lean" "44",
      .file "src/lake/Lake/Load/Package.lean" "109-117", .file "src/lake/Lake/Util/IO.lean" "87-101"]
  | lakeCommands => [.file "src/lake/Lake/CLI/Main.lean" "1218-1226", .file "src/lake/Lake/CLI/Check.lean" "662-675",
      .file "src/lake/Lake/Check/Axioms.lean" "60-71"]
  | lakeStart => [.file "src/lake/Lake/CLI/Actions.lean" "20-30, 88-100", .file "src/lake/Lake/Config/Workspace.lean" "417-431",
      .file "src/lake/Lake/Config/Env.lean" "289-303", .file "src/lake/Lake/CLI/Main.lean" "47-48, 131-138"]
  | h4 => [.file "src/Init/System/IO.lean" "874-879", .manual "realpath(3)"]
  | files => [.file "src/Init/System/IO.lean" "943, 1058-1060, 1156, 1229-1233, 1316, 1335-1342", .manual "open(2)",
      .manual "stat(2)", .manual "mkdir(2)", .manual "mktemp(3)"]
  | processes => [.file "src/Init/System/IO.lean" "1434-1440, 1489", .manual "env(1)", .manual "posix_spawn(2)",
      .manual "getenv(3)", .manual "dyld(1)"]

/-- Each entry has a source. -/
theorem sources_ne_nil (a : Assumption) : a.sources ≠ [] := by
  cases a <;> nofun

/-- What `h1` says of the options that the parser reads in doc comments: neither is one that a file or the Lake configuration
may set, so each admitted file is parsed with both unset. -/
theorem verso_options_not_admitted :
    `doc.verso ∉ Regula.Language.options ∧ `doc.verso.module ∉ Regula.Language.options := by
  decide

/-- The files that an entry's stated search matches and that it does not cite, each with why no admitted input reaches it.
Only `h2` states a search: the whole words `evalConst`, `evalConstCheck`, `evalExpr`, `evalTerm` and `evalDecl` over the
sources of Lean's repository at the tag `v4.35.0`. At that tag it matches 61 files. `h2`'s sources cite the 26 whose sites
are reached only through what the tables refuse, each with every line the search matches, and this list names the other 35.
That the two together are those 61 files is **measured**, by running the search at the tag and comparing, and no theorem
states it; it is read again at each upgrade with the entry. -/
def excluded : Assumption → List Exclusion
  | h2 =>
    [⟨"src/Lean/Compiler/InitAttr.lean", "193", .refused,
        "the command `initialize` and the attribute `init`; on import it runs only the toolchain's own initializers"⟩,
      ⟨"src/Lean/CoreM.lean", "726", .noEvaluation, "a comment"⟩,
      ⟨"src/Lean/DocString/Markdown.lean", "548, 558", .refused,
        "the attributes `doc_inline_md` and `doc_block_md`, for elements of a Verso doc comment"⟩,
      ⟨"src/Lean/Elab/DocString/Builtin/Keywords.lean", "211, 294", .verso, "a role of a Verso doc comment"⟩,
      ⟨"src/Lean/Elab/DocString/Builtin/Postponed.lean", "87", .verso,
        "a deferred check of a Verso doc comment, whose handlers the attribute `deferred_doc_check` registers"⟩,
      ⟨"src/Lean/Elab/ErrorExplanation.lean", "107", .refused, "the command `register_error_explanation`"⟩,
      ⟨"src/Lean/Elab/Eval.lean", "17, 22", .definition, "`Lean.Elab.Term.evalTerm`"⟩,
      ⟨"src/Lean/Elab/Idbg.lean", "233, 235", .refused, "the term `idbg`"⟩,
      ⟨"src/Lean/Elab/Tactic/VCGen/FrameProcAttr.lean", "29", .toolchainOnly,
        "frame procedures of `vcgen`; a project's needs the attribute `frameproc`"⟩,
      ⟨"src/Lean/LibrarySuggestions/Basic.lean", "508", .refused,
        "the command `set_library_suggestions`, read by tactics such as `exact?`"⟩,
      ⟨"src/Lean/Linter/CodeQuality/Frontend.lean", "48", .lakeLint, "the attribute `package_code_quality_check`"⟩,
      ⟨"src/Lean/Linter/EnvLinter/Basic.lean", "59", .refused,
        "the attribute `builtin_env_linter` and the commands that run environment linters"⟩,
      ⟨"src/Lean/Meta/Eval.lean", "48, 50, 55, 57, 61", .definition, "`Lean.Meta.evalExpr` and its variants"⟩,
      ⟨"src/Lean/Meta/Sym/Arith/EvalNum.lean", "19, 20", .noEvaluation, "a module docstring"⟩,
      ⟨"src/Lean/Meta/Tactic/BVDecide/Reflect/ReifiedLemmas.lean", "58, 59, 68, 88, 89, 98", .noEvaluation,
        "a local name for an expression"⟩,
      ⟨"src/Lean/Meta/Tactic/BVDecide/Reflect/SatAtBVLogical.lean", "73, 76", .noEvaluation,
        "a local name for an expression"⟩,
      ⟨"src/Lean/Meta/Tactic/Cbv/CbvSimproc.lean", "162", .toolchainOnly,
        "simprocs of `cbv`; a project's needs the command `cbv_simproc`"⟩,
      ⟨"src/Lean/Meta/Tactic/Grind/Arith/EvalNum.lean", "19, 20, 57", .noEvaluation, "a module docstring and a comment"⟩,
      ⟨"src/Lean/Meta/Tactic/Simp/Types.lean", "411", .noEvaluation, "a docstring"⟩,
      ⟨"src/Lean/MonadEnv.lean", "181, 185, 187, 190", .definition, "`Lean.evalConst` and `Lean.evalConstCheck`"⟩,
      ⟨"src/Lean/Parser/Extension.lean", "266, 269, 272, 276", .toolchainOnly,
        "parsers; a project's needs `syntax` or a parser attribute"⟩,
      ⟨"src/Lean/Parser/Term.lean", "758, 759, 760", .noEvaluation, "a docstring"⟩,
      ⟨"src/Lean/ParserCompiler.lean", "156, 157", .refused, "the parser attributes, which `syntax` applies"⟩,
      ⟨"src/Lean/ParserCompiler/Attribute.lean", "53", .refused,
        "the attributes `combinator_formatter` and `combinator_parenthesizer`"⟩,
      ⟨"src/Lean/PostprocessTraces/Basic.lean", "238, 243, 245", .refused,
        "the scoped commands of `Lean.PostprocessTraces`"⟩,
      ⟨"src/Lean/PrettyPrinter/Basic.lean", "27", .toolchainOnly,
        "parser descriptions of syntax kinds; a project's needs `syntax` or `notation`"⟩,
      ⟨"src/Lean/PrettyPrinter/Delaborator/Builtins.lean", "1545", .toolchainOnly,
        "the tactic of an `autoParam`; a project's `autoParam` is refused"⟩,
      ⟨"src/Lean/Server/CodeActions/Attr.lean", "35, 70", .server, "code actions"⟩,
      ⟨"src/Lean/Server/CodeActions/Basic.lean", "111", .server, "code action providers"⟩,
      ⟨"src/Lean/Server/Rpc/RequestHandling.lean", "31", .server, "remote procedures of the server"⟩,
      ⟨"src/Lean/Util/TestExtern.lean", "34", .refused, "the command `test_extern`"⟩,
      ⟨"src/Lean/Widget/UserWidget.lean", "20, 26, 246", .server,
        "widgets of the infoview, which commands and attributes that the tables refuse declare"⟩,
      ⟨"src/lake/Lake/DSL/Meta.lean", "31, 54", .refused, "`lakefile.lean`"⟩,
      ⟨"src/lake/Lake/DSL/VerLit.lean", "85", .refused, "`lakefile.lean`"⟩,
      ⟨"src/lake/Lake/Load/Lean/Eval.lean", "24, 36, 43, 47, 87, 101, 130, 136, 144, 184, 187, 190", .refused,
        "`lakefile.lean`, of which the full gate's tree holds none (`Reason.configShadowed`)"⟩]
  | _ => []

/-- The declarations of this package that state an entry formally, as a premise of a theorem of `Meaning`. An entry with
none is relied on through the meaning of a response, which no theorem here can state. -/
def formal : Assumption → List Name
  | h1 | h2 => [``Language.LeanBehaviour]
  | h3 => [``Effects.LakeBehaviour]
  | h4 => [``Effects.RealPathBehaviour, ``Effects.OneRealPath]
  | h5 => [``Effects.LakeSelection]
  | h6 => [``SafeMentionsSafe]
  | usedConstants => [``Loader.UsedConstantsComplete]
  | leanImport => [``ModuleDataComplete]
  | _ => []

/-- The Lean release, by version and commit, at which the sources of each entry were read. -/
def readAt : Assumption → String × String
  | kernel => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h6 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | compiler => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h1 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h2 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | usedConstants => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | leanImport => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | leanVersion => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | platform => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | lakeLoad => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h3 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h5 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | lakeCommands => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | lakeStart => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | h4 => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | files => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
  | processes => ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")

/-- Each entry was read at the one release that the checker reads, so a change of `Regula.Closed.pinnedLean` fails this
proof at each entry until that entry's sources are read again and its record changed. -/
theorem readAt_pinned (a : Assumption) : a.readAt = Regula.Closed.pinnedLean := by
  cases a <;> rfl

/-- What each operation of the checker relies on: the meaning of its response. A `match` over the closed type
`Regula.Effect.Op`, so an operation added there fails this definition until it is given its entries. -/
def ofOp {L E : Type} : Regula.Effect.Op L E → List Assumption
  | .leanVersion => [leanVersion]
  | .getEnv _ => [processes, lakeStart]
  | .realPath _ => [h4]
  | .readFile _ => [files]
  | .symlinkMetadata _ => [files]
  | .writeFile _ _ => [files]
  | .createDirAll _ => [files]
  | .createTempDir => [files]
  | .removeDirAll _ => [files]
  | .println _ => [processes]
  | .flush => [processes]
  | .parseHeader _ => [h1]
  | .parseCommand .. => [h1, h2]
  | .findOLean .. => [leanImport]
  | .importForRules .. => [leanImport, usedConstants]
  | .importForParser .. => [leanImport, h1]
  | .parseToml _ => [lakeLoad]
  | .lakeInstall _ => [lakeLoad]
  | .loadWorkspace .. => [lakeLoad]
  | .loadRoot .. => [lakeLoad]
  | .libModules _ => [lakeLoad]
  | .runLake .. => [processes, lakeCommands, kernel, h6, h3, h5]

/-- Each operation relies on an entry. -/
theorem ofOp_ne_nil {L E : Type} (o : Regula.Effect.Op L E) : ofOp o ≠ [] := by
  cases o <;> nofun

end Assumption

/-- The published ways to start the checker. Each names how Lake starts it and which verdict it gives; every other start is
outside the contract. -/
inductive Route where
  /-- `lake lint` from the project's own directory, with no option of Lake's and `REGULA_FULL` unset: the proof verdict
  about the workspace in that directory. -/
  | proof
  /-- `REGULA_FULL=DIR lake exe lint PROFILE` from the directory of a checkout of Regula built apart from the project, with
  no option of Lake's: the full gate on the project at `DIR`. -/
  | full
  deriving DecidableEq, Repr

namespace Route

open Assumption

/-- What each route relies on beyond its operations. Both rest on how Lake starts the checker, on the compiler and on the
platform; a pass of the proof verdict also rests on the operator's `lake build --wfail` and `lake check` of the same build,
and on what the kernel's replay establishes. -/
def relies : Route → List Assumption
  | proof => [lakeStart, compiler, platform, lakeCommands, kernel, h6]
  | full => [lakeStart, compiler, platform]

/-- Each route relies on an entry. -/
theorem relies_ne_nil (r : Route) : r.relies ≠ [] := by
  cases r <;> nofun

end Route

/-- No entry is idle: each is relied on by an operation, a route or a premise of `Meaning`. -/
theorem each_relied_on (a : Assumption) :
    (∃ o : Regula.Effect.Op Unit Unit, a ∈ Assumption.ofOp o) ∨ (∃ r : Route, a ∈ r.relies) ∨ a.formal ≠ [] := by
  cases a
  · exact .inl ⟨.runLake "" "" [], by decide⟩
  · exact .inl ⟨.runLake "" "" [], by decide⟩
  · exact .inr (.inl ⟨.full, by decide⟩)
  · exact .inl ⟨.parseHeader (Lean.Parser.mkInputContext "" ""), by decide⟩
  · exact .inl ⟨.parseCommand (Lean.Parser.mkInputContext "" "") () {} {}, by decide⟩
  · exact .inl ⟨.importForRules [] #[], by decide⟩
  · exact .inl ⟨.findOLean [] .anonymous, by decide⟩
  · exact .inl ⟨.leanVersion, by decide⟩
  · exact .inr (.inl ⟨.full, by decide⟩)
  · exact .inl ⟨.loadRoot "" "", by decide⟩
  · exact .inl ⟨.runLake "" "" [], by decide⟩
  · exact .inl ⟨.runLake "" "" [], by decide⟩
  · exact .inl ⟨.runLake "" "" [], by decide⟩
  · exact .inl ⟨.getEnv "", by decide⟩
  · exact .inl ⟨.realPath "", by decide⟩
  · exact .inl ⟨.readFile "", by decide⟩
  · exact .inl ⟨.flush, by decide⟩

-- This package builds only with the Lean that the checker reads. With `readAt_pinned`, a change of the pinned toolchain
-- fails this build until each entry is read again at the new release.
run_cmd do
  unless (Lean.versionString, Lean.githash) == Regula.Closed.pinnedLean do
    Lean.throwError m!"this is Lean {Lean.versionString} ({Lean.githash}), and Regula.Closed.pinnedLean and each entry of \
      RegulaSpecification.Assumptions.Assumption name {Regula.Closed.pinnedLean}: read each entry's sources again at this \
      release, then change its record, `Assumption.readAt` and `Regula.Closed.pinnedLean`"

end RegulaSpecification.Assumptions
