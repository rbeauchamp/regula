module

public import RegulaSpecification.Proofs.Behaviour
public import RegulaSpecification.Proofs.Occurrences
public import RegulaSpecification.Rules.RG1006
meta import Lean.Elab.Command
import all Init.Prelude
import all Regula.LanguageSet
import all Regula.Verdict

@[expose] public section

namespace RegulaSpecification.Assumptions

open Lean (Name)

inductive Owner where
  | lean
  | lake
  | os
  deriving DecidableEq, Repr

inductive Platform where
  | macOS
  | ubuntu
  deriving DecidableEq, Repr

inductive Source where
  | file (path : String) (lines : String)
  | component (dir : String)
  | manual (page : String)
  deriving DecidableEq, Repr

inductive Assumption where
  | kernel
  | h6
  | replay
  | compiler
  | ctorIdxTag
  | h1
  | h2
  | usedConstants
  | leanImport
  | leanVersion
  | platform
  | lakeLoad
  | h3
  | h5
  | lakeCommands
  | lakeStart
  | h4
  | files
  | processes
  deriving DecidableEq, Repr

inductive Unreached where
  | noEvaluation
  | definition
  | refused
  | verso
  | server
  | lakeLint
  | toolchainOnly
  deriving DecidableEq, Repr

structure Exclusion where
  path : String
  lines : String
  reason : Unreached
  detail : String
  deriving DecidableEq, Repr

namespace Assumption

def owner : Assumption → Owner
  | kernel | h6 | replay | compiler | ctorIdxTag | h1 | h2 | usedConstants | leanImport | leanVersion | platform => .lean
  | lakeLoad | h3 | h5 | lakeCommands | lakeStart => .lake
  | h4 | files | processes => .os

def platforms : Assumption → List Platform
  | platform | h4 | files | processes => [.macOS, .ubuntu]
  | _ => []

theorem os_on_platform (a : Assumption) (h : a.owner = .os) : a.platforms ≠ [] := by
  cases a <;> simp_all [owner, platforms]

def ModuleDataComplete (f : Regula.Load.Facts) : Prop :=
  f.env.header.moduleData.size = f.modules.size

def sources : Assumption → List Source
  | kernel => [.component "src/kernel/"]
  | h6 => [.file "src/kernel/type_checker.cpp" "110-117", .file "src/kernel/type_checker.h" "124-125",
      .file "src/kernel/environment.cpp" "155, 180, 195, 214"]
  | replay => [.file "src/Lean/Replay.lean" "59-63, 74-140, 148-190", .file "src/Lean/Environment.lean" "1848-1863",
      .file "src/Lean/Util/FoldConsts.lean" "16-56, 67-74", .file "src/kernel/type_checker.cpp" "412-426, 1100-1106, 1242-1266",
      .file "src/kernel/inductive.cpp" "1347-1390", .file "src/kernel/quot.cpp" "19-56", .file "src/library/constants.cpp" "12-15",
      .file "src/Lean/Expr.lean" "622-624, 803-811"]
  | compiler => [.component "src/Lean/Compiler/", .component "src/runtime/", .file "src/Init/System/IO.lean" "39"]
  | ctorIdxTag => [.file "src/Lean/Meta/Constructions/CtorIdx.lean" "40-141",
      .file "src/Lean/Meta/Constructions/CasesOn.lean" "17, 28-33, 71-81",
      .file "src/Lean/MetavarContext.lean" "1351-1368",
      .file "src/Lean/Expr.lean" "1591-1616, 1649-1658",
      .file "src/Lean/Environment.lean" "730-732, 3175-3176",
      .file "src/Lean/Compiler/LCNF/Util.lean" "40-53", .file "src/Init/Prelude.lean" "1381-1382",
      .file "src/include/lean/lean.h" "757-763"]
  | h1 => [.file "src/Lean/Language/Lean.lean" "595-601", .file "src/Lean/Parser/Extension.lean" "607-612, 765",
      .file "src/Lean/Parser/Module.lean" "124, 135, 146", .file "src/Lean/Elab/Open.lean" "83, 89, 101",
      .file "src/Lean/Elab/BuiltinCommand.lean" "60", .file "src/Lean/Environment.lean" "2472-2554",
      .file "src/Lean/Elab/Frontend.lean" "287", .file "src/Lean/Shell.lean" "509", .file "src/Lean/Language/Lean.lean" "451",
      .file "src/Lean/DocString/Parser.lean" "2239-2240, 2264-2271", .file "src/Lean/Parser/Term.lean" "214-215",
      .file "src/Lean/Parser/Command.lean" "60-61", .file "src/Lean/DocString/Extension.lean" "116, 121"]
  | h2 => [.file "src/Lean/Elab/BuiltinEvalCommand.lean" "194, 200, 225, 226",
      .file "src/Lean/Elab/BuiltinNotation.lean" "588, 594",
      .file "src/Lean/Elab/BuiltinTerm.lean" "432", .file "src/Lean/Elab/Tactic/BuiltinTactic.lean" "685",
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
      .file "src/Lean/Attributes.lean" "454", .file "src/Lean/Elab/DocString.lean" "1300, 1307, 1357, 1380, 1399, 1417",
      .file "src/Lean/Linter/MissingDocs.lean" "43, 46", .file "src/Lean/Linter/UnusedVariables.lean" "143",
      .file "src/Lean/Compiler/LCNF/Simp/ConstantFold.lean" "792", .file "src/Lean/Compiler/LCNF/PassManager.lean" "217",
      .file "src/Lean/Compiler/IR/Meta.lean" "52, 56-59", .file "src/Lean/Environment.lean" "2893, 2974, 2976, 2983"]
  | usedConstants => [.file "src/Lean/Util/FoldConsts.lean" "51-56"]
  | leanImport => [.file "src/Lean/Environment.lean" "109-111, 155-167, 1384-1385, 1990-1996, 2213, 2224-2227, 2243-2259, 2381-2398, 2443-2444, 2458-2459, 2545-2547, 2672-2673, 2677-2681, 2697-2712, 2734-2737, 2742, 2773",
      .file "src/Lean/Compiler/CSimpAttr.lean" "18-55, 71-80",
      .file "src/Lean/Compiler/ImplementedByAttr.lean" "67-68", .file "src/Lean/Compiler/ExternAttr.lean" "75-76, 119-120",
      .file "src/Lean/Compiler/InitAttr.lean" "50-79, 101, 110, 112-127",
      .file "src/Lean/Attributes.lean" "151-156, 262-266, 276-283, 293-296, 310-325",
      .file "src/Lean/Util/Path.lean" "138-152", .file "src/Lean/Elab/Import.lean" "26-27, 141-160",
      .file "src/Lean/Elab/Frontend.lean" "294-313", .file "src/Lean/Language/Lean.lean" "502-505",
      .file "src/Lean/Parser/Extension.lean" "348",
      .file "src/Lean/ScopedEnvExtension.lean" "17-19, 40-47, 137-153, 159-162, 245-277, 333-360"]
  | leanVersion => [.file "src/Init/Meta/Defs.lean" "37, 57"]
  | platform => [.file "src/Init/System/Platform.lean" "39, 44", .file "src/Init/System/FilePath.lean" "127"]
  | lakeLoad => [.file "src/lake/Lake/Load/Workspace.lean" "31-47, 61", .file "src/lake/Lake/Load/Package.lean" "100-105",
      .file "src/lake/Lake/Load/Config.lean" "31, 44", .file "src/lake/Lake/Config/Module.lean" "63-67, 88-91",
      .file "src/Lean/Util/Path.lean" "34-41",
      .file "src/lake/Lake/Config/LeanLib.lean" "24, 34-35", .file "src/lake/Lake/Config/LeanLibConfig.lean" "46, 140",
      .file "src/lake/Lake/Config/LeanExe.lean" "22-23, 30, 46, 49-51, 72", .file "src/lake/Lake/Config/Package.lean" "68, 356-357, 364-365",
      .file "src/lake/Lake/Config/Workspace.lean" "279-280, 356-357, 391-392", .file "src/lake/Lake/Config/Glob.lean" "53-59",
      .file "src/lake/Lake/Config/InstallPath.lean" "128, 196-200, 272", .file "src/lake/Lake/Config/Env.lean" "74-76, 165, 186-187, 255, 263",
      .file "src/lake/Lake/Toml/Load.lean" "20"]
  | h3 => [.file "src/lake/Lake/Build/Package.lean" "45-61", .file "src/lake/Lake/Build/Module.lean" "50-58",
      .file "src/lake/Lake/Config/Workspace.lean" "279-280", .file "src/lake/Lake/Config/Module.lean" "42-43"]
  | h5 => [.file "src/lake/Lake/CLI/Main.lean" "49, 141", .file "src/lake/Lake/Load/Config.lean" "44",
      .file "src/lake/Lake/Load/Package.lean" "109-117", .file "src/lake/Lake/Util/IO.lean" "87-101"]
  | lakeCommands => [.file "src/lake/Lake/CLI/Main.lean" "317, 977-1000", .file "src/lake/Lake/Build/Run.lean" "114-118"]
  | lakeStart => [.file "src/lake/Lake/CLI/Actions.lean" "20-30, 88-100",
      .file "src/lake/Lake/Config/Workspace.lean" "372-373, 409-410, 417-431", .file "src/lake/Lake/Config/Env.lean" "188, 289-303",
      .file "src/lake/Lake/Config/InstallPath.lean" "160-164", .file "src/lake/Lake/Config/Package.lean" "228-229, 382-383",
      .file "src/lake/Lake/Util/NativeLib.lean" "35-41", .file "src/lake/Lake/CLI/Main.lean" "48-49, 134-141"]
  | h4 => [.file "src/Init/System/IO.lean" "874-879", .file "src/runtime/io.cpp" "1055", .manual "realpath(3)"]
  | files => [.file "src/Init/System/IO.lean" "943, 1058-1060, 1156, 1229-1233, 1316, 1335-1342",
      .file "src/runtime/io.cpp" "422, 1168, 1188, 1309, 1338", .manual "open(2)", .manual "stat(2)", .manual "mkdir(2)",
      .manual "mktemp(3)", .manual "mkdtemp(3)"]
  | processes => [.file "src/Init/System/IO.lean" "1434-1440, 1489, 1494", .file "src/runtime/io.cpp" "1004",
      .file "src/runtime/process.cpp" "358, 453, 475, 496, 510", .manual "env(1)", .manual "fork(2)", .manual "execvp(3)",
      .manual "waitpid(2)", .manual "getenv(3)", .manual "dyld(1)", .manual "ld.so(8)"]

theorem sources_ne_nil (a : Assumption) : a.sources ≠ [] := by
  cases a <;> nofun

theorem verso_options_not_admitted :
    `doc.verso ∉ Regula.Language.options ∧ `doc.verso.module ∉ Regula.Language.options := by
  decide

def excluded : Assumption → List Exclusion
  | h2 =>
    [⟨"src/Lean/Compiler/InitAttr.lean", "193", .refused,
        "the command `initialize` and the attribute `init`; on import it runs only the toolchain's own initializers"⟩,
      ⟨"src/Lean/CoreM.lean", "893", .noEvaluation, "a comment"⟩,
      ⟨"src/Lean/DocString/Markdown.lean", "548, 558", .refused,
        "the attributes `doc_inline_md` and `doc_block_md`, for elements of a Verso doc comment"⟩,
      ⟨"src/Lean/Elab/DocString/Builtin/Keywords.lean", "203, 286", .verso, "a role of a Verso doc comment"⟩,
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
      ⟨"src/Lean/Meta/Tactic/Simp/Types.lean", "411", .noEvaluation, "a docstring"⟩,
      ⟨"src/Lean/MonadEnv.lean", "181, 185, 187, 190", .definition, "`Lean.evalConst` and `Lean.evalConstCheck`"⟩,
      ⟨"src/Lean/Parser/Extension.lean", "266, 269, 272, 276", .toolchainOnly,
        "parsers; a project's needs `syntax` or a parser attribute"⟩,
      ⟨"src/Lean/Parser/Term.lean", "881, 882, 883", .noEvaluation, "a docstring"⟩,
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

def formal : Assumption → List Name
  | h1 | h2 => [``Language.LeanBehaviour]
  | h3 => [``Effects.LakeBehaviour]
  | h4 => [``Effects.RealPathBehaviour, ``Effects.OneRealPath]
  | h5 => [``Effects.LakeSelection]
  | h6 => [``SafeMentionsSafe]
  | usedConstants => [``Loader.UsedConstantsComplete]
  | leanImport => [``ModuleDataComplete]
  | _ => []

def readAt : Assumption → String × String
  | kernel => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h6 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | replay => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | compiler => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | ctorIdxTag => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h1 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h2 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | usedConstants => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | leanImport => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | leanVersion => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | platform => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | lakeLoad => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h3 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h5 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | lakeCommands => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | lakeStart => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | h4 => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | files => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")
  | processes => ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")

theorem readAt_pinned (a : Assumption) : a.readAt = Regula.Closed.pinnedLean := by
  cases a <;> rfl

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
  | .kernelReplay _ => [replay, kernel, h6]
  | .parseToml _ => [lakeLoad]
  | .lakeInstall _ => [lakeLoad]
  | .loadWorkspace .. => [lakeLoad]
  | .loadRoot .. => [lakeLoad]
  | .libModules _ => [lakeLoad]
  | .runLake .. => [processes, lakeCommands, h3, h5]

theorem ofOp_ne_nil {L E : Type} (o : Regula.Effect.Op L E) : ofOp o ≠ [] := by
  cases o <;> nofun

end Assumption

inductive Route where
  | proof
  | full
  | outOfTreeProof
  deriving DecidableEq, Repr

namespace Route

open Assumption

def relies : Route → List Assumption
  | proof => [lakeStart, compiler, ctorIdxTag, platform, lakeCommands]
  | full => [lakeStart, compiler, ctorIdxTag, platform]
  | outOfTreeProof => [lakeStart, compiler, ctorIdxTag, platform, lakeCommands]

theorem relies_ne_nil (r : Route) : r.relies ≠ [] := by
  cases r <;> nofun

end Route

theorem each_relied_on (a : Assumption) :
    (∃ o : Regula.Effect.Op Unit Unit, a ∈ Assumption.ofOp o) ∨ (∃ r : Route, a ∈ r.relies) ∨ a.formal ≠ [] := by
  cases a
  · exact .inl ⟨.kernelReplay {}, by decide⟩
  · exact .inl ⟨.kernelReplay {}, by decide⟩
  · exact .inl ⟨.kernelReplay {}, by decide⟩
  · exact .inr (.inl ⟨.full, by decide⟩)
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

run_cmd do
  unless (Lean.versionString, Lean.githash) == Regula.Closed.pinnedLean do
    Lean.throwError m!"this is Lean {Lean.versionString} ({Lean.githash}), and Regula.Closed.pinnedLean and each entry of \
      RegulaSpecification.Assumptions.Assumption name {Regula.Closed.pinnedLean}: read each entry's sources again at this \
      release, then change its record, `Assumption.readAt` and `Regula.Closed.pinnedLean`"

end RegulaSpecification.Assumptions
