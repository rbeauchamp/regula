/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Verdict

/-!
# The closed set of the language check

What a Lean file may hold, as data, and the type of what the reader gives the decision. Nothing here
decides anything: `Regula.Language` is the decision, and `specification/RegulaSpecification/Language.lean`
states it over these tables, independently of that decision.

Each table is closed: a name that it does not hold is refused, so a construct that a later Lean adds is
refused until someone reads it and adds it. The criterion each entry was read against, at Lean v4.35.0,
is in the specification's section "The language check", which states it as the hypothesis H2.
-/

public section

namespace Regula.Language

open Lean (Name Syntax)

/-- The syntax kinds a file may hold. -/
def kinds : List Name :=
  [`Lean.Elab.Tactic.Ext.ext, `Lean.Parser.Attr.simp, `Lean.Parser.Attr.simple,
    `Lean.Parser.Command.abbrev, `Lean.Parser.Command.attribute,
    `Lean.Parser.Command.classAbbrev, `Lean.Parser.Command.classTk, `Lean.Parser.Command.ctor,
    `Lean.Parser.Command.declId, `Lean.Parser.Command.declModifiers,
    `Lean.Parser.Command.declSig, `Lean.Parser.Command.declValEqns,
    `Lean.Parser.Command.declValSimple, `Lean.Parser.Command.declaration,
    `Lean.Parser.Command.definition, `Lean.Parser.Command.derivingClass,
    `Lean.Parser.Command.end, `Lean.Parser.Command.example, `Lean.Parser.Command.extends,
    `Lean.Parser.Command.in, `Lean.Parser.Command.include, `Lean.Parser.Command.inductive,
    `Lean.Parser.Command.instance, `Lean.Parser.Command.mutual, `Lean.Parser.Command.namespace,
    `Lean.Parser.Command.noncomputable, `Lean.Parser.Command.omit, `Lean.Parser.Command.open,
    `Lean.Parser.Command.openOnly, `Lean.Parser.Command.openSimple,
    `Lean.Parser.Command.optDeclSig, `Lean.Parser.Command.optDeriving,
    `Lean.Parser.Command.private, `Lean.Parser.Command.protected, `Lean.Parser.Command.section,
    `Lean.Parser.Command.sectionHeader, `Lean.Parser.Command.set_option,
    `Lean.Parser.Command.structCtor, `Lean.Parser.Command.structExplicitBinder,
    `Lean.Parser.Command.structFields, `Lean.Parser.Command.structParent,
    `Lean.Parser.Command.structSimpleBinder, `Lean.Parser.Command.structure,
    `Lean.Parser.Command.structureTk, `Lean.Parser.Command.theorem,
    `Lean.Parser.Command.universe, `Lean.Parser.Command.variable,
    `Lean.Parser.Command.whereStructInst, `Lean.Parser.Level.addLit, `Lean.Parser.Level.paren,
    `Lean.Parser.Module.header, `Lean.Parser.Module.import, `Lean.Parser.Module.moduleTk,
    `Lean.Parser.Module.public, `Lean.Parser.Tactic.Conv.conv,
    `Lean.Parser.Tactic.Conv.convRw__, `Lean.Parser.Tactic.Conv.convSeq,
    `Lean.Parser.Tactic.Conv.convSeq1Indented, `Lean.Parser.Tactic.Conv.lhs,
    `Lean.Parser.Tactic.Conv.rhs, `Lean.Parser.Tactic.Conv.unfold, `Lean.Parser.Tactic.acRfl,
    `Lean.Parser.Tactic.allGoals, `Lean.Parser.Tactic.apply, `Lean.Parser.Tactic.assumption,
    `Lean.Parser.Tactic.cases, `Lean.Parser.Tactic.change, `Lean.Parser.Tactic.classical,
    `Lean.Parser.Tactic.clear, `Lean.Parser.Tactic.configItem, `Lean.Parser.Tactic.congr,
    `Lean.Parser.Tactic.constructor, `Lean.Parser.Tactic.contradiction,
    `Lean.Parser.Tactic.decide, `Lean.Parser.Tactic.done, `Lean.Parser.Tactic.dsimp,
    `Lean.Parser.Tactic.elimTarget, `Lean.Parser.Tactic.exact, `Lean.Parser.Tactic.first,
    `Lean.Parser.Tactic.generalize, `Lean.Parser.Tactic.generalizeArg,
    `Lean.Parser.Tactic.induction, `Lean.Parser.Tactic.inductionAlt,
    `Lean.Parser.Tactic.inductionAltLHS, `Lean.Parser.Tactic.inductionAlts,
    `Lean.Parser.Tactic.intro, `Lean.Parser.Tactic.left, `Lean.Parser.Tactic.location,
    `Lean.Parser.Tactic.locationHyp, `Lean.Parser.Tactic.locationType,
    `Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.match,
    `Lean.Parser.Tactic.obtain, `Lean.Parser.Tactic.omega, `Lean.Parser.Tactic.optConfig,
    `Lean.Parser.Tactic.paren, `Lean.Parser.Tactic.posConfigItem, `Lean.Parser.Tactic.rcases,
    `Lean.Parser.Tactic.rcasesPat.clear, `Lean.Parser.Tactic.rcasesPat.ignore,
    `Lean.Parser.Tactic.rcasesPat.one, `Lean.Parser.Tactic.rcasesPat.paren,
    `Lean.Parser.Tactic.rcasesPat.tuple, `Lean.Parser.Tactic.rcasesPatLo,
    `Lean.Parser.Tactic.rcasesPatMed, `Lean.Parser.Tactic.refine, `Lean.Parser.Tactic.renameI,
    `Lean.Parser.Tactic.repeat', `Lean.Parser.Tactic.revert, `Lean.Parser.Tactic.right,
    `Lean.Parser.Tactic.rintro, `Lean.Parser.Tactic.rintroPat.one, `Lean.Parser.Tactic.rwRule,
    `Lean.Parser.Tactic.rwRuleSeq, `Lean.Parser.Tactic.rwSeq, `Lean.Parser.Tactic.rwa,
    `Lean.Parser.Tactic.rwaAt, `Lean.Parser.Tactic.show, `Lean.Parser.Tactic.simp,
    `Lean.Parser.Tactic.simpAll, `Lean.Parser.Tactic.simpArgs, `Lean.Parser.Tactic.simpLemma,
    `Lean.Parser.Tactic.simpPre, `Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpa,
    `Lean.Parser.Tactic.simpaArgsRest, `Lean.Parser.Tactic.split, `Lean.Parser.Tactic.subst,
    `Lean.Parser.Tactic.symm, `Lean.Parser.Tactic.tacticExfalso,
    `Lean.Parser.Tactic.tacticHave__, `Lean.Parser.Tactic.tacticInfer_instance,
    `Lean.Parser.Tactic.tacticLet__, `Lean.Parser.Tactic.tacticRfl,
    `Lean.Parser.Tactic.tacticSeq, `Lean.Parser.Tactic.tacticSeq1Indented,
    `Lean.Parser.Tactic.tacticSuffices_, `Lean.Parser.Tactic.tacticTrivial,
    `Lean.Parser.Tactic.tacticTry_, `Lean.Parser.Tactic.unfold,
    `Lean.Parser.Tactic.«tacticNext_=>_», `Lean.Parser.Tactic.«tactic_<;>_»,
    `Lean.Parser.Term.anonymousCtor, `Lean.Parser.Term.app, `Lean.Parser.Term.arrow,
    `Lean.Parser.Term.attrInstance, `Lean.Parser.Term.attrKind, `Lean.Parser.Term.attributes,
    `Lean.Parser.Term.basicFun, `Lean.Parser.Term.binderDefault, `Lean.Parser.Term.byTactic,
    `Lean.Parser.Term.byTactic', `Lean.Parser.Term.cdot, `Lean.Parser.Term.depArrow,
    `Lean.Parser.Term.do, `Lean.Parser.Term.doBreak, `Lean.Parser.Term.doCatch,
    `Lean.Parser.Term.doContinue, `Lean.Parser.Term.doExpr, `Lean.Parser.Term.doFinally,
    `Lean.Parser.Term.doFor, `Lean.Parser.Term.doForDecl, `Lean.Parser.Term.doHave,
    `Lean.Parser.Term.doIdDecl, `Lean.Parser.Term.doIf, `Lean.Parser.Term.doIfLet,
    `Lean.Parser.Term.doIfLetBind, `Lean.Parser.Term.doIfLetPure, `Lean.Parser.Term.doIfProp,
    `Lean.Parser.Term.doLet, `Lean.Parser.Term.doLetArrow, `Lean.Parser.Term.doLetElse,
    `Lean.Parser.Term.doMatch, `Lean.Parser.Term.doNested, `Lean.Parser.Term.doPatDecl,
    `Lean.Parser.Term.doReassign, `Lean.Parser.Term.doReassignArrow,
    `Lean.Parser.Term.doReturn, `Lean.Parser.Term.doSeqIndent, `Lean.Parser.Term.doSeqItem,
    `Lean.Parser.Term.doTry, `Lean.Parser.Term.doUnless, `Lean.Parser.Term.dotIdent,
    `Lean.Parser.Term.doubleQuotedName, `Lean.Parser.Term.ellipsis, `Lean.Parser.Term.explicit,
    `Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.explicitUniv, `Lean.Parser.Term.forall,
    `Lean.Parser.Term.fromTerm, `Lean.Parser.Term.fun, `Lean.Parser.Term.have,
    `Lean.Parser.Term.hole, `Lean.Parser.Term.hygienicLParen, `Lean.Parser.Term.implicitBinder,
    `Lean.Parser.Term.inferInstanceAs, `Lean.Parser.Term.instBinder, `Lean.Parser.Term.let,
    `Lean.Parser.Term.letConfig, `Lean.Parser.Term.letDecl, `Lean.Parser.Term.letEqnsDecl,
    `Lean.Parser.Term.letI, `Lean.Parser.Term.letId, `Lean.Parser.Term.letIdDecl,
    `Lean.Parser.Term.letIdDeclNoBinders, `Lean.Parser.Term.letPatDecl,
    `Lean.Parser.Term.letRecDecl, `Lean.Parser.Term.letRecDecls, `Lean.Parser.Term.letrec,
    `Lean.Parser.Term.local, `Lean.Parser.Term.match, `Lean.Parser.Term.matchAlt,
    `Lean.Parser.Term.matchAlts, `Lean.Parser.Term.matchAltsWhereDecls,
    `Lean.Parser.Term.matchDiscr, `Lean.Parser.Term.namedArgument,
    `Lean.Parser.Term.namedPattern, `Lean.Parser.Term.nestedAction, `Lean.Parser.Term.nofun,
    `Lean.Parser.Term.nomatch, `Lean.Parser.Term.optEllipsis, `Lean.Parser.Term.paren,
    `Lean.Parser.Term.pipeProj, `Lean.Parser.Term.proj, `Lean.Parser.Term.prop,
    `Lean.Parser.Term.quotedName, `Lean.Parser.Term.show, `Lean.Parser.Term.sort,
    `Lean.Parser.Term.structInst, `Lean.Parser.Term.structInstField,
    `Lean.Parser.Term.structInstFieldDef, `Lean.Parser.Term.structInstFieldEqns,
    `Lean.Parser.Term.structInstFields, `Lean.Parser.Term.structInstLVal,
    `Lean.Parser.Term.subst, `Lean.Parser.Term.sufficesDecl, `Lean.Parser.Term.syntheticHole,
    `Lean.Parser.Term.termReturn, `Lean.Parser.Term.termTry, `Lean.Parser.Term.termUnless, `Lean.Parser.Term.tuple,
    `Lean.Parser.Term.type, `Lean.Parser.Term.typeAscription, `Lean.Parser.Term.typeSpec,
    `Lean.Parser.Term.whereDecls, `Lean.Parser.Termination.decreasingBy,
    `Lean.Parser.Termination.suffix, `Lean.Parser.Termination.terminationBy, `Lean.binderIdent,
    `Lean.bracketedExplicitBinders, `Lean.calcFirstStep, `Lean.calcStep, `Lean.calcSteps,
    `Lean.calcTactic, `Lean.cdot, `Lean.cdotTk, `Lean.explicitBinders,
    `Lean.termThrowErrorAt____, `Lean.termThrowError__, `Lean.unbracketedExplicitBinders,
    `Lean.«binderPred<_», `Lean.«binderPred∈_», `Lean.«term_Matches_|», `Lean.«term∀__,_»,
    `Lean.«term∃__,_», `List.«term_<+:_», `List.«term_<:+:_», `Std.Legacy.Range.«term[:_]»,
    `Std.Legacy.Range.«term[_:_:_]», `Std.Legacy.Range.«term[_:_]», `Vector.«term#v[_,]»,
    `choice, `group, `interpolatedStrKind, `null, `patternIgnore, `tacticFunext___, `term!_,
    `termDepIfThenElse, `termIfLet, `termIfThenElse, `termS!_, `token.«⊢»,
    `«tacticBy_cases_:_», `«term#[_,]», `«term-_», `«term[_]», `«term_!=_», `«term_%_»,
    `«term_&&&_», `«term_&&_», `«term_*_», `«term_++_», `«term_+_», `«term_-_», `«term_/_»,
    `«term_::_», `«term_<$>_», `«term_<<<_», `«term_<_», `«term_<|_», `«term_==_», `«term_=_»,
    `«term_>>=_», `«term_>>>_», `«term_>_», `«term_^^^_», `«term_^_», `«term__[_]'_»,
    `«term__[_]_!», `«term__[_]_?», `«term__[_]», `«term_||_», `«term_|||_», `«term_×'__1»,
    `«term_×__1», `«term_×_», `«term_↔_», `«term_∈_», `«term_∉_», `«term_∘_», `«term_∣_»,
    `«term_∧_», `«term_∨_», `«term_≠_», `«term_≤_», `«term_≥_», `«term_⊆_», `«term_⊕_»,
    `«term{_:_//_}», `«term{_}», `«term{}», `«term¬_», `«term‹_›», `«term∃_,_», `«term∅»]

/-- The tokens a file may hold, outside the kinds of `leafKinds`. -/
def atoms : List String :=
  ["!", "!=", "`", "?", "#[", "#v[", "%", "&&", "&&&", "(", ")", "*", "+", "++", ",", "-", ".", "..",
    "/", "//", ":", "::", ":=", ";", "<", "<$>", "<+:", "<:+:", "<;>", "<<<", "<|", "=", "==",
    "=>", ">", ">>=", ">>>", "@", "@[", "Prop", "Sort", "Type", "[", "]", "]'", "^", "^^^",
    "_", "abbrev", "ac_rfl", "all_goals", "apply", "assumption", "at", "attribute", "break",
    "by", "by_cases", "calc", "cases", "catch", "change", "class", "classical", "clear",
    "congr", "constructor", "continue", "contradiction", "conv", "decide", "decreasing_by",
    "def", "deriving", "do", "done", "dsimp", "else", "end", "example", "exact", "exfalso", "ext",
    "extends", "finally", "first", "for", "from", "fun", "funext", "generalize",
    "generalizing", "have", "if", "import", "in", "include", "induction", "inductive",
    "inferInstanceAs", "infer_instance", "instance", "intro", "left", "let", "letI", "lhs",
    "local", "match", "matches", "module", "mut", "mutual", "namespace", "next", "nofun",
    "nomatch", "noncomputable", "obtain", "omega", "omit", "only", "open", "private",
    "protected", "public", "rcases", "rec", "refine", "rename_i", "repeat", "repeat'",
    "return", "revert", "rfl", "rhs", "right", "rintro", "rw", "rwa", "s!", "section",
    "set_option", "show", "simp", "simp_all", "simpa", "split", "structure", "subst",
    "suffices", "symm", "termination_by", "then", "theorem", "throwError", "throwErrorAt",
    "trivial", "try", "unfold", "universe", "unless", "using", "variable", "where", "with",
    "{", "|", "|>.", "||", "|||", "}", "¬", "·", "×", "‹", "›", "←", "→", "↓", "↔", "∀", "∃",
    "∅", "∈", "∉", "∘", "∣", "∧", "∨", "≠", "≤", "≥", "⊆", "⊕", "⊢", "▸", "⟨", "⟩"]
/-- The kinds whose children are the text of a literal, a comment or hygiene data that Lean's parser
makes. The decision does not enter them, because what they hold is open text that names no construct. -/
def leafKinds : List Name :=
  [`str, `num, `char, `name, `scientific, `fieldIdx, `interpolatedStrLitKind, `hygieneInfo,
    `Lean.Parser.Command.docComment, `Lean.Parser.Command.moduleDoc, `Lean.Parser.Command.eoi]

/-- The attributes of the form `@[name]` that a file may use. -/
def simpleAttributes : List Name :=
  [`inline, `noinline, `always_inline, `reducible, `irreducible, `expose]

/-- The options a file or the Lake configuration may set. -/
def options : List Name :=
  [`maxRecDepth, `maxHeartbeats, `exponentiation.threshold, `autoImplicit, `relaxedAutoImplicit,
    `warningAsError, `linter.missingDocs]

/-- The items of a tactic's `+item` configuration that a file may use. -/
def configItems : List Name := [`kernel]

/-- The classes that a `deriving` clause may name. -/
def derivingClasses : List Name :=
  [`DecidableEq, `BEq, `Repr, `Inhabited, `Hashable, `Ord, `Nonempty]

/-- The keys of a `lakefile.toml` outside `leanOptions`, each as a path of TOML keys. -/
def configKeys : List Name :=
  [`name, `version, `description, `keywords, `license, `licenseFiles, `srcDir, `defaultTargets,
    `lintDriver, `lintDriverArgs, `lean_lib.name, `lean_lib.roots, `lean_lib.globs, `lean_lib.srcDir,
    `lean_exe.name, `lean_exe.root, `lean_exe.srcDir, `lean_exe.supportInterpreter, `require.name,
    `require.git, `require.rev]

/-- What `lean-toolchain` must say: the one Lean this revision reads, which the checker also uses to
build, whatever a project's own file names. -/
def leanToolchain : String := "leanprover/lean4:v4.35.0"

/-- The components of a name, in order, each as a name of one component. -/
def components : Name → List Name
  | .anonymous => []
  | .str p s => components p ++ [.str .anonymous s]
  | .num p n => components p ++ [.num .anonymous n]

/-- One Lean file as the reader got it from Lean's parser. -/
structure FileRead where
  /-- Its module, as Lake names it. -/
  module : Name
  /-- Whether the root package holds it. -/
  inRoot : Bool
  /-- `Lean.Parser.parseHeader`'s tree. -/
  header : Syntax
  /-- `Lean.Parser.parseCommand`'s trees, in order. -/
  commands : List Syntax
  /-- Whether Lean's parser gave no error. -/
  parsed : Bool
  /-- The namespaces that hold scoped parser entries in the environment this file was parsed in. -/
  scopedParsers : List Name

/-- One package of the workspace other than the root. -/
structure PackageRead where
  /-- Its name. -/
  name : Name
  /-- Whether the manifest takes it from a Git revision, not from a local path. -/
  fromGit : Bool
  /-- Whether its Lake configuration is TOML, read by name before any Lake load of it. -/
  tomlConfig : Bool

/-- What the reader read of one project, before anything of it is compiled. -/
structure Reading where
  /-- Whether this checker was started from outside the project's Lake: its program lies outside the
  project, and the Lake that started it was the Lake of the checker's own package. -/
  outside : Bool
  /-- What the project's `lean-toolchain` says, trimmed, or none if it has none. -/
  toolchainFile : Option String
  /-- Whether the root package has a `lakefile.lean`, which Lake prefers and runs. -/
  leanConfig : Bool
  /-- The key paths of the root package's `lakefile.toml`. -/
  configKeys : List Name
  /-- The other packages of the workspace. -/
  packages : List PackageRead
  /-- The modules of the root package's default targets. -/
  roots : List Name
  /-- The roots, and each module outside the toolchain that their imports reach. -/
  reached : List Name
  /-- What the reader read of the modules of `reached`. -/
  files : List FileRead
  /-- What the reader could not read, each with its reason. -/
  unread : List (Name × String)
  /-- What already exists under the project's `.lake`, and the build outputs of each dependency whose
  files are read. -/
  outputs : List String

/-- What the decision gives. -/
inductive Outcome where
  /-- Everything read is in the closed set, so the build can have the full verdict. -/
  | admitted
  /-- The root package holds something outside the closed set. Nothing is compiled. -/
  | refused
  /-- The build can have only the proof verdict: Mathlib is in its imports, or a dependency's code is
  outside the closed set. -/
  | proofOnly
  /-- Something could not be read, so nothing is decided. Nothing is compiled. -/
  | incomplete
  deriving DecidableEq, Repr

/-- One step that the full gate takes, in the order it takes them. -/
inductive Step where
  /-- Read the project and decide (`Reading`, `Outcome`). -/
  | read
  /-- Build the default targets and replay them (`lake build --wfail`, `lake check`). -/
  | build
  /-- Read the finished build and run the rules (`Regula.Closed.run`). -/
  | rules
  deriving DecidableEq, Repr

/-- What a run of the full gate reports. The two verdicts are distinct constructors, so that neither
can be read as the other. -/
inductive Report where
  /-- The full verdict: the check admitted everything before anything was compiled. -/
  | full (verdict : Regula.Closed.Verdict)
  /-- The proof verdict: the rules on the finished build, with no promise about what ran in it. -/
  | proof (verdict : Regula.Closed.Verdict)
  /-- The check refused the project. Nothing was compiled. -/
  | refused
  /-- The check could not read the project. Nothing was compiled. -/
  | incomplete
  deriving DecidableEq, Repr

end Regula.Language
