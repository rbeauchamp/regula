module

public import Regula.Verdict

public section

namespace Regula.Language

open Lean (Name Syntax)

def kinds : List Name :=
  [`choice, `group, `interpolatedStrKind, `null, `patternIgnore, `«tacticBy_cases_:_»,
    `tacticFunext___, `term!_, `«term#[_,]», `«term-_», `termDepIfThenElse, `termIfLet,
    `termIfThenElse, `termS!_, `«term[_]», `«term_!=_», `«term_%_», `«term_&&&_», `«term_&&_»,
    `«term_*_», `«term_++_», `«term_+_», `«term_-_», `«term_/_», `«term_::_», `«term_<$>_»,
    `«term_<<<_», `«term_<_», `«term_<|_», `«term_==_», `«term_=_», `«term_>>=_», `«term_>>>_»,
    `«term_>_», `«term_^^^_», `«term_^_», `«term__[_]», `«term__[_]'_», `«term__[_]_!», `«term__[_]_?»,
    `«term_||_», `«term_|||_», `«term_×'__1», `«term_×_», `«term_×__1», `«term_↔_», `«term_∈_»,
    `«term_∉_», `«term_∘_», `«term_∣_», `«term_∧_», `«term_∨_», `«term_≠_», `«term_≤_», `«term_≥_»,
    `«term_⊆_», `«term_⊕_», `«term{_:_//_}», `«term{_}», `«term{}», `«term¬_», `«term‹_›», `«term∃_,_»,
    `«term∅», `Lean.binderIdent, `Lean.«binderPred<_», `Lean.«binderPred∈_»,
    `Lean.bracketedExplicitBinders, `Lean.calcFirstStep, `Lean.calcStep, `Lean.calcSteps,
    `Lean.calcTactic, `Lean.cdot, `Lean.cdotTk, `Lean.explicitBinders, `Lean.termThrowErrorAt____,
    `Lean.termThrowError__, `Lean.«term_Matches_|», `Lean.«term∀__,_», `Lean.«term∃__,_»,
    `Lean.unbracketedExplicitBinders, `List.«term_<+:_», `List.«term_<:+:_», `Vector.«term#v[_,]»,
    `token.«⊢», `Lean.Parser.Attr.simp, `Lean.Parser.Attr.simple, `Lean.Parser.Command.abbrev,
    `Lean.Parser.Command.attribute, `Lean.Parser.Command.classAbbrev, `Lean.Parser.Command.classTk,
    `Lean.Parser.Command.ctor, `Lean.Parser.Command.declId, `Lean.Parser.Command.declModifiers,
    `Lean.Parser.Command.declSig, `Lean.Parser.Command.declValEqns, `Lean.Parser.Command.declValSimple,
    `Lean.Parser.Command.declaration, `Lean.Parser.Command.definition,
    `Lean.Parser.Command.derivingClass, `Lean.Parser.Command.end, `Lean.Parser.Command.example,
    `Lean.Parser.Command.extends, `Lean.Parser.Command.in, `Lean.Parser.Command.include,
    `Lean.Parser.Command.inductive, `Lean.Parser.Command.instance, `Lean.Parser.Command.mutual,
    `Lean.Parser.Command.namespace, `Lean.Parser.Command.noncomputable, `Lean.Parser.Command.omit,
    `Lean.Parser.Command.open, `Lean.Parser.Command.openOnly, `Lean.Parser.Command.openSimple,
    `Lean.Parser.Command.optDeclSig, `Lean.Parser.Command.optDeriving, `Lean.Parser.Command.private,
    `Lean.Parser.Command.protected, `Lean.Parser.Command.section, `Lean.Parser.Command.sectionHeader,
    `Lean.Parser.Command.set_option, `Lean.Parser.Command.structCtor,
    `Lean.Parser.Command.structExplicitBinder, `Lean.Parser.Command.structFields,
    `Lean.Parser.Command.structParent, `Lean.Parser.Command.structSimpleBinder,
    `Lean.Parser.Command.structure, `Lean.Parser.Command.structureTk, `Lean.Parser.Command.theorem,
    `Lean.Parser.Command.universe, `Lean.Parser.Command.variable, `Lean.Parser.Command.whereStructInst,
    `Lean.Parser.Level.addLit, `Lean.Parser.Level.paren, `Lean.Parser.Module.header,
    `Lean.Parser.Module.import, `Lean.Parser.Module.moduleTk, `Lean.Parser.Module.public,
    `Lean.Parser.Tactic.acRfl, `Lean.Parser.Tactic.allGoals, `Lean.Parser.Tactic.apply,
    `Lean.Parser.Tactic.assumption, `Lean.Parser.Tactic.cases, `Lean.Parser.Tactic.change,
    `Lean.Parser.Tactic.classical, `Lean.Parser.Tactic.clear, `Lean.Parser.Tactic.configItem,
    `Lean.Parser.Tactic.congr, `Lean.Parser.Tactic.constructor, `Lean.Parser.Tactic.contradiction,
    `Lean.Parser.Tactic.decide, `Lean.Parser.Tactic.done, `Lean.Parser.Tactic.dsimp,
    `Lean.Parser.Tactic.elimTarget, `Lean.Parser.Tactic.exact, `Lean.Parser.Tactic.first,
    `Lean.Parser.Tactic.generalize, `Lean.Parser.Tactic.generalizeArg, `Lean.Parser.Tactic.induction,
    `Lean.Parser.Tactic.inductionAlt, `Lean.Parser.Tactic.inductionAltLHS,
    `Lean.Parser.Tactic.inductionAlts, `Lean.Parser.Tactic.intro, `Lean.Parser.Tactic.left,
    `Lean.Parser.Tactic.location, `Lean.Parser.Tactic.locationHyp, `Lean.Parser.Tactic.locationType,
    `Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.match, `Lean.Parser.Tactic.obtain,
    `Lean.Parser.Tactic.omega, `Lean.Parser.Tactic.optConfig, `Lean.Parser.Tactic.paren,
    `Lean.Parser.Tactic.posConfigItem, `Lean.Parser.Tactic.rcases, `Lean.Parser.Tactic.rcasesPatLo,
    `Lean.Parser.Tactic.rcasesPatMed, `Lean.Parser.Tactic.refine, `Lean.Parser.Tactic.renameI,
    `Lean.Parser.Tactic.repeat', `Lean.Parser.Tactic.revert, `Lean.Parser.Tactic.right,
    `Lean.Parser.Tactic.rintro, `Lean.Parser.Tactic.rwRule, `Lean.Parser.Tactic.rwRuleSeq,
    `Lean.Parser.Tactic.rwSeq, `Lean.Parser.Tactic.rwa, `Lean.Parser.Tactic.rwaAt,
    `Lean.Parser.Tactic.show, `Lean.Parser.Tactic.simp, `Lean.Parser.Tactic.simpAll,
    `Lean.Parser.Tactic.simpArgs, `Lean.Parser.Tactic.simpLemma, `Lean.Parser.Tactic.simpPre,
    `Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpa, `Lean.Parser.Tactic.simpaArgsRest,
    `Lean.Parser.Tactic.split, `Lean.Parser.Tactic.subst, `Lean.Parser.Tactic.symm,
    `Lean.Parser.Tactic.tacticExfalso, `Lean.Parser.Tactic.tacticHave__,
    `Lean.Parser.Tactic.tacticInfer_instance, `Lean.Parser.Tactic.tacticLet__,
    `Lean.Parser.Tactic.«tacticNext_=>_», `Lean.Parser.Tactic.tacticRfl, `Lean.Parser.Tactic.tacticSeq,
    `Lean.Parser.Tactic.tacticSeq1Indented, `Lean.Parser.Tactic.tacticSuffices_,
    `Lean.Parser.Tactic.tacticTrivial, `Lean.Parser.Tactic.tacticTry_,
    `Lean.Parser.Tactic.«tactic_<;>_», `Lean.Parser.Tactic.unfold, `Lean.Parser.Term.anonymousCtor,
    `Lean.Parser.Term.app, `Lean.Parser.Term.arrow, `Lean.Parser.Term.attrInstance,
    `Lean.Parser.Term.attrKind, `Lean.Parser.Term.attributes, `Lean.Parser.Term.basicFun,
    `Lean.Parser.Term.binderDefault, `Lean.Parser.Term.byTactic, `Lean.Parser.Term.byTactic',
    `Lean.Parser.Term.cdot, `Lean.Parser.Term.depArrow, `Lean.Parser.Term.do,
    `Lean.Parser.Term.doBreak, `Lean.Parser.Term.doCatch, `Lean.Parser.Term.doContinue,
    `Lean.Parser.Term.doExpr, `Lean.Parser.Term.doFinally, `Lean.Parser.Term.doFor,
    `Lean.Parser.Term.doForDecl, `Lean.Parser.Term.doHave, `Lean.Parser.Term.doIdDecl,
    `Lean.Parser.Term.doIf, `Lean.Parser.Term.doIfLet, `Lean.Parser.Term.doIfLetBind,
    `Lean.Parser.Term.doIfLetPure, `Lean.Parser.Term.doIfProp, `Lean.Parser.Term.doLet,
    `Lean.Parser.Term.doLetArrow, `Lean.Parser.Term.doLetElse, `Lean.Parser.Term.doMatch,
    `Lean.Parser.Term.doNested, `Lean.Parser.Term.doPatDecl, `Lean.Parser.Term.doReassign,
    `Lean.Parser.Term.doReassignArrow, `Lean.Parser.Term.doReturn, `Lean.Parser.Term.doSeqIndent,
    `Lean.Parser.Term.doSeqItem, `Lean.Parser.Term.doTry, `Lean.Parser.Term.doUnless,
    `Lean.Parser.Term.dotIdent, `Lean.Parser.Term.doubleQuotedName, `Lean.Parser.Term.ellipsis,
    `Lean.Parser.Term.explicit, `Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.explicitUniv,
    `Lean.Parser.Term.forall, `Lean.Parser.Term.fromTerm, `Lean.Parser.Term.fun,
    `Lean.Parser.Term.have, `Lean.Parser.Term.hole, `Lean.Parser.Term.hygienicLParen,
    `Lean.Parser.Term.implicitBinder, `Lean.Parser.Term.inferInstanceAs, `Lean.Parser.Term.instBinder,
    `Lean.Parser.Term.let, `Lean.Parser.Term.letConfig, `Lean.Parser.Term.letDecl,
    `Lean.Parser.Term.letEqnsDecl, `Lean.Parser.Term.letI, `Lean.Parser.Term.letId,
    `Lean.Parser.Term.letIdDecl, `Lean.Parser.Term.letIdDeclNoBinders, `Lean.Parser.Term.letPatDecl,
    `Lean.Parser.Term.letRecDecl, `Lean.Parser.Term.letRecDecls, `Lean.Parser.Term.letrec,
    `Lean.Parser.Term.local, `Lean.Parser.Term.match, `Lean.Parser.Term.matchAlt,
    `Lean.Parser.Term.matchAlts, `Lean.Parser.Term.matchAltsWhereDecls, `Lean.Parser.Term.matchDiscr,
    `Lean.Parser.Term.namedArgument, `Lean.Parser.Term.namedPattern, `Lean.Parser.Term.nestedAction,
    `Lean.Parser.Term.nofun, `Lean.Parser.Term.nomatch, `Lean.Parser.Term.optEllipsis,
    `Lean.Parser.Term.paren, `Lean.Parser.Term.pipeProj, `Lean.Parser.Term.proj,
    `Lean.Parser.Term.prop, `Lean.Parser.Term.quotedName, `Lean.Parser.Term.show,
    `Lean.Parser.Term.sort, `Lean.Parser.Term.structInst, `Lean.Parser.Term.structInstField,
    `Lean.Parser.Term.structInstFieldDef, `Lean.Parser.Term.structInstFieldEqns,
    `Lean.Parser.Term.structInstFields, `Lean.Parser.Term.structInstLVal, `Lean.Parser.Term.subst,
    `Lean.Parser.Term.sufficesDecl, `Lean.Parser.Term.syntheticHole, `Lean.Parser.Term.termReturn,
    `Lean.Parser.Term.termTry, `Lean.Parser.Term.termUnless, `Lean.Parser.Term.tuple,
    `Lean.Parser.Term.type, `Lean.Parser.Term.typeAscription, `Lean.Parser.Term.typeSpec,
    `Lean.Parser.Term.whereDecls, `Lean.Parser.Termination.decreasingBy,
    `Lean.Parser.Termination.suffix, `Lean.Parser.Termination.terminationBy,
    `Std.Legacy.Range.«term[:_]», `Std.Legacy.Range.«term[_:_:_]», `Std.Legacy.Range.«term[_:_]»,
    `Lean.Elab.Tactic.Ext.ext, `Lean.Parser.Tactic.Conv.conv, `Lean.Parser.Tactic.Conv.convRw__,
    `Lean.Parser.Tactic.Conv.convSeq, `Lean.Parser.Tactic.Conv.convSeq1Indented,
    `Lean.Parser.Tactic.Conv.lhs, `Lean.Parser.Tactic.Conv.rhs, `Lean.Parser.Tactic.Conv.unfold,
    `Lean.Parser.Tactic.rcasesPat.clear, `Lean.Parser.Tactic.rcasesPat.ignore,
    `Lean.Parser.Tactic.rcasesPat.one, `Lean.Parser.Tactic.rcasesPat.paren,
    `Lean.Parser.Tactic.rcasesPat.tuple, `Lean.Parser.Tactic.rintroPat.one]

def atoms : List String :=
  ["!", "!=", "#[", "#v[", "%", "&&", "&&&", "(", ")", "*", "+", "++", ",", "-", ".", "..", "/", "//",
    ":", "::", ":=", ";", "<", "<$>", "<+:", "<:+:", "<;>", "<<<", "<|", "=", "==", "=>", ">", ">>=",
    ">>>", "?", "@", "@[", "Prop", "Sort", "Type", "[", "]", "]'", "^", "^^^", "_", "`", "abbrev",
    "ac_rfl", "all_goals", "apply", "assumption", "at", "attribute", "break", "by", "by_cases", "calc",
    "cases", "catch", "change", "class", "classical", "clear", "congr", "constructor", "continue",
    "contradiction", "conv", "decide", "decreasing_by", "def", "deriving", "do", "done", "dsimp",
    "else", "end", "exact", "example", "exfalso", "ext", "extends", "finally", "first", "for", "from",
    "fun", "funext", "generalize", "generalizing", "have", "if", "import", "in", "include",
    "induction", "inductive", "inferInstanceAs", "infer_instance", "instance", "intro", "left", "let",
    "letI", "lhs", "local", "match", "matches", "module", "mut", "mutual", "namespace", "next",
    "nofun", "nomatch", "noncomputable", "obtain", "omega", "omit", "only", "open", "private",
    "protected", "public", "rcases", "rec", "refine", "rename_i", "repeat", "repeat'", "return",
    "revert", "rfl", "rhs", "right", "rintro", "rw", "rwa", "s!", "section", "set_option", "show",
    "simp", "simp_all", "simpa", "split", "structure", "subst", "suffices", "symm", "termination_by",
    "then", "theorem", "throwError", "throwErrorAt", "trivial", "try", "unfold", "universe", "unless",
    "using", "variable", "where", "with", "{", "|", "|>.", "||", "|||", "}", "¬", "·", "×", "‹", "›",
    "←", "→", "↓", "↔", "∀", "∃", "∅", "∈", "∉", "∘", "∣", "∧", "∨", "≠", "≤", "≥", "⊆", "⊕", "⊢", "▸",
    "⟨", "⟩"]

def leafKinds : List Name :=
  [`char, `fieldIdx, `hygieneInfo, `interpolatedStrLitKind, `name, `num, `scientific, `str,
    `Lean.Parser.Command.docComment, `Lean.Parser.Command.eoi, `Lean.Parser.Command.moduleDoc]

def simpleAttributes : List Name :=
  [`inline, `noinline, `always_inline, `reducible, `irreducible, `expose]

def options : List Name :=
  [`maxRecDepth, `maxHeartbeats, `exponentiation.threshold, `autoImplicit, `relaxedAutoImplicit,
    `warningAsError, `linter.missingDocs]

def configItems : List Name := [`kernel]

def derivingClasses : List Name :=
  [`DecidableEq, `BEq, `Repr, `Inhabited, `Hashable, `Ord, `Nonempty]

def configKeys : List Name :=
  [`name, `version, `description, `keywords, `license, `licenseFiles, `srcDir, `defaultTargets,
    `lintDriver, `lintDriverArgs, `lean_lib.name, `lean_lib.roots, `lean_lib.globs,
    `lean_exe.name, `lean_exe.root, `lean_exe.supportInterpreter]

def leanToolchain : String := "leanprover/lean4:v4.36.0"

structure FileRead where
  module : Name
  header : Syntax
  commands : List Syntax
  parsed : Bool
  scopedParsers : List Name

structure Reading where
  toolchainFile : Option String
  leanConfig : Bool
  configKeys : List Name
  openPaths : List String
  roots : List Name
  reached : List Name
  files : List FileRead
  unread : List (Name × String)

inductive Outcome where
  | admitted
  | refused
  | proofOnly
  | incomplete
  deriving DecidableEq, Repr

inductive Step where
  | read
  | build
  | rules
  deriving DecidableEq, Repr

inductive Report where
  | full (verdict : Regula.Closed.Verdict)
  | proofOnly
  | refused
  | incomplete
  deriving DecidableEq, Repr

end Regula.Language
