module

/-! # The two closed allowlists

The members of the allowlists of RG2006 and RG2007 (`specification/RegulaSpecification/Project.lean`).
A name that a list does not name is refused, an unknown one included, so a new option of Lean and a
new kind of registration are refused until a change of Regula reads them and adds them.

Each list holds exact names, compared whole. So `weak.linter.hashCommand` is not
`linter.hashCommand`, and an extension in another namespace is not the member that it resembles. No
claimed module can bring an extension of its own into a list: an extension exists only through an
`initialize`, which RG2007 refuses in a claimed module, and RG2004 refuses an import of a module of an
excluded target. A dependency's extension is a dependency's meta-code, which is trusted.

The members come from an observation at Lean v4.35.0, recorded in the specification
(`specification/README.md`, RG2006 and RG2007): the names on Regula's own build, on Acorn, a real
Mathlib project, and on the modules of Mathlib at the commit Acorn pins. Each extension was read at its
declaration in the source of that release: its entries are data that Lean or a tactic reads, and no
entry names code for Lean to run while it elaborates. -/

public section

namespace Regula.Allowlist

open Lean (Name)

/-- The options a claimed target may set, by the name Lake gives. None can stop a warning that Lean
reports by default, or a check of Lean, at any value.

- `autoImplicit` and `relaxedAutoImplicit`, which RG2006 requires at `false`.
- `warningAsError` turns warnings into errors, and `false` is its default. `debugAssertions`, which
  Lake's `debug` build type sets, keeps run-time assertions in compiled code.
- `linter.missingDocs` is off by default, so it stops no default warning.
- The resource limits: Lean stops with an error at a limit. `0` means no limit where a limit has that
  meaning. `exponentiation.threshold` is left out, because raising it stops a warning that Lean
  reports by default.
- `pp.unicode.fun` changes how a function prints. Mathlib's `lakefile.lean` sets it.
- Mathlib's linter set and its §6.7 exclusions, under `weak.`. Their defaults are off (`false` or `0`),
  so they stop no warning that Lean or Mathlib reports by default, read at Mathlib 56a00585:
  `Mathlib/Tactic/Linter/HashCommandLinter.lean:36`, `Header.lean:225-232` and `Style.lean:347`. -/
def options : List Name :=
  [`autoImplicit, `relaxedAutoImplicit,
    `warningAsError, `debugAssertions,
    `linter.missingDocs,
    `maxHeartbeats, `synthInstance.maxHeartbeats, `synthInstance.maxSize, `maxRecDepth,
    `maxSynthPendingDepth,
    `pp.unicode.fun,
    `weak.linter.mathlibStandardSet, `weak.linter.style.header, `weak.linter.style.header.license,
    `weak.linter.hashCommand, `weak.linter.style.longFile]

/-- The name of a private declaration of the module `_private.M`, with the components of its name. -/
def privateIn (m : Name) (components : List String) : Name :=
  components.foldl Name.str (Name.num m 0)

/-- What Lean records for an ordinary declaration, a module and the compiler's output. These entries
describe a declaration that the module has, or its compiled code, which RG3001 and RG3002 read. -/
def recorded : List Name :=
  [`Lean.declRangeExt, `Lean.docStringExt, `Lean.versoDocStringExt, `Lean.deprecatedModuleExt,
    `Lean.protectedExt, `Lean.noConfusionExt, `Lean.auxRecExt, `Lean.auxParentProjInfoExt,
    `Lean.projectionFnInfoExt, `Lean.classExtension, `Lean.noncomputableExt, `Lean.indirectModUseExt,
    `Lean.aliasExtension, `recExt, `reducibilityCore,
    `Lean.Meta.matcherLikeExt, `Lean.Meta.completionBlackListExt, `Lean.Meta.congrKindsExt,
    `Lean.Meta.funIndInfoExt, `Lean.Meta.eqnOptionsExt, `Lean.Meta.Match.Extension.extension,
    `Lean.Elab.WF.eqnInfoExt, `Lean.Elab.Structural.eqnInfoExt, `Lean.Elab.PartialFixpoint.eqnInfoExt,
    `Lean.IR.declMapExt, `Lean.Compiler.LCNF.monoTypeExt, `Lean.Compiler.LCNF.baseExt,
    `Lean.Compiler.LCNF.monoExt, `Lean.Compiler.LCNF.impureSigExt, `Lean.Compiler.LCNF.specExtension,
    `Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt,
    privateIn `_private.Lean.DocString.Extension ["Lean", "moduleDocExt"],
    privateIn `_private.Lean.DocString.Extension ["Lean", "versoModuleDocExt"],
    privateIn `_private.Lean.DocString.Extension ["Lean", "inheritDocStringExt"],
    privateIn `_private.Lean.Compiler.ModPkgExt ["Lean", "modPkgExt"],
    privateIn `_private.Lean.Structure ["Lean", "structureExt"],
    privateIn `_private.Lean.ExtraModUses ["Lean", "extraModUses"],
    privateIn `_private.Lean.ExtraModUses ["Lean", "isExtraRevModUseExt"],
    privateIn `_private.Lean.AuxRecursor ["Lean", "sparseCasesOnExt"],
    privateIn `_private.Lean.Util.CollectAxioms ["Lean", "exportedAxiomsExt"],
    privateIn `_private.Lean.OriginalConstKind ["Lean", "privateConstKindsExt"],
    privateIn `_private.Lean.Namespace ["Lean", "namespacesExt"],
    privateIn `_private.Lean.Meta.MethodSpecs ["Lean", "methodSpecsAttr"],
    privateIn `_private.Lean.Meta.Constructions.SparseCasesOn ["Lean", "Meta", "sparseCasesOnInfoExt"],
    privateIn `_private.Lean.Compiler.LCNF.MonoTypes
      ["Lean", "Compiler", "LCNF", "trivialStructureInfoExt"],
    privateIn `_private.Lean.Compiler.LCNF.ToImpureType
      ["Lean", "Compiler", "LCNF", "impureTrivialStructureInfoExt"],
    privateIn `_private.Lean.Compiler.LCNF.ToImpureType ["Lean", "Compiler", "LCNF", "impureTypeExt"],
    privateIn `_private.Lean.Compiler.LCNF.ToImpureType ["Lean", "Compiler", "LCNF", "ctorLayoutExt"],
    privateIn `_private.Lean.Compiler.LCNF.Specialize
      ["Lean", "Compiler", "LCNF", "Specialize", "specCacheExt"]]

/-- The entries of Lean's own attributes that hold a fact about a declaration: a lemma that a tactic
uses, a flag that the elaborator or the compiler reads, or a mark for a person. -/
def attributes : List Name :=
  [`Lean.Meta.instanceExtension, `Lean.Meta.defaultInstanceExtension, `Lean.Meta.simpExtension,
    `Lean.Meta.congrExtension, `Lean.Meta.Grind.grindExt, `Lean.Meta.Ext.extExtension,
    `Lean.Meta.NormCast.normCastExt.up, `Lean.Meta.NormCast.normCastExt.down,
    `Lean.Meta.NormCast.normCastExt.squash, `Lean.Meta.NormCast.pushCastExt, `Lean.Meta.coeExt,
    `Lean.Meta.Rfl.reflExt, `Lean.Meta.Symm.symmExt, `Lean.Meta.customEliminatorExt,
    `Lean.Meta.unificationHintExtension, `Lean.Meta.recursorAttribute, `Lean.defeqAttr,
    `Lean.backwardDefeqAttr, `Lean.matchPatternAttr, `Lean.Elab.Term.elabAsElim,
    `Lean.Elab.Term.elabWithoutExpectedTypeAttr, `Lean.Linter.deprecatedAttr, `Lean.ppNoDotAttr,
    `Lean.ppUsingAnonymousConstructorAttr, `Lean.Compiler.inlineAttrs, `Lean.Compiler.specializeAttr]

/-- A point at which compiled code departs from a kernel value, or code outside the toolchain. Lean's
compiler reads these entries, and no elaboration runs them. RG3001 and RG3002 decide them. -/
def departures : List Name :=
  [`Lean.Compiler.implementedByAttr, `Lean.Compiler.CSimp.ext, `Lean.externAttr]

/-- The entries of Mathlib's and Batteries' attributes that hold a fact about a declaration, read at
Mathlib 56a00585 and the Batteries it pins: `Mathlib/Tactic/Translate/ToAdditive.lean:253-256`,
`Mathlib/Tactic/Translate/ToDual.lean:125-128`, `Mathlib/Tactic/Simps/Basic.lean:415`,
`Mathlib/Tactic/GCongr/Core.lean:217`, `Mathlib/Tactic/FunProp/Theorems.lean:121-259`,
`Mathlib/Tactic/FunProp/Decl.lean:49`, `Mathlib/Tactic/Push/Attr.lean:47-80`,
`Batteries/Tactic/Alias.lean:61`, `Batteries/Tactic/Trans.lean:30` and
`Batteries/Tactic/Lint/Basic.lean:183`. These are data, and the attribute that writes them is a
dependency's meta-code. A Mathlib attribute that registers code, such as `norm_num`, `positivity` or
`aesop` with a tactic, is not on the list. -/
def mathlib : List Name :=
  [`Mathlib.Tactic.ToAdditive.translations, `Mathlib.Tactic.ToAdditive.dontTranslateAttr,
    `Mathlib.Tactic.ToDual.translations, `Mathlib.Tactic.ToDual.dontTranslateAttr,
    `Simps.structureExt, `simpsAttr, `Mathlib.Tactic.GCongr.gcongrExt,
    `Mathlib.Meta.FunProp.lambdaTheoremsExt, `Mathlib.Meta.FunProp.functionTheoremsExt,
    `Mathlib.Meta.FunProp.transitionTheoremsExt, `Mathlib.Meta.FunProp.morTheoremsExt,
    `Mathlib.Meta.FunProp.funPropDeclsExt, `Mathlib.Tactic.Push.pushExt,
    `Mathlib.Tactic.Push.pullExt, `Batteries.Tactic.Alias.aliasExt, `Batteries.Tactic.transExt,
    `Batteries.Tactic.Lint.nolintAttr]

/-- The environment extensions a claimed module may have entries of. -/
def extensions : List Name := recorded ++ attributes ++ departures ++ mathlib

/-- Whether a claimed target may set the option `n` (RG2006). -/
def admitsOption (n : Name) : Bool := options.contains n

/-- Whether a claimed module may have entries of the environment extension `n` (RG2007). -/
def admitsExtension (n : Name) : Bool := extensions.contains n

end Regula.Allowlist
