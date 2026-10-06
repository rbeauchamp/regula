module

public import Lean.Attributes

/-! # Decision registration

Explicit selection of the functions a project declares to be decisions: a parser, decoder,
validator or admission function whose result accepts or refuses its input.
Registration identifies the RG1008 obligation: the function is the implementation of a decision
contract of its inventory (an `ExecutableContract` whose requirement is a `Regula.DecidesSoundly`,
`Regula.DecidesCompletely` or `Regula.Decides`, or the structure of the same name in
`Regula.Dependent`), or its result type is `Decidable _`.
A registration adds that requirement and waives nothing. It does not certify that every function
that acts as a checker is registered, or that a registered contract's specification is the
intended one.

A function is registered where it is declared (`@[regula_decision] def f`) or, for a function
whose module cannot import this one, in a module of the same inventory that imports it
(`attribute [regula_decision] f`). The attribute itself accepts any declaration: which
declarations an audit owns is not known while a file is elaborated. The audit refuses a
registration that one of its modules writes for a declaration outside its inventory
(`Regula.Collect.ownedDecisionRegistrations`), since it could not decide that requirement.

A file that is not a `module` imports this module with `import Regula.Decision`. A `module`
imports it with `meta import Regula.Decision`: the attribute is needed only while the file is
elaborated, and under that import Lean refuses a definition of the file that would run this
module's imports. The extension that holds the registrations is an ordinary definition, not a
`meta` one, so the collector reads them through it (`Regula.Collect.declaration`). -/

public section

namespace Regula

/-- The declarations the current module registers with `@[regula_decision]`. Lean saves them with
that module and loads them wherever the module is imported, so a registration is kept by the
module that writes it: the one that declares the function, or one that imports it. As Lean's own
tag attributes do, a registration of a declaration that is private to its module is saved for
importers that load the module's private data only. -/
initialize decisionExtension : Lean.PersistentEnvExtension Lean.Name Lean.Name Lean.NameSet ←
  Lean.registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun _ _ => pure {}
    addEntryFn := fun registered declaration => registered.insert declaration
    exportEntriesFnEx := fun env registered =>
      let all := registered.foldl (fun names name => names.push name) #[]
        |>.qsort Lean.Name.quickLt
      let exported := all.filter ((env.setExporting true).contains (skipRealize := false))
      { exported, server := exported, «private» := all }
    replay? := some fun _ replayed constants registered =>
      constants.foldl (init := registered) fun registered constant =>
        if replayed.contains constant then registered.insert constant else registered
  }

/-- `@[regula_decision]` registers a declaration of the current module or of an imported one. It
is applied after compilation: Lean applies an attribute of the earlier application time to the
`_unary` or `_mutual` definition it generates for a function defined by well-founded recursion as
well, and that definition is not the function the project registered. Applied after compilation,
the registration is on the declaration that carries the attribute and on no other, so the
collector and the policy need no exemption for a generated copy. -/
initialize
  Lean.registerBuiltinAttribute {
    ref := ``decisionExtension
    name := `regula_decision
    descr := "Marks a function as a decision that must state which direction it proves."
    applicationTime := .afterCompilation
    add := fun declaration source kind => do
      Lean.Attribute.Builtin.ensureNoArgs source
      unless kind == .global do Lean.throwAttrMustBeGlobal `regula_decision kind
      let env ← Lean.getEnv
      unless decisionExtension.toEnvExtension.asyncMayModify env declaration do
        Lean.throwAttrNotInAsyncCtx `regula_decision declaration env.asyncPrefix?
      Lean.modifyEnv fun env =>
        decisionExtension.addEntry (asyncDecl := declaration) env declaration
  }

/-- Every declaration `@[regula_decision]` registers in `env`: those the current module
registers and those every loaded module does, each of which is the module that declares the
function or one that imports it. A registration only adds the RG1008 requirement, so every loaded
registration counts, whichever module wrote it. One pass over the loaded modules computes the
set; a caller that asks about many declarations of one environment computes it once
(`Regula.Collect.ContractScope`). -/
def decisionRegistrations (env : Lean.Environment) : Lean.NameSet :=
  (Array.range env.header.moduleNames.size).foldl (init := decisionExtension.getState env)
    fun registered index =>
      (decisionExtension.getModuleEntries env index).foldl (init := registered)
        fun registered declaration => registered.insert declaration

end Regula
