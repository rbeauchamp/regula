module

public import Lean.Environment
public import Std.Data.HashMap.Basic
import all Lean.Compiler.LCNF.Specialize

/-! # The specializations that Lean's compiler records

Lean's compiler records each specialization that it makes in the specialization cache of the module
that compiles it, as a key and the specialization's name. The key is `fun params => f args`, whose
head constant `f` is the declaration that it specializes (Lean v4.34.1
`Lean/Compiler/LCNF/Specialize.lean:30-42`, `:288-301` and `:409-434`). The cache is private data of
its module, which a root that is not a `module` imports with the rest
(`Lean/Elab/Import.lean:150-156`, `Lean/Environment.lean:2180-2190`). The name of a declaration
never makes it a specialization here. -/

public section

namespace Regula.Specialization

open Lean Lean.Compiler.LCNF.Specialize

/-- Each specialization that Lean's compiler recorded in `env`, with the declaration that it
specializes. An entry counts only in the cache of the module whose compiled code holds the
specialization (`Lean/Environment.lean:2345-2347`), or of the environment's own commands for one
that no imported module holds. A declaration that a source defines, a constant of the kernel, is
never a specialization.
Assumes: only Lean's compiler writes the specialization caches of Regula's compiled modules
(`Lean/Compiler/LCNF/Specialize.lean:41-42` and `:434`); no Regula command writes one. A command
that calls the public `cacheSpec` or otherwise changes the environment is a deliberate environment
mutation, outside the honest-code boundary, and can add an entry. -/
def origins (env : Environment) : Std.HashMap Name Name := Id.run do
  let specialized (entry : CacheEntry) : Option Name :=
    entry.key.getLambdaBody.getAppFn.constName?
  let mut origins := {}
  for index in [:env.header.moduleNames.size] do
    for entry in PersistentEnvExtension.getModuleEntries specCacheExt env index do
      if (env.getModuleIdxFor? entry.declName).map (·.toNat) == some index &&
          !env.contains entry.declName then
        if let some origin := specialized entry then origins := origins.insert entry.declName origin
  for entry in specCacheExt.getEntries env do
    if (env.getModuleIdxFor? entry.declName).isNone && !env.contains entry.declName then
      if let some origin := specialized entry then origins := origins.insert entry.declName origin
  return origins

end Regula.Specialization
