import RegulaPolicy.Domain
import Lean.Compiler.IR.EmitUtil
import Lean.Elab.Command

/-! # The effects in the compiled code of an adopter's program

Regula's checker has three effects: it loads the finished build, it prints its report and it sets
its exit code. `check` makes the build of a program's root module fail when the compiled code of a
module that the program links, other than the toolchain's, starts a process, writes or removes a
file, or makes or moves an entry, unless the program names that call. The `lint` executable names
none, and the `regula` executable names only the setup files that `init` writes.

## How it reads the program

Each input is read through Lean's own record of it:

- The modules the program links: the imports of the environment in which its root module is
  elaborated (`Environment.header.moduleNames`). A module outside the toolchain's roots
  (`RegulaPolicy.ToolchainRoot`) is the program's own.
- The compiled code of those modules: each declaration of Lean's IR store (`Lean.IR.declMapExt`,
  `getDecls`), which holds `main`, the initializers and the zero-argument declarations that a
  compiled module computes when it starts. A declaration that nothing calls counts too, so the check
  needs no model of what runs. A root module whose store holds no `main` is refused, so finding
  nothing is never a pass.
- A call: a full or a partial application in the compiled body (`bodyCalls`). A callee is an effect
  when it is in `primitives`, when it is an `extern` declaration bound to a C function of `symbols`
  (`boundAmong`), or when it is `IO.FS.Handle.mk` or another declaration bound to its C function
  with any mode but the literal `IO.FS.Mode.read`. The boxed and reduced variants that the compiler
  makes of a declaration count as that declaration (`baseOf`). An `extern` declaration of the
  program's own modules is refused whatever it binds: its C function is outside these lists.

## Boundaries

`check` walks every call from each declaration of the toolchain that the program's own code calls,
and refuses one that reaches an effect or code it cannot read. The exception is `lakeLoad`, Lake's
load of a workspace, which runs Git and Lean and writes the compiled configuration below
`.lake/config`, and whose elaboration of a `lakefile.lean` runs project code: those effects are
Lake's, as they are when `lake build` loads the same workspace. The walk reads calls, so a function
that a toolchain declaration reaches only through a value it is given is read at the place that
makes the value, when that place is compiled code that the walk reads. A write through a handle that
an admitted opening made, or to a standard stream, is not a call that the check finds.

`check` is a check at build time, with no theorem. Its coverage rests on Lean's store of compiled
code (`declMapExt`, `findEnvDecl`), and nothing proves that a build that passes has no such call. -/

namespace Regula.Effects

open Lean IR

/-- The declarations of Lean's library that start a process, write or remove a file, or make, move
or change an entry, by a read of `Init/System/IO.lean` at Lean v4.35.0 and of the writers of a
module. -/
def primitives : List Name :=
  [``IO.Process.spawn, ``IO.Process.output, ``IO.Process.run, ``IO.FS.removeFile, ``IO.FS.removeDir,
    ``IO.FS.removeDirAll, ``IO.FS.rename, ``IO.FS.createDir, ``IO.FS.createDirAll, ``IO.FS.writeFile,
    ``IO.FS.writeBinFile, ``IO.FS.withFile, ``IO.FS.createTempFile, ``IO.FS.createTempDir,
    ``IO.FS.withTempFile, ``IO.FS.withTempDir, ``IO.setAccessRights, ``Lean.writeModule,
    ``Lean.saveModuleData, ``Lean.saveModuleDataParts]

/-- The C functions of the Lean 4.35.0 runtime that those declarations reach: a declaration of any
name that is bound to one of them has that effect. -/
def symbols : List String :=
  ["lean_io_process_spawn", "lean_io_remove_file", "lean_io_remove_dir", "lean_io_rename",
    "lean_io_create_dir", "lean_io_hard_link", "lean_io_prim_handle_truncate",
    "lean_io_create_tempfile", "lean_io_create_tempdir", "lean_chmod",
    "lean_compacted_region_save"]

/-- The C function of `IO.FS.Handle.mk`, which opens a file in the mode of its second argument. -/
def openSymbol : String := "lean_io_prim_handle_mk"

/-- Whether the entry of an `extern` attribute calls the C function `symbol`: by its name, or in
the C text of an inline entry. -/
def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

/-- The C function of `candidates` that `name` is bound to, when it is an `extern` declaration bound
to one. -/
def boundAmong (env : Environment) (candidates : List String) (name : Name) : Option String :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) => candidates.find? fun symbol => data.entries.any (bindsTo symbol)
  | _ => none

/-- `name` without the suffixes of the compiled variants of a declaration. -/
def baseOf (name : Name) : Name :=
  let base := if name matches .str _ "_boxed" then name.getPrefix else name
  if base matches .str _ "_redArg" then base.getPrefix else base

/-- What the check reads of a compiled body: each variable that the body binds to a literal number,
with the number, and each call that it makes, with its arguments and whether it is a partial
application. -/
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

/-- The effect of a call of `callee` with `args` from a body whose literals are `literals`, by the
declaration that has it. An opening has an effect unless it is a full application of
`IO.FS.Handle.mk` whose mode is a variable that the body binds to the literal 0, which is
`IO.FS.Mode.read`. -/
def effectOf (env : Environment) (literals : Array (VarId × Nat)) (callee : Name) (args : Array Arg)
    (partialCall : Bool) : Option Name :=
  let base := baseOf callee
  if primitives.contains base || (boundAmong env symbols base).isSome then some base
  else if (boundAmong env [openSymbol] base).isSome then
    match args[1]? with
    | some (Arg.var mode) =>
      if base == ``IO.FS.Handle.mk && !partialCall && literals.contains (mode, 0) then none
      else some base
    | _ => some base
  else none

/-- The compiled declarations of the modules of `env` outside the toolchain, those of its own
commands included. A module of the module system stores `extern` stubs for its public declarations
in its `.olean` and their code in its `.ir` (`Lean/Compiler/IR/CompilerM.lean:89-110`), so each name
is read through Lean's own lookup, `findEnvDecl`, which prefers the code. -/
def ownDeclarations (env : Environment) : Array Decl := Id.run do
  let mut decls := (getDecls env).toArray
  let mut seen : NameSet := {}
  for module in env.header.moduleNames do
    unless decide (RegulaPolicy.ToolchainRoot module.getRoot) do
      if let some index := env.getModuleIdx? module then
        for entry in declMapExt.getModuleIREntries env index ++
            declMapExt.getModuleEntries env index do
          unless seen.contains entry.name do
            seen := seen.insert entry.name
            if let some decl := findEnvDecl env entry.name then decls := decls.push decl
  return decls

/-- Whether the compiled name `name` is part of the source declaration `source`: its own compiled
parts, or a specialization that the compiler made for it, whose name holds it after `_at_`. -/
def partOf (source name : Name) : Bool :=
  (name.toString.splitOn source.toString).length > 1

/-- Each call of `decls` with an effect (`effectOf`) that `admitted` does not name, and each
`extern` declaration among them, as a line of the refusal: an `extern` stub is compiled code that
the check cannot read, and any other binds a C function outside its lists. `admitted` names a call
by the declaration of a source that makes it and the declaration with the effect. -/
def refusals (env : Environment) (decls : Array Decl) (admitted : List (Name × Name)) :
    Array String := Id.run do
  let mut found := #[]
  for decl in decls do
    match decl with
    | .extern name .. => found := found.push s!"{name} is an extern declaration"
    | .fdecl (f := name) (body := body) .. =>
      let (literals, calls) := bodyCalls body
      for (callee, args, partialCall) in calls do
        if let some effect := effectOf env literals callee args partialCall then
          unless admitted.any (fun (source, named) => partOf source name && named == effect) do
            found := found.push s!"{name} calls {effect}"
  return found

/-- The bound on the declarations that `reaching` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- The declarations of Lake that make up its load of a workspace, whose own effects are Lake's. -/
def lakeLoad : List Name := [`Lake.loadWorkspace, `Lake.LeanInstall.get]

/-- Each declaration of `callees`, the toolchain's declarations that the program's own code calls,
outside `lakeLoad`, whose compiled code reaches an effect (`effectOf`) or code that the check cannot
read, with what it reaches. It follows every call from each. A declaration that a finished walk
found clean is not read again. A walk that stops at the bound counts as reaching something. -/
def reaching (env : Environment) (callees : Array Name) : Array (Name × String) := Id.run do
  let mut clean : NameSet := {}
  let mut found := #[]
  for callee in callees do
    if lakeLoad.contains (baseOf callee) || primitives.contains (baseOf callee) then continue
    let mut seen : NameSet := {}
    let mut work := [callee]
    let mut hit : Option String := none
    for _ in [:maxDeclarations] do
      let name :: rest := work | break
      work := rest
      if hit.isSome then break
      if clean.contains name || seen.contains name then continue
      seen := seen.insert name
      match findEnvDecl env name with
      | some (.fdecl (body := body) ..) =>
        let (literals, calls) := bodyCalls body
        for (next, args, partialCall) in calls do
          if let some effect := effectOf env literals next args partialCall then
            hit := some effect.toString
          else work := next :: work
      | some (.extern _ _ _ data) =>
        if data.entries.any (· matches .opaque) then hit := some s!"{name}, whose code is unread"
      | none => hit := some s!"{name}, whose code is unread"
    match hit, work with
    | some effect, _ => found := found.push (callee, effect)
    | none, [] => clean := seen.foldl (·.insert ·) clean
    | none, _ => found := found.push (callee, "more than the walk's bound")
  return found

/-- The toolchain's declarations that `decls` call. -/
def toolchainCallees (decls : Array Decl) : Array Name := Id.run do
  let own : NameSet := decls.foldl (fun names decl => names.insert decl.name) {}
  let mut callees : NameSet := {}
  for decl in decls do
    if let .fdecl (body := body) .. := decl then
      for (callee, _, _) in (bodyCalls body).2 do
        unless own.contains callee do callees := callees.insert callee
  return callees.toArray

/-- Fail the build of the program whose root module this command ends unless the compiled code of
its own modules has no effect that `admitted` does not name (`refusals`), and each declaration of the
toolchain that it calls reaches none, except those of `lakeLoad` (`reaching`). It fails when the
store holds no `main`.

This is a check at build time, with no theorem. Its coverage rests on Lean's store of compiled code
(`declMapExt`, `findEnvDecl`), and nothing proves that a build that passes has no such call. -/
def check (admitted : List (Name × Name) := []) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let decls := ownDeclarations env
  unless decls.any (·.name == `main) do
    throwError "the compiled code of this module holds no `main`, so there is no program to check"
  let reached := (reaching env (toolchainCallees decls)).map fun (callee, effect) =>
    s!"{callee}, of the toolchain, reaches {effect}"
  let found := refusals env decls admitted ++ reached
  unless found.isEmpty do
    throwError "this program may only load the finished build, print and set its exit code, and \
      its compiled code does more:\n{"\n".intercalate found.toList}"

end Regula.Effects
