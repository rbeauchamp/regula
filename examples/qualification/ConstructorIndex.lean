/-! Collector qualification on the declarations the selected compiler generates and on isolated,
unchecked copies. Which controls run depends on that compiler's capability, not on whether the
revision is a candidate: without `getObjTagNat`, as on Lean 4.34.0 and 4.35.0-rc3, which generate
no wrapper, the control checks only that the observer finds no constructor-index helper for any of
the six parents; with it, as on source compiler `6751f97`, it also exercises the observer's
positive path, `ConstructorIndexHelperOK` admission, the transport round trip and the mutation
controls.
The altered environments are never exported or executed. This checks the actual observer and
transport, not kernel admission or native correspondence of the mutated declarations.
The harness prefixes imports and the positive fixture's source so its declarations are local. -/

open Lean Elab Command
open scoped Regula.Report

run_cmd do
  let _ : BEq QuotKind := ⟨fun a b => match a, b with
    | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
    | _, _ => false⟩
  let _ : BEq QuotVal := ⟨fun ⟨a, k⟩ ⟨b, l⟩ => a == b && k == l⟩
  let _ : BEq InductiveVal := ⟨fun
    ⟨a, p, i, all, cs, n, r, u, f⟩ ⟨b, p', i', all', cs', n', r', u', f'⟩ =>
      a == b && p == p' && i == i' && all == all' && cs == cs' && n == n' &&
        r == r' && u == u' && f == f'⟩
  let _ : BEq ConstantInfo := ⟨fun a b => match a, b with
    | .axiomInfo a, .axiomInfo b => a == b
    | .defnInfo a, .defnInfo b => a == b
    | .thmInfo a, .thmInfo b => a == b
    | .opaqueInfo a, .opaqueInfo b => a == b
    | .quotInfo a, .quotInfo b => a == b
    | .inductInfo a, .inductInfo b => a == b
    | .ctorInfo a, .ctorInfo b => a == b
    | .recInfo a, .recInfo b => a == b
    | _, _ => false⟩
  let original ← getEnv
  let observe (env : Environment) (helper : Name) := liftTermElabM do
    let saved ← saveState
    try
      setEnv env
      Regula.Collect.constructorIndexObservation env helper
    finally saved.restore
  let check (label : String) (env : Environment) (helper : Name)
      (expected : Option (Name × Name)) := do
    unless (← observe env helper) == expected do
      throwError "constructor-index observer: {label}"
  let mut parents : Array Name := #[]
  for (name, info) in original.constants.map₂ do
    if let .inductInfo _ := info then parents := parents.push name
  unless parents.size == 6 do throwError "constructor-index control lost a parent"
  let newCompiler := original.contains `getObjTagNat
  for parent in parents do
    let base := parent.str "ctorIdx"
    let helper := base.str "_impl"
    let excluded := parent == `FixturesSingle || parent == `FixturesPredicate
    check s!"generated {parent}" original helper
      (if newCompiler && !excluded then some (parent, base) else none)
  if !newCompiler then return
  let parent := `FixturesConstructorIndex
  let baseName := parent.str "ctorIdx"
  let helperName := baseName.str "_impl"
  let some (.defnInfo helper) := original.find? helperName | throwError "missing real helper"
  let some (.defnInfo base) := original.find? baseName | throwError "missing real base"
  let some (.defnInfo cases) := original.find? (mkCasesOnName parent)
    | throwError "missing real eliminator"
  -- Kernel insertion changes a local constant; retain the elaborator's replacement metadata.
  let replace (decl : DefinitionVal) := do
    let kernel ← ofExceptKernelException <|
      original.toKernelEnv.addDeclWithoutChecking (.defnDecl decl)
    let changed := Compiler.implementedByAttr.ext.setState (Environment.ofKernelEnv kernel)
      (Compiler.implementedByAttr.ext.getState original)
    unless changed.find? decl.name == some (.defnInfo decl) do
      throwError "constructor-index mutation not visible: {decl.name}"
    unless changed.toKernelEnv.constants.map₁ == original.toKernelEnv.constants.map₁ do
      throwError "constructor-index mutation changed imported constants"
    for (name, info) in original.constants.map₂ do
      unless changed.find? name == some (if name == decl.name then .defnInfo decl else info) do
        throwError "constructor-index mutation changed another local constant: {name}"
      unless Compiler.getImplementedBy? changed name == Compiler.getImplementedBy? original name &&
          isExtern changed name == isExtern original name do
        throwError "constructor-index mutation changed local metadata: {name}"
    return changed
  check "unchanged declaration update" (← replace helper) helperName (some (parent, baseName))
  let body := helper.value.replace fun e =>
    if e.isAppOfArity `getObjTagNat 2 then some (mkRawNatLit 0) else none
  let callee := helper.value.replace fun e =>
    if e.isConstOf `getObjTagNat then some (mkConst ``Nat.succ) else none
  let argument := helper.value.replace fun e =>
    if e.isAppOfArity `getObjTagNat 2 then some (mkApp e.appFn! (mkBVar 1)) else none
  let branch := base.value.replace fun e =>
    if e == mkRawNatLit 0 then some (mkRawNatLit 1) else none
  for (label, decl) in #[
      ("helper computation", {helper with value := body}),
      ("helper primitive", {helper with value := callee}),
      ("helper argument", {helper with value := argument}),
      ("helper type", {helper with type := mkConst ``Nat}),
      ("helper universes", {helper with levelParams := []}),
      ("helper group", {helper with all := []}),
      ("helper hints", {helper with hints := .abbrev}),
      ("helper safety", {helper with safety := .safe}),
      ("helper partial", {helper with safety := .partial}),
      ("base alternative", {base with value := branch}),
      ("base type", {base with type := mkConst ``Nat}),
      ("base universes", {base with levelParams := []}),
      ("base group", {base with all := []}),
      ("base hints", {base with hints := .opaque}),
      ("base safety", {base with safety := .unsafe}),
      ("eliminator value", {cases with value := mkRawNatLit 0}),
      ("eliminator type", {cases with type := mkConst ``Nat}),
      ("eliminator group", {cases with all := []}),
      ("eliminator universes", {cases with levelParams := []})] do
    check label (← replace decl) helperName none
    check s!"restored {label}" original helperName (some (parent, baseName))
  for (label, sourceName, target) in #[
      ("base replacement", baseName, baseName),
      ("helper replacement", helperName, baseName)] do
    let changed := Compiler.implementedByAttr.ext.modifyState original fun state =>
      (state.1, state.2.insert sourceName target)
    unless Compiler.getImplementedBy? changed sourceName == some target do
      throwError "constructor-index replacement mutation not visible: {sourceName}"
    for name in #[baseName, helperName] do
      if name != sourceName &&
          Compiler.getImplementedBy? changed name != Compiler.getImplementedBy? original name then
        throwError "constructor-index mutation changed another replacement: {name}"
    check label changed helperName none
    check s!"restored {label}" original helperName (some (parent, baseName))
  let h ← Regula.Collect.declaration helperName .replayCandidate
  let b ← Regula.Collect.declaration baseName .replayCandidate
  let t ← Regula.Collect.declaration parent .replayCandidate
  unless RegulaPolicy.authorizedConstructorIndexHelpers #[t, b, h] == #[helperName] do
    throwError "real constructor-index inventory was not authorized"
  let encoded := toJson h
  let .ok decoded := (fromJson? encoded : Except String Regula.Report.Declaration)
    | throwError "constructor-index transport refused the real record"
  unless decoded == h do throwError "constructor-index transport changed the real record"
  let fields ← ofExcept encoded.getObj?
  let missing := Json.mkObj (fields.toList.filter (·.1 != "constructorIndex"))
  if (fromJson? missing : Except String Regula.Report.Declaration).isOk then
    throwError "constructor-index transport accepted a missing observation"
  let .ok restored := (fromJson? encoded : Except String Regula.Report.Declaration)
    | throwError "constructor-index restored transport refused"
  unless restored == h do throwError "constructor-index restored transport changed the record"
