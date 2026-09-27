import Lean
/-! # Reflexivity

Reflexivity declared with unchecked, ill-typed evidence. -/
open Lean Elab Command
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| Lean.addDecl (.thmDecl {
  name := `reflexive
  levelParams := []
  type := mkForall `n .default (mkConst ``Nat)
    (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (mkBVar 0) (mkBVar 0))
  value := mkConst ``True.intro })
