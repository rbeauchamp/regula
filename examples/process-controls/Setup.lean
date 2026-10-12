import Lean

/-! Setup stub for the exact approved wrapper control. -/

/-- Complete the controlled setup, recording that it ran. -/
def main : IO UInt32 := do
  let some marker ← IO.getEnv "REGULA_PROCESS_SETUP_MARKER"
    | throw <| IO.userError "setup control has no marker"
  IO.FS.writeFile marker "setup ran\n"
  return 0
