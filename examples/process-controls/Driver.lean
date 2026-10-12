import Lean

/-! Wrapper-selection fixture, not an acceptance driver. -/

/-- Record the selected driver phase and return its distinct result. -/
def main (args : List String) : IO UInt32 := do
  if args.head? == some "--begin-attempt" then
    let some marker ← IO.getEnv "REGULA_PROCESS_BEGIN_MARKER"
      | throw <| IO.userError "begin-attempt control has no marker"
    IO.FS.writeFile marker "begin ran\n"
    return 0
  let some marker ← IO.getEnv "REGULA_PROCESS_DRIVER_MARKER"
    | throw <| IO.userError "driver control has no marker"
  IO.FS.writeFile marker "driver ran\n"
  return 37
