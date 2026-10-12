import Lean

/-! Raw external-boundary baseline, outside any claimed program. -/

/-- Launch Lake with the deliberately unsafe native override and capture its outcome. -/
def main (args : List String) : IO UInt32 := do
  let [lake, project, overrideName, name] := args
    | throw <| IO.userError "raw native control requires lake, project, override and tool"
  let result ← IO.Process.output {
    cmd := lake
    args := #["build", "ProcessFixture:static"]
    cwd := some project
    env := #[(overrideName, some name)] }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
