import RegulaCore.Guidance

/-! # Offline rule guidance executable

`regula`: offline rule guidance for agents and humans (`lake exe regula explain <RULE-ID>`,
`rules`, `agent-guide`, `skill`). It prints `Regula.Guidance.output` of the command that the
proved parser `Regula.Guidance.parseCommand` admits; the texts are generated from the
installed registry, so they match this build and need no network. -/

def main (args : List String) : IO UInt32 := do
  match Regula.Guidance.parseCommand args with
  | .ok command =>
      IO.print (Regula.Guidance.output command)
      if command == .help then IO.println ""
      return 0
  | .error message =>
      IO.eprintln Regula.Guidance.usage
      IO.eprintln s!"regula: {message}"
      return 2
