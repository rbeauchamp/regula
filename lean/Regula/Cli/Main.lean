import Regula.Effects
import Regula.Cli.Setup

/-! # The `regula` executable

`regula`: project setup and offline rule guidance for agents and humans (`lake exe regula init`,
`doctor`, `explain <RULE-ID>`, `rules`, `agent-guide`, `skill`). It runs the invocation that the
proved parser `Regula.Guidance.parseInvocation` admits: the printing commands print
`Regula.Guidance.output`, generated from the installed registry, so they match this build and
need no network; `init` and `doctor` run `Regula.Cli.Setup` in the project at the working
directory. -/

open Regula.Cli.Setup in
/-- Run `action` on the project at the working directory; an error that escapes it is printed
and exits 1. -/
def inProject (command : String) (action : System.FilePath → IO UInt32) : IO UInt32 := do
  try
    initializeSearchPath
    action (← IO.currentDir)
  catch error =>
    IO.eprintln s!"regula {command}: {error}"
    return 1

/-- Run the invocation `parseInvocation` admits, or print the usage and the parse error to standard
error and return 2. `init` and `doctor` return 0 when the setup is complete and 1 otherwise. -/
def regulaMain (args : List String) : IO UInt32 := do
  match Regula.Guidance.parseInvocation args with
  | .ok (.print command) =>
      IO.print (Regula.Guidance.output command)
      if command == .help then IO.println ""
      return 0
  | .ok (.init guidance) => inProject "init" (Regula.Cli.Setup.init guidance)
  | .ok .doctor => inProject "doctor" Regula.Cli.Setup.doctor
  | .error message =>
      IO.eprintln Regula.Guidance.usage
      IO.eprintln s!"regula: {message}"
      return 2

/-- The `regula` executable: `regulaMain` on the command-line arguments. -/
def main : List String → IO UInt32 :=
  regulaMain


-- The program prints, and `init` writes the setup files of the project that it sets up. The build
-- of this module fails when the compiled code of a module outside the toolchain that it links starts
-- a process or removes a file, or writes at another place, or calls a declaration of the toolchain
-- that reaches one (`Regula.Effects.check`). The two of `Regula.Effects.lakeLoad` are Lake's load
-- of the workspace, whose own Git, Lean and `.lake/config` effects are Lake's.
run_cmd Regula.Effects.check (admitted := [
  (`Regula.Cli.Setup.write, ``IO.FS.createDirAll),
  (`Regula.Cli.Setup.write, ``IO.FS.writeFile),
  (`Regula.Cli.Setup.restore, ``IO.FS.writeFile)])
