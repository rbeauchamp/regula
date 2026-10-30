import Regula.Removal
import Regula.TaskManagerCheck
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

/-- The refusal of an invocation in a process without Lean's task manager
(`Regula.TaskManager.guard`): its arguments name no result destination, so it marks none, and it
returns 1. -/
def refuseRegula (_reason : String) (_args : List String) : IO UInt32 :=
  pure 1

/-- The `regula` executable: `regulaMain` on the command-line arguments. A process without Lean's
task manager is refused before the invocation runs, with exit code 1
(`Regula.TaskManager.guard`). -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "regula" refuseRegula regulaMain

-- The removals and the writes that the compiled code of the program reaches from its roots
-- (`Regula.Removal.rawRemovals`) are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists, and those named here, each by the declaration of a source
-- that makes it: the build of this module fails otherwise, and when a name here admits no call
-- (`Regula.Removal.checkProgram`). The program elaborates Lean source, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true) (named := [
  -- The configuration that `regula setup` writes in the project that it sets up, and its
  -- restoration when the setup stops.
  (`Regula.Cli.Setup.restore, ``IO.FS.writeFile),
  (`Regula.Cli.Setup.write, ``IO.FS.createDirAll),
  (`Regula.Cli.Setup.write, ``IO.FS.writeFile),
  -- The source of the compiler probe, in its temporary directory.
  (``Regula.Toolchain.probe, ``IO.FS.writeFile)])

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
