module

public import Lake.Load.Config
public import Lake.Config.Workspace
public import Lake.Util.MainM
public import Lake.Util.Cli
public import Lake.Util.IO
public import Lake.CLI.Main
public meta import Lean.Elab.Frontend
public meta import Lake.CLI.Main
meta import all Lake.CLI.Main
import all Lake.CLI.Main

/-! # The actual build's Lake configuration

Expose only the pinned Lake parser needed to recover a workspace's actual invocation.
The cold website configuration includes the same implementation before Regula is built.
-/

public section

namespace Regula.LakeBuildConfig
run_cmd do
  let input := Lean.Parser.mkInputContext (include_str "LakeBuildConfig.inc")
    "Regula/LakeBuildConfig.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
end Regula.LakeBuildConfig
