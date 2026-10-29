module
public import VersoManual
import all VersoManual

/-! # Verso's own parser of a render's options

Verso's parser of the command-line options of `manualMain`, `manualMain.opts`, is an auxiliary
definition of `manualMain`, private to the module `VersoManual`. This module imports `VersoManual`
with `import all`, which gives it that private definition, and exposes the parser itself as
`RegulaRender.versoOptions`, so `RegulaRender.refuse` reads the options with the parser that
`manualMain` runs. -/

namespace RegulaRender

open Verso.Genre.Manual

/-- The configuration that Verso's parser of `manualMain`'s options, `manualMain.opts`, gives on the
command-line options `args` from `config`, or the error that it throws on options that it refuses.

Assumes: Verso `304b8561` (the revision that `website/lake-manifest.json` pins),
`src/verso-manual/VersoManual.lean`: `manualMain.opts` is defined at 997-1039, and `manualMain`
renders with `opts config options` (1046). Lean 4.35.0 gives a private declaration of a module
to a module that imports it with `import all` (`src/Lean/ResolveName.lean:278-293`). -/
public def versoOptions (config : RenderConfig) (args : List String) : IO RenderConfig :=
  manualMain.opts config args

end RegulaRender
