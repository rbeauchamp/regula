module

public import Init

/-! # The value of a variable after a child's environment changes

Lean describes the environment of a child process as the parent's, with the changes of the start's
`env` array applied left to right. `effective` states that value. The process observer's launch
theorems (`Regula.Process.Prepared.environment`) and the decisions of Git isolation
(`Regula.GitIsolation.processEnvironment_isolated`) are stated over this one definition. -/

@[expose] public section

namespace Regula.Process

/-- The value of `name` after the changes `changes`, applied left to right to `initial`: a change
of `name` replaces the value, `none` removes it.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1441-1450` describes a child's environment as the
parent's with `env` applied left to right, and `runtime/process.cpp:461-469` applies each entry
with `setenv` or `unsetenv` in that order between `fork` and `execvp`, when every native update
succeeds; the runtime ignores update failures, which valid strings do not exclude. This is not a
model of Windows environment construction. -/
def effective (initial : Option String) (changes : Array (String × Option String))
    (name : String) : Option String :=
  changes.foldl (fun value (key, replacement) => if key = name then replacement else value) initial

end Regula.Process
