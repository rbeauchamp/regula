import RegulaPolicy.Compiler
import Lean

/-! # Candidate observation boundaries

An explicit diagnostic invocation can exercise a prepared checker, but its written results
are unsupported observation envelopes. Ordinary candidate audit entrypoints refuse. Neither
the diagnostic switch nor decoding an observation constructs an accepted run. -/

namespace Regula.Checker.CompilerMode
open Lean RegulaPolicy

/-- The explicit diagnostic purpose inherited by qualification child processes. -/
def diagnostic : IO Bool := do
  return (← IO.getEnv "REGULA_COMPILER_QUALIFICATION") == some "1"

/-- The public entrypoint guard, after invalidating any requested output. -/
def requireAllowed : IO Unit := do
  unless Compiler.mayRun Compiler.candidate (← diagnostic) do
    throw <| IO.userError "unsupported compiler/checker combination: this revision is an \
      unqualified candidate; run its development qualification, then review a compatibility \
      revision before using ordinary audits"

/-- Transport of the proved publication classification. JSON encoding is a trusted adapter. -/
def envelope (value : Json) : Json :=
  match Compiler.publication Compiler.candidate value with
  | .audit value => value
  | .diagnostic value => Json.mkObj [
      ("purpose", .str "compiler-qualification"), ("status", .str "unsupported"),
      ("grantsSupport", .bool false), ("observation", value)]

/-- Decode candidate transport only inside an explicit candidate diagnostic invocation.
Ordinary readers refuse the envelope. The returned JSON is still observation data. -/
def readObservation (value : Json) : IO Json := do
  if (value.getObjValAs? String "purpose").toOption == some "compiler-qualification" then
    unless Compiler.candidate && (← diagnostic) do
      throw <| IO.userError "candidate diagnostic output is not supported audit evidence"
    unless (value.getObjValAs? String "status").toOption == some "unsupported" &&
        (value.getObjValAs? Bool "grantsSupport").toOption == some false do
      throw <| IO.userError "malformed compiler qualification envelope"
    IO.ofExcept (value.getObjVal? "observation")
  else return value

end Regula.Checker.CompilerMode
