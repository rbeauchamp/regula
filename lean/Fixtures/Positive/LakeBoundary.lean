import Lake.Util.IO

/-
Positive control of item 3 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): a
root that reaches a boundary of Lake, the toolchain's own build system. `Lake.removeDirAllIfExists`
is a `partial def` of `Lake.Util.IO`, which Lean loads from the pinned toolchain's library, so the
boundary is part of the toolchain's trusted base and passes a checked execution claim, as one of
`Init`, `Std` or `Lean` does. Before the fix, `Lake` was no toolchain root, the boundary was the
dependency's, and the checked claim failed with RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/).
-/

/-- Removes the directory `path` and everything below it, if it exists. -/
def fixtures_lake_remove (path : System.FilePath) : IO Unit :=
  Lake.removeDirAllIfExists path
