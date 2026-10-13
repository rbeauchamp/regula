/-
Mutation, kept as the counterexample control of item 6 of issue #285
(https://github.com/rbeauchamp/regula/issues/285): an owned `unsafe def main`. Lean's C emitter
makes the compiled body named `main` the program's entry point, whatever its safety, so the
declaration is an executable root and its unsafe computation is a trusted boundary of its own
account, which fails a checked execution claim with RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/) beside the declaration's RG1006
(https://rbeauchamp.github.io/regula/dev/rules/RG1006/). Before the fix, executable roots were
the safe definitions alone, `main` was no root, its account was empty and only RG1006 reported it.
-/

/-- The program's entry point, declared `unsafe`. -/
unsafe def main : IO Unit :=
  IO.println "unsafe entry point"
