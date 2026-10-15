/-! The construction process adapters used by the package and by the cold constructor interpreter.
Git configuration and copy policy live in `RegulaCore.CopyProgram`; this adapter only routes its
effects, including directory listings, through the process observer. Lean elaborates it inside
`Regula.CopyProcess`. -/

/-- Git is the deliberately stated repository mechanism, separate from Lean's toolchain. -/
def gitProgram : Regula.Process.Program := .stated "git" "Git is the stated repository mechanism"

/-- Supply the enumerator's explicitly stated external listing program through the shared
observer. GNU version admission remains in `Construction.locate`, not a second selection policy.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1002-1003,1544-1557` reads binary stdout, drains stderr
and waits for the child; the OS, listing program and stream fidelity remain trusted. -/
instance listingProcesses : Regula.Filesystem.Construction.ListingProcesses where
  output program options := do
    let selected := Regula.Process.Program.stated program
      "The directory enumerator explicitly selects this external GNU listing program"
    let child ← Regula.Process.spawn selected
      {options with stdin := .null, stdout := .piped, stderr := .piped}
    let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let bytes ← IO.ofExcept stdout.get
    return (exitCode, bytes, stderr)

/-- Supply the copy adapter's text and binary Git effects through the same typed selection.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1002-1003,1544-1557` reads binary stdout, drains stderr
and waits for the child; process execution and stream fidelity remain trusted. -/
instance gitProcesses : Regula.Filesystem.Construction.GitProcesses where
  output options := Regula.Process.output gitProgram options
  binaryOutput options := do
    let child ← Regula.Process.spawn gitProgram
      {options with stdin := .null, stdout := .piped, stderr := .piped}
    let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let bytes ← IO.ofExcept stdout.get
    return (exitCode, bytes, stderr)
