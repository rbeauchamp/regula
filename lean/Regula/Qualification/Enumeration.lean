import Regula.Qualification.Support

/-! # Directory enumeration qualification

Two controls of the directory enumeration of `Regula.Filesystem.Construction` (issue 408). They
are operational observations of the actual constructor, not proofs about the operating system.

`check` runs the constructor, `Regula.Filesystem.copy`, in a child `qualify` process whose `PATH`
finds a stand-in listing program first. The stand-in is a copy of this executable named as
`Construction.locate` looks for GNU `ls`: it identifies as GNU coreutils 9.4 and lists the
directory the way the variable `standinVariable` selects. A listing that ends with the exit code 2
and the message of a failed read, as GNU `ls` reports one, a valid but shorter listing with the exit
code 2 and no error text, a listing whose last name has no NUL, a listing with error text but exit
code 0, a listing that names `..`, and a name that is not UTF-8 must each be refused before any
receipt and before any write at the destination. The `truncated` listing is refused only for its
exit code. A complete listing must give exactly the stand-in's names, which leave out one file of
the source, so the receipt is the stand-in's and not the real program's. The same source copied
in-process through the real program must give every file.

`failure` injects a real failed read of a directory. On a GitHub-hosted Linux runner, whose machine
is discarded after the job, it builds an ext4 image, maps it through device-mapper with one block
of a large directory replaced by the `error` target, and mounts it read-only. The real `ls` must
exit nonzero with an input/output error, `System.FilePath.readDir` of Lean v4.34.1 must return
fewer entries without an error, which is the defect of issue 408, and `Regula.Filesystem.copy`
must refuse with no destination. The same image mapped without the error must copy completely.
Anywhere else it refuses as unsupported, never as a pass. -/
namespace Regula.Qualification.Enumeration
open Lean System

/-- The variable whose value selects the stand-in's listing, in a copy of `qualify` named
`standinName`. -/
def standinVariable : String := "REGULA_LISTING_STANDIN"

/-- The name of the stand-in: the first program that `Construction.locate` tries on this
platform. -/
def standinName : String := if System.Platform.isOSX then "gls" else "ls"

/-- The names that the stand-in lists. -/
def listed : List String := ["alpha", "beta", "gamma"]

/-- A file of the control's source that the stand-in does not list. -/
def unlisted : String := "delta"

/-- Each name of `names`, ended by a NUL byte, as `ls --zero` writes it. -/
def zeroListing (names : List String) : ByteArray :=
  names.foldl (fun bytes name => bytes ++ name.toUTF8 ++ ByteArray.mk #[0]) ByteArray.empty

/-- The stand-in listing program. With `--version` it identifies as GNU coreutils 9.4. With the
options that `Construction.gnuEnumerator` gives that release, `--` and a directory, it lists that
directory as `mode` says: `complete` writes the names of `listed`, `failed` writes the first of
them and then fails as GNU `ls` does after a failed read, `truncated` writes the first of them and
exits 2 with no error text, so that only the exit code reports the failure, `unterminated` leaves
out the last NUL, `noisy` writes error text with exit code 0, `dotted` adds the name `..`, and
`binary` adds a name that is not UTF-8. Other arguments and modes exit 3. -/
def standin (mode : String) (args : List String) : IO UInt32 := do
  if args == ["--version"] then
    IO.println "ls (GNU coreutils) 9.4"
    return 0
  let ["-A", "-U", "--zero", "--", directory] := args
    | IO.eprintln s!"listing stand-in: unexpected arguments {args}"; return 3
  let stdout ← IO.getStdout
  match mode with
  | "complete" =>
    stdout.write (zeroListing listed)
    return 0
  | "failed" =>
    stdout.write (zeroListing (listed.take 1))
    IO.eprintln s!"ls: reading directory '{directory}': Input/output error"
    return 2
  | "truncated" =>
    stdout.write (zeroListing (listed.take 1))
    return 2
  | "unterminated" =>
    let listing := zeroListing listed
    stdout.write (listing.extract 0 (listing.size - 1))
    return 0
  | "noisy" =>
    stdout.write (zeroListing listed)
    IO.eprintln s!"ls: {directory}: a message after a complete listing"
    return 0
  | "dotted" =>
    stdout.write (zeroListing (listed ++ [".."]))
    return 0
  | "binary" =>
    stdout.write (zeroListing listed ++ ByteArray.mk #[0xff, 0])
    return 0
  | _ =>
    IO.eprintln s!"listing stand-in: unknown mode {mode}"
    return 3

/-- The child of `check`: copy `source` to `target` through `Regula.Filesystem.copy` and print the
receipt, the relative path of each item, as one JSON line. -/
def copyChild (source target : String) : IO Unit := do
  let items ← Regula.Filesystem.copy source target
  IO.println (toJson (items.map (·.relative))).compress

/-- The receipt of a copy of a directory whose files are `names`, in that order. -/
def receipt (names : List String) : List (List String) :=
  [] :: names.map ([·])

/-- Each stand-in mode that must be refused, with a text that the refusal must contain. -/
def refusals : List (String × String) :=
  [("failed", "failed with exit code 2: ls: reading directory"),
    ("truncated", "failed with exit code 2"),
    ("unterminated", "does not decode"),
    ("noisy", "failed with exit code 0: ls:"),
    ("dotted", "lists an invalid name: .."),
    ("binary", "is not UTF-8")]

/-- Run the constructor in a child process that lists through the stand-in in `mode`. -/
def copyThroughStandin (root bin source target : FilePath) (mode : String) :
    IO IO.Process.Output := do
  let path := (← Regula.Process.readEnv "PATH").getD ""
  Regula.Process.output
    (.stated (← Regula.Process.appPath) "The enumeration control selects this running executable") {
    cmd := "",
    args := #["--under-deadline", "enumeration-copy", source.toString, target.toString],
    cwd := some root,
    env := #[("PATH", some s!"{bin}:{path}"), (standinVariable, some mode),
      ("REGULA_QUALIFICATION_WRAPPER", none), ("REGULA_RECEIPT_TIMER", none)] }

/-- The stand-in control of the constructor (`qualify enumeration`). -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "enumeration" fun scratch => do
    let bin := scratch / "bin"
    IO.FS.createDir bin
    -- The stand-in is this executable, run by name through `PATH` in the child.
    Regula.Filesystem.copyFile (← Regula.Process.appPath) (bin / standinName) 493
    let source := scratch / "source"
    IO.FS.createDir source
    for name in listed ++ [unlisted] do
      IO.FS.writeFile (source / name) s!"{name}\n"
    for (mode, reason) in refusals do
      let target := scratch / s!"target-{mode}"
      let result ← copyThroughStandin root bin source target mode
      requireChecks [⟨s!"{mode}: the copy is refused", result.exitCode != 0⟩,
        ⟨s!"{mode}: the refusal is the listing's", result.stderr.contains reason⟩,
        ⟨s!"{mode}: no receipt is printed", result.stdout.isEmpty⟩,
        ⟨s!"{mode}: nothing is written at the destination",
          !(← Regula.Filesystem.isPresent target)⟩]
      IO.println s!"enumeration {mode}: refused before any receipt or write: PASS"
    let target := scratch / "target-complete"
    let result ← copyThroughStandin root bin source target "complete"
    let printed := (Json.parse result.stdout.trimAscii.toString).toOption.bind
      (fromJson? · |>.toOption)
    requireChecks [⟨"complete: the copy succeeds", result.exitCode == 0⟩,
      ⟨"complete: the receipt holds the stand-in's names", printed == some (receipt listed)⟩,
      ⟨"complete: the unlisted file is not copied",
        !(← Regula.Filesystem.isPresent (target / unlisted))⟩]
    for name in listed do
      requireChecks [⟨s!"complete: {name} is copied",
        (← IO.FS.readFile (target / name)) == s!"{name}\n"⟩]
    IO.println "enumeration complete: the stand-in's listing is the receipt: PASS"
    let items ← Regula.Filesystem.copy source (scratch / "target-real")
    let names := (listed ++ [unlisted]).map ([·])
    requireChecks [⟨"real listing: every file is copied",
      items.length == names.length + 1 && items.head?.map (·.relative) == some [] &&
        names.all fun name => (items.map (·.relative)).contains name⟩]
    IO.println "enumeration real listing: every file is copied: PASS"

/-! ## A failed read of a directory on a real filesystem -/

/-- The number of files of the directory whose read fails. -/
def entries : Nat := 400

/-- The block of that directory, counted from 0, that device-mapper replaces with an error. -/
def failedBlock : Nat := 10

/-- The size of the image, in 512-byte sectors (16 MiB). -/
def sectors : Nat := 32768

/-- The name of the file `index` of that directory: long, so the directory spans many blocks. -/
def entryFile (index : Nat) : String :=
  s!"entry-{index}-{String.ofList (List.replicate 40 'x')}"

/-- Whether `command args` runs and exits 0. -/
def runs (command : Regula.Process.Program) (args : Array String) : IO Bool := do
  match ← (Regula.Process.output command { cmd := "", args }).toBaseIO with
  | .ok result => return result.exitCode == 0
  | .error _ => return false

/-- Why `failure` cannot run here: it changes block devices and mounts, so it runs only on a
GitHub-hosted Linux runner, with passwordless `sudo` and each tool it runs. -/
def unsupported? : IO (Option String) := do
  unless System.Platform.isLinux do return some "it runs on Linux only"
  unless (← Regula.Process.readEnv "GITHUB_ACTIONS") == some "true" &&
      (← Regula.Process.readEnv "RUNNER_ENVIRONMENT") == some "github-hosted" do
    return some "it runs on a GitHub-hosted runner only, whose machine is discarded after the job"
  unless ← runs (.stated "sudo" "The hosted-Linux failure campaign requires sudo")
      #["-n", "true"] do return some "sudo needs a password"
  let checks : List (Regula.Process.Program × Array String) := [
      (.stated "mkfs.ext4" "The hosted-Linux failure campaign creates an ext4 image", #["-V"]),
      (.stated "debugfs" "The hosted-Linux failure campaign reads the image's block map", #["-V"]),
      (.toolchain .lean, #["--version"])]
  for (tool, args) in checks do
    unless ← runs tool args do return some s!"{tool} is not available"
  for (tool, args) in [("losetup", #["--version"]), ("dmsetup", #["version"]),
      ("mount", #["--version"])] do
    unless ← runs (.stated "sudo" "The hosted-Linux failure campaign selects privileged tools")
        (#["-n", tool] ++ args) do return some s!"{tool} is not available"
  return none

/-- Run `command args` with `input` on its standard input, refusing unless it exits 0; its
output. -/
def required (root : FilePath) (command : Regula.Process.Program) (args : Array String)
    (input : Option String := none) : IO String := do
  let result ← Regula.Process.output command { cmd := "", args, cwd := some root } input
  unless result.exitCode == 0 do
    throw <| IO.userError s!"{command} {" ".intercalate args.toList} failed with exit code \
      {result.exitCode}: {result.stderr}"
  return result.stdout

/-- `required` through `sudo -n`. -/
def privileged (root : FilePath) (args : Array String) (input : Option String := none) :
    IO String :=
  required root (.stated "sudo" "The hosted-Linux failure campaign selects privileged tools")
    (#["-n"] ++ args) input

/-- Map the loop device `loop` as `name` with `table`, mount it read-only at `mount` and run
`action`; then unmount it and remove the mapping, also when `action` fails. -/
def withMapping {α : Type} (root : FilePath) (name table : String) (mount : FilePath)
    (action : IO α) : IO α := do
  discard <| privileged root #["dmsetup", "create", name] table
  try
    discard <| privileged root #["mount", "-t", "ext4", "-o",
      "ro,nodev,nosuid,noexec,errors=continue", s!"/dev/mapper/{name}", mount.toString]
    try action
    finally discard <| privileged root #["umount", mount.toString]
  finally discard <| privileged root #["dmsetup", "remove", "--retry", name]

/-- The number of entries that Lean v4.34.1's `System.FilePath.readDir` returns for `path`, read
in a separate `lean` process from source text, so that no declaration of Regula refers to it. -/
def readDirCount (root path : FilePath) : IO (UInt32 × String) := do
  let result ← Regula.Process.output (.toolchain .lean) {
    cmd := "", args := #["--stdin", "--run", "Probe.lean", path.toString], cwd := some root }
    "def main (args : List String) : IO Unit := do\n  \
      IO.println (← System.FilePath.readDir args[0]!).size\n"
  return (result.exitCode, result.stdout.trimAscii.toString ++ result.stderr)

/-- The dm-error campaign (`qualify enumeration-failure`). -/
def failure : IO Unit := do
  if let some reason ← unsupported? then
    throw <| IO.userError s!"enumeration-failure: UNSUPPORTED, not run: {reason}"
  let root ← rootDirectory
  withScratch root "enumeration-failure" fun scratch => do
    let tree := scratch / "tree"
    IO.FS.createDirAll (tree / "dir")
    for index in [0:entries] do
      IO.FS.writeFile (tree / "dir" / entryFile index) ""
    let image := scratch / "image.ext4"
    -- The image file exists at its full size before mkfs.ext4 formats it.
    let mebibyte := ByteArray.mk (Array.replicate (1024 * 1024) 0)
    IO.FS.withFile image .writeNew fun handle => do
      for _ in [0:sectors / 2048] do handle.write mebibyte
    discard <| required root
      (.stated "mkfs.ext4" "The hosted-Linux failure campaign creates its disposable ext4 image")
      #["-q", "-F", "-b", "1024", "-O",
      "^dir_index,^has_journal", "-d", tree.toString, image.toString, s!"{sectors / 2}k"]
    let mapped ← required root
      (.stated "debugfs" "The hosted-Linux failure campaign reads its image's block map")
      #["-R", s!"bmap /dir {failedBlock}", image.toString]
    let some block := mapped.trimAscii.toString.toNat?
      | throw <| IO.userError s!"debugfs gave no block: {mapped}"
    requireChecks [⟨"the directory spans the failed block", 0 < block && 2 * block + 2 < sectors⟩]
    let sector := 2 * block
    let suffix := (← IO.getRandomBytes 8).foldl (fun text byte => text ++ s!"{byte.toNat}") ""
    let name := s!"regula-enumeration-{suffix}"
    let mount := scratch / "mount"
    IO.FS.createDir mount
    let loop := (← privileged root #["losetup", "--find", "--show", "--read-only",
      image.toString]).trimAscii.toString
    try
      let failing := s!"0 {sector} linear {loop} 0\n{sector} 2 error\n\
        {sector + 2} {sectors - sector - 2} linear {loop} {sector + 2}\n"
      withMapping root name failing mount do
        let listed ← Regula.Process.output
          (.stated "ls" "The hosted-Linux failure campaign observes GNU ls's failed read") {
          cmd := "", args := #["-A", "-U", "--zero", "--", (mount / "dir").toString ++ "/"],
          env := #[("LC_ALL", some "C")] }
        requireChecks [⟨"ls fails after the failed read", listed.exitCode != 0 &&
          listed.stderr.contains "Input/output error"⟩]
        IO.println "enumeration-failure ls: exits nonzero with an input/output error: PASS"
        let (code, count) ← readDirCount root (mount / "dir")
        let truncated := code == 0 && count.toNat?.any (· < entries)
        requireChecks [⟨s!"readDir returns fewer entries without an error ({code}: {count})",
          truncated⟩]
        IO.println s!"enumeration-failure readDir: {count} of {entries} entries and no error: PASS"
        let target := scratch / "copied"
        let copied ← (Regula.Filesystem.copy (mount / "dir") target).toBaseIO
        let outcome := match copied with
          | .ok items => s!"a receipt of {items.length} items"
          | .error error => toString error
        requireChecks [⟨s!"the copy refuses with the listing's failure: {outcome}",
            copied matches .error _ && outcome.contains "failed with exit code"⟩,
          ⟨"nothing is written at the destination", !(← Regula.Filesystem.isPresent target)⟩]
        IO.println "enumeration-failure copy: refused before any receipt or write: PASS"
      let whole := s!"0 {sectors} linear {loop} 0\n"
      withMapping root s!"{name}-whole" whole mount do
        let items ← Regula.Filesystem.copy (mount / "dir") (scratch / "whole")
        requireChecks [⟨"without the error every file is copied", items.length == entries + 1⟩]
        IO.println s!"enumeration-failure positive control: {entries} files copied: PASS"
    finally discard <| privileged root #["losetup", "--detach", loop]

end Regula.Qualification.Enumeration
