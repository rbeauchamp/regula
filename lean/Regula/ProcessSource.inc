/-! The shared cold-start process implementation.

Lean's frontend elaborates this source inside the caller's namespace, so the bootstrap drivers
and the installed observer execute one source of the tool selection and override decision.
There is no package import to build before a cold driver can run. -/

open System

/-- The closed set of programs belonging to the selected Lean installation. -/
inductive Tool where
  /-- Lean's source compiler. -/
  | lean
  /-- Lean's package and build manager. -/
  | lake
  /-- Lean's serialized-module kernel checker. -/
  | leanchecker
  /-- Lean's native compiler driver. -/
  | leanc
  /-- The installation's C compiler. -/
  | clang
  /-- The installation's archiver. -/
  | llvmAr
  /-- The installation's SAT solver used by Lean's builtin bitvector tactic. -/
  | cadical
  deriving Repr, DecidableEq, BEq

/-- The installation's spelling of each tool, before the platform's executable extension. -/
def Tool.basename : Tool → String
  | .lean => "lean"
  | .lake => "lake"
  | .leanchecker => "leanchecker"
  | .leanc => "leanc"
  | .clang => "clang"
  | .llvmAr => "llvm-ar"
  | .cadical => "cadical"

/-- Selection belongs to the type: a tool of the installation, or a separately stated program.
The latter is a trusted selection, with its reason supplied at the call site. -/
inductive Program where
  /-- A tool selected only from the identity-checked installation. -/
  | toolchain (_tool : Tool)
  /-- A non-toolchain program, selected at this path for the stated reason. -/
  | stated (path : FilePath) (_reason : String)
  deriving Repr

instance : ToString Program where
  toString
    | .toolchain tool => tool.basename
    | .stated path _ => path.toString

/-- Read the named variable from this process's environment.
Assumes: Lean v4.34.1 `Init/System/IO.lean:951-955` returns the environment's current value;
the runtime's environment read and concurrent environment stability are trusted. -/
@[noinline] def readEnv (name : String) : BaseIO (Option String) := IO.getEnv name

/-- The process's working directory, through Lean's primitive.
Assumes: Lean v4.34.1 `Init/System/IO.lean:956-959` reports the working directory; the runtime and
concurrent directory stability are trusted. -/
@[noinline] def currentDir : IO FilePath := IO.currentDir

/-- The current executable's path, through Lean's primitive.
Assumes: Lean v4.34.1 `Init/System/IO.lean:952-955` reports the executing image's path; the runtime
and installation integrity are trusted. -/
@[noinline] def appPath : IO FilePath := IO.appPath

/-- Change this process's directory through Lean's primitive.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1383-1386` implements the requested change; the runtime,
filesystem and absence of competing directory changes inside this process are trusted. -/
@[noinline] def setCurrentDir (path : FilePath) : IO Unit := IO.Process.setCurrentDir path

/-- The runtime passes native strings without an embedded NUL. On Windows its command-line
builder quotes the program without escaping quotes inside it (`runtime/process.cpp:191-196`).
Lean v4.34.1 FilePath.isAbsolute accepts a drive-relative C:tool or a root-relative \tool
(`Init/System/FilePath.lean:109-110`). The Windows domain requires a separator after a drive
colon and rejects a single leading separator. Lean has no
stricter absolute-path predicate to reuse. Assumes: Microsoft's Win32 "Naming Files, Paths, and
Namespaces", "Fully Qualified vs. Relative Paths", gives that drive-relative interpretation:
https://learn.microsoft.com/en-us/windows/win32/fileio/naming-a-file -/
def nativeProgram (command : String) : Bool :=
  !command.contains "\x00" && (!System.Platform.isWindows ||
    (!command.contains "\"" &&
      (match command.toList with
        | first :: rest => !FilePath.pathSeparators.contains first ||
            rest.head?.any FilePath.pathSeparators.contains
        | [] => true) && match command.toList with
      | _ :: ':' :: separator :: _ => FilePath.pathSeparators.contains separator
      | _ :: ':' :: [] => false
      | _ => true))

/-- A path validated by Lean's absolute-path predicate and the native command-string domain. -/
abbrev AbsolutePath := {path : FilePath // path.isAbsolute = true ∧ nativeProgram path.toString = true}

/-- Admit an absolute path, without resolving a name against PATH. -/
def absolute (path : FilePath) : Except String AbsolutePath :=
  if h : path.isAbsolute = true ∧ nativeProgram path.toString = true then .ok ⟨path, h⟩
  else .error s!"process selection requires an absolute path: {path}"

/-- Successful path admission carries the predicate the caller uses. -/
theorem absolute_sound (path : FilePath) (admitted : AbsolutePath)
    (accepted : absolute path = .ok admitted) : admitted.val = path := by
  unfold absolute at accepted
  split at accepted <;> cases accepted <;> rfl

/-- The override variables Lake v4.34.1 reads for its compiler and archiver
(`Lake/Config/InstallPath.lean:289-316`). Each must be absent or absolute. -/
def overrideVariables : Array String := #["LEAN_CC", "CC", "LEAN_AR", "AR"]

/-- The effective value of a variable after POSIX Lean's left-to-right environment changes.
Assumes: Lean v4.34.1 `runtime/process.cpp:463-469` applies valid changes in this order;
this is not a model of Windows environment construction. -/
def effective (initial : Option String) (changes : Array (String × Option String))
    (name : String) : Option String :=
  changes.foldl (fun value (key, replacement) => if key = name then replacement else value) initial

/-- Native environment entries have a nonempty key without '=' or NUL and a value without NUL.
Assumes: Lean v4.34.1 `runtime/process.cpp:463-469` passes these strings to setenv/unsetenv. -/
def nativeEntry (entry : String × Option String) : Bool :=
  !entry.1.isEmpty && !entry.1.contains "=" && !entry.1.contains "\x00" &&
    entry.2.all (fun value => !value.contains "\x00")

/-- The domain on which the emitted environment has its stated native meaning. -/
def nativeChanges (changes : Array (String × Option String)) : Bool := changes.all nativeEntry

/-- Refuse malformed native environment entries without printing their values. -/
def requireChanges (changes : Array (String × Option String)) : IO Unit := do
  unless nativeChanges changes do throw <| IO.userError "invalid native process environment entry"

/-- Refuse every inherited or supplied compiler/archiver override that Lake could resolve
through PATH. Checking every occurrence avoids relying on duplicate-key merge order. Windows
keys are checked in uppercase because that OS's environment lookup is case insensitive.
This conservative decision also refuses an unsafe inherited value that a change would remove.
Assumes: Lean v4.34.1 `Lake/Config/InstallPath.lean:289-316` reads these variables; Windows
case-insensitive environment lookup is trusted. This is the one shared override decision. -/
def requireOverrides (changes : Array (String × Option String) := #[]) : IO Unit := do
  requireChanges changes
  for name in overrideVariables do
    if let some value ← readEnv name then
      discard <| IO.ofExcept (absolute value)
  for (key, value) in changes do
    let key := if System.Platform.isWindows then key.toUpper else key
    if overrideVariables.contains key then
      if let some value := value then discard <| IO.ofExcept (absolute value)

/-- Select the installation without starting a PATH-resolved Lean. A Lake environment supplies
an absolute LEAN_SYSROOT. Otherwise Lake's own Elan toolchain-directory construction resolves
ELAN_TOOLCHAIN under ELAN_HOME (or HOME/.elan), defaulting to the release that built this program.
Assumes: Lean v4.34.1 `Lake/Config/InstallPath.lean:32-58` describes the Elan installation layout;
the named installed toolchain and its contents are trusted. No PATH fallback or installation runs. -/
private def candidateRoot : IO AbsolutePath := do
  if let some root ← readEnv "LEAN_SYSROOT" then return ← IO.ofExcept (absolute root)
  let home ← match ← readEnv "ELAN_HOME" with
    | some home => pure (FilePath.mk home)
    | none =>
      let some home ← readEnv "HOME"
        | throw <| IO.userError "process selection needs LEAN_SYSROOT or an absolute Elan home"
      pure (FilePath.mk home / ".elan")
  let home ← IO.ofExcept (absolute home)
  let selector := (← readEnv "ELAN_TOOLCHAIN").getD s!"leanprover/lean4:v{Lean.versionString}"
  let elan : _root_.Lake.ElanInstall := { home := home.val, elan := home.val / "bin" / "elan" }
  let root := elan.toolchainDir selector
  IO.ofExcept (absolute root)

/-- An absolute installation whose Lean reported this program's compiler identity.
Only the identity observer constructs it. File contents and the compiler's self-report remain trusted. -/
structure Installation where
  private mk ::
  /-- The installation's absolute directory. -/
  root : AbsolutePath

/-- Cache hooks retain only identity-checked installations. The installed observer supplies an
IO.Ref; cold-source drivers use the default hooks without an initialized same-module reference.
The validation and selection rule is the same implementation in both contexts. -/
@[nospecialize] class Cache where
  /-- A previously checked installation, if this context retained one. -/
  find : IO (Option Installation)
  /-- Retain a token constructed by the identity check. -/
  save : Installation → IO Unit

/-- Cold-source interpretation needs no initializer; its launches recheck identity. -/
instance (priority := 0) : Cache where
  find := pure none
  save := fun _ => pure ()

/-- Resolve and check the compiler identity, preserving its absolute root.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1489-1502` executes the provided absolute program;
the runtime and the installation's files are trusted, including between this check and a start. -/
@[noinline, nospecialize] def identified [Cache] : IO Installation := do
  if let some installation ← Cache.find then return installation
  let root ← candidateRoot
  let root ← IO.ofExcept (absolute (← IO.FS.realPath root.val))
  let lean ← IO.ofExcept (absolute ((root.val / "bin" / "lean").addExtension FilePath.exeExtension))
  let result ← IO.Process.output {
    cmd := lean.val.toString, args := #["--stdin"],
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_SYSROOT", none)] }
    (some "#eval IO.println Lean.versionString\n#eval IO.println Lean.githash\n")
  unless result.exitCode == 0 &&
      result.stdout.replace "\r" "" == s!"{Lean.versionString}\n{Lean.githash}\n" do
    throw <| IO.userError s!"process selection: selected compiler at {lean.val} identity differs from this program"
  let found : Installation := ⟨root⟩
  Cache.save found
  return found

/-- A tool path carries both its absolute-path proof and its checked installation. -/
structure ResolvedTool (tool : Tool) where
  /-- The installation admitted by the compiler identity observation. -/
  installation : Installation
  /-- The absolute program path. -/
  path : AbsolutePath
  /-- The path belongs to this installation's closed tool selection. -/
  belongs : path.val =
    (installation.root.val / "bin" / tool.basename).addExtension FilePath.exeExtension

/-- Construct a closed tool path from the checked installation, with no workspace PATH lookup.
Assumes: the installation's other tools belong to it and its contents stay unchanged between
identity observation and execution; compiler self-report and installation integrity are trusted. -/
def resolvedTool [Cache] (tool : Tool) (known : Option Installation := none) : IO (ResolvedTool tool) := do
  let installation ← match known with
    | some installation => pure installation
    | none => identified
  let path := (installation.root.val / "bin" / tool.basename).addExtension FilePath.exeExtension
  let admitted ← match h : absolute path with
    | .ok admitted => pure (⟨admitted, absolute_sound path admitted h⟩ :
        {admitted : AbsolutePath // admitted.val = path})
    | .error error => throw <| IO.userError error
  unless ← path.pathExists do
    throw <| IO.userError s!"the selected installation has no {tool.basename} at {path}"
  return ⟨installation, admitted.val, admitted.property⟩

/-- The path projected from the same proof-bearing selection the launches consume. -/
def toolPath [Cache] (tool : Tool) (known : Option Installation := none) : IO FilePath :=
  return (← resolvedTool tool known).path.val

/-- The checked installation root, for Lean library lookup and in-process Lake. -/
def sysroot [Cache] : IO FilePath := return (← identified).root.val

/-- A resolved program retains the tool's checked installation, whenever its type selects a tool. -/
structure Resolution (program : Program) where
  /-- The actual command passed to the process runtime. -/
  command : String
  /-- The emitted command belongs to the native runtime's command-string domain. -/
  native : nativeProgram command = true
  /-- Toolchain commands are the paths constructed for the selected closed tool. -/
  tool : ∀ selected, program = .toolchain selected →
    ∃ resolved : ResolvedTool selected, command = resolved.path.val.toString

/-- Every toolchain resolution carries an absolute command path. -/
theorem Resolution.absolute {program : Program} (resolution : Resolution program)
    (tool : Tool) (selected : program = .toolchain tool) :
    (FilePath.mk resolution.command).isAbsolute = true := by
  obtain ⟨resolved, same⟩ := resolution.tool tool selected
  rw [same]
  exact resolved.path.property.1

/-- Resolve by the program's constructor. A stated path is a deliberate external selection;
its reason must be nonempty. Toolchain selections retain their proof-bearing installation path. -/
def resolution [Cache] (program : Program) (known : Option Installation := none) : IO (Resolution program) := do
  match h : program with
  | .toolchain tool =>
    let resolved ← resolvedTool tool known
    return ⟨resolved.path.val.toString, resolved.path.property.2, fun selected same => by
      have equal := h.symm.trans same
      cases equal
      exact ⟨resolved, rfl⟩⟩
  | .stated path reason =>
    if reason.trimAscii.isEmpty then throw <| IO.userError "a stated program needs its selection reason"
    if valid : nativeProgram path.toString = true then
      return ⟨path.toString, valid, fun _ same => by cases h.symm.trans same⟩
    else throw <| IO.userError "invalid native process command"

/-- The command spelling projected from the typed resolution. -/
def resolve [Cache] (program : Program) : IO String := return (← resolution program).command

/-- A prepared launch keeps its original arguments and streams, its one environment value,
and the proof-bearing resolution that supplies its runtime command. -/
structure Prepared (program : Program) (original : IO.Process.SpawnArgs) where
  /-- The resolution used by the emitted launch. -/
  selected : Resolution program
  /-- The launch's prepared environment changes, kept as one value. -/
  env : Array (String × Option String)

/-- The actual runtime command of a prepared launch. -/
def Prepared.cmd {program : Program} {original : IO.Process.SpawnArgs}
    (prepared : Prepared program original) : String := prepared.selected.command

/-- A prepared launch keeps the caller's argument array. -/
def Prepared.args {program : Program} {original : IO.Process.SpawnArgs}
    (_prepared : Prepared program original) : Array String := original.args

/-- A prepared launch keeps the caller's working directory. -/
def Prepared.cwd {program : Program} {original : IO.Process.SpawnArgs}
    (_prepared : Prepared program original) : Option FilePath := original.cwd

/-- Emit the same selected command and one prepared environment, preserving every other field. -/
abbrev Prepared.emit {program : Program} {original : IO.Process.SpawnArgs}
    (prepared : Prepared program original) : IO.Process.SpawnArgs :=
  { original with cmd := prepared.cmd, env := prepared.env }

/-- Every emitted toolchain start uses an absolute path, by its retained resolution. -/
theorem Prepared.absolute {original : IO.Process.SpawnArgs} (tool : Tool)
    (prepared : Prepared (.toolchain tool) original) :
    (FilePath.mk prepared.emit.cmd).isAbsolute = true :=
  prepared.selected.absolute tool rfl

/-- Every emitted command carries its native-domain admission. -/
theorem Prepared.native {program : Program} {original : IO.Process.SpawnArgs}
    (prepared : Prepared program original) : nativeProgram prepared.emit.cmd = true :=
  prepared.selected.native

/-- Prepare a launch. Toolchain launches refuse bare compiler/archiver overrides in their
inherited and supplied environments and receive the checked installation's Lean, Lake and sysroot paths.
The environment array stays one value for the later environment-recording work. -/
def prepare [Cache] (program : Program) (args : IO.Process.SpawnArgs) : IO (Prepared program args) := do
  requireChanges args.env
  let known ← match program with
    | .toolchain _ => some <$> identified
    | .stated .. => pure none
  let selected ← resolution program known
  let env ← match program with
    | .stated .. => pure args.env
    | .toolchain _ => do
      requireOverrides args.env
      let some installation := known | throw <| IO.userError "toolchain launch lost its checked installation"
      pure (args.env ++ #[("LEAN_SYSROOT", some installation.root.val.toString),
        ("LEAN", some (← toolPath .lean known).toString), ("LAKE", some (← toolPath .lake known).toString),
        ("LAKE_OVERRIDE_LEAN", none)])
  return ⟨selected, env⟩

/-- Start the typed program with the requested streams and one prepared environment.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1489-1502` and the process runtime implement spawn;
with an absolute path no PATH search selects a different file, and inheritEnv plus env has the
documented effect. The OS, signal delivery and child execution remain trusted. -/
@[noinline, nospecialize] def spawn [Cache] (program : Program) (args : IO.Process.SpawnArgs) : IO (IO.Process.Child args.toStdioConfig) := do
  let selected ← prepare program args
  IO.Process.spawn selected.emit

/-- Run the typed program to completion and capture its output, using Lean's own pipe management.
Assumes: Lean v4.34.1 `Init/System/IO.lean:1577-1608` joins the child and drains its streams. -/
@[noinline, nospecialize] def output [Cache] (program : Program) (args : IO.Process.SpawnArgs)
    (input : Option String := none) : IO IO.Process.Output := do
  IO.Process.output (← prepare program args).emit input
