import Regula.Checker.Lake
import Regula.Contract
import Regula.Decision
import Lake.Load.Lean.Elab

/-! # The `lint` driver's claimed build

The plain-shape guard that decides whether the `lint` driver's claimed build needs the audit-build
marker (`auditMarkerNeeded`), and that build (`buildAuditTargets`). Only the driver
(`Regula.Checker.Lint`) and its qualification (`Regula.Checker.LintQualification`) import this
module, so `axiomGate` and the checker modules it imports do not build it. -/

namespace Regula.Checker.Lake

open Lean System
open Regula.Checker

/-- The module whose import loads Regula's local feedback: it registers the linter and the module
hook with `initialize`, and it is the only module of Regula that reads the marker of
`auditLeanOptions`. That it is Regula's only reader is checked by inspection. A project module that
reads the option from its own import-time options would read the marker too; the equal verdicts of
the plain shape assume that none does. -/
def linterModule : Name := `Regula.Linter

/-- The kind of a target that a package declares, or of the target that a `needs` entry names,
as the plain shape reads it. -/
inductive TargetKind where
  /-- A `lean_lib`. -/
  | leanLib
  /-- A `lean_exe`. -/
  | leanExe
  /-- An `input_file`, which Lake only reads and hashes. -/
  | inputFile
  /-- An `input_dir`, which Lake only reads and hashes. -/
  | inputDir
  /-- Any other declaration (a custom `target`, an `extern_lib`, an unknown kind), or a `needs`
  entry that names no target of its own package. -/
  | other
  deriving DecidableEq, Repr

/-- The name of `kind` in the reasons of `markerReason`. -/
def TargetKind.label : TargetKind → String
  | .leanLib => "lean_lib"
  | .leanExe => "lean_exe"
  | .inputFile => "input_file"
  | .inputDir => "input_dir"
  | .other => "other"

/-- The fields of a target's configuration that the plain shape lets differ from Lake's default:
the source directory, roots and globs of a library, the root, file name and interpreter support
of an executable, `needs` and Lean options of both, and the path and text mode of an input target.
Lake's build runs no code from any of them. -/
def TargetKind.fields : TargetKind → List Name
  | .leanLib => [`srcDir, `roots, `globs, `needs, `leanOptions]
  | .leanExe => [`srcDir, `root, `exeName, `needs, `supportInterpreter, `leanOptions]
  | .inputFile | .inputDir => [`path, `text]
  | .other => []

/-- The fields of a package's configuration that the plain shape lets differ from Lake's default:
the source directory, Lean options, the lint and test drivers, and the package's metadata. Lake's
build runs no code from any of them. -/
def packageFields : List Name :=
  [`srcDir, `leanOptions, `lintDriver, `lintDriverArgs, `testDriver, `testDriverArgs, `version,
    `versionTags, `description, `keywords, `homepage, `license, `licenseFiles, `readmeFile,
    `reservoir]

/-- What the plain shape reads of one target of a package. -/
structure TargetShape where
  /-- The target's name, which only `markerReason` reads. -/
  name : Name
  /-- The kind of the target. -/
  kind : TargetKind
  /-- Each field of the target's configuration that Regula does not show to have Lake's default
  value. -/
  unknown : Array Name
  /-- The kind of the target that each `needs` entry of a library or an executable names. -/
  needs : Array TargetKind

/-- A target of the plain shape: a `lean_lib`, `lean_exe`, `input_file` or `input_dir` that has
Lake's default value in each field outside `TargetKind.fields`, and whose `needs` entries each
name an `input_file` or an `input_dir` of its package. -/
def TargetShape.Plain (target : TargetShape) : Prop :=
  target.kind ≠ .other ∧ (∀ field ∈ target.unknown, field ∈ target.kind.fields) ∧
    ∀ kind ∈ target.needs, kind = .inputFile ∨ kind = .inputDir

/-- A declaration of a package's compiled configuration file, as the plain shape reads it. -/
inductive ConfigDeclaration where
  /-- One of Lake's configuration declarations, by name and kind (`configurationNames`): the
  package declaration and its configuration, the package-name helper `_package.name`, a `require`
  dependency, and each target's `ConfigDecl`, its declaration and its configuration, linked as
  Lake's commands generate them. -/
  | configuration
  /-- A theorem or an axiom whose statement is a `Lake.FamilyDef` or an equation between types, as
  Lake's commands generate. A compiler replacement (`csimp`) is an equation between functions, so
  it is not one. -/
  | typeFact
  /-- Any other declaration. -/
  | other
  deriving DecidableEq, Repr

/-- The environment extensions whose entries a compiled configuration file of the plain shape may
have: those that Lake's commands and the compilation of their declarations fill, as in Regula's own
configuration files at the pinned Lean. Any other extension, such as that of `csimp`,
`implemented_by`, `extern`, `init` or a documentation comment, is not plain. -/
def configExtensions : List String :=
  ["Lean.declRangeExt", "_private.Lean.Namespace.0.Lean.namespacesExt", "reducibilityCore",
    "Lean.Compiler.inlineAttrs", "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
    "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt", "Lean.Meta.instanceExtension",
    "Lean.IR.declMapExt", "_private.Lean.ExtraModUses.0.Lean.extraModUses",
    "Lean.Compiler.LCNF.baseExt", "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.impureSigExt",
    "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "Lean.deprecatedModuleExt",
    "Lean.Meta.simpExtension", "Lean.Linter.deprecatedAttr", "symbolFrequency", "sineQueNon",
    "Lake.packageAttr", "Lake.packageDepAttr", "Lake.leanLibAttr", "Lake.leanExeAttr",
    "Lake.inputFileAttr", "Lake.inputDirAttr", "Lake.targetAttr", "Lake.defaultTargetAttr"]

/-- The roots of the module names of Lean and Lake, the only modules that a configuration file of
the plain shape imports. -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- What the plain shape reads of one package of the workspace. -/
structure PackageShape where
  /-- The package's name, which only `markerReason` reads. -/
  name : Name
  /-- Each field of the package's configuration that Regula does not show to have Lake's default
  value. -/
  unknown : Array Name
  /-- Each target that the package declares. -/
  targets : Array TargetShape
  /-- The number of facets that the package's configuration file declares, new or in place of
  one of Lake's; `none` when Regula cannot read it. -/
  facets : Option Nat
  /-- Each declaration of the package's compiled configuration file, by name; none for a
  `lakefile.toml`. -/
  declarations : Array (Name × ConfigDeclaration)
  /-- Each environment extension with entries of the compiled configuration file itself; none for
  a `lakefile.toml`. -/
  extensions : Array String
  /-- The modules that the compiled configuration file imports; none for a `lakefile.toml`. -/
  imports : Array Name
  /-- The number of `attribute` commands, and of local or scoped attributes, in the configuration
  file's parsed syntax; zero for a `lakefile.toml`. -/
  attributes : Nat
  /-- The number of entries of the `inline` attributes in the compiled configuration file that
  differ from those Lake's commands give its configuration declarations; zero for a
  `lakefile.toml`. -/
  strayInlines : Nat

/-- A package of the plain shape: it has Lake's default value in each field outside
`packageFields`, each of its targets is of the plain shape, its configuration file declares no
facet, each declaration of its compiled configuration file is a `configuration` or a `typeFact`,
and each extension with entries of that file is one of `configExtensions`. The file imports only
modules of Lean and Lake (`toolchainRoots`), its syntax has no `attribute` command and no local or
scoped attribute, and its `inline` entries are exactly those of Lake's commands. In a workspace of
such packages, a build of `lean_lib` and `lean_exe` targets runs no custom build step: it compiles
modules and reads and hashes input files. -/
def PackageShape.Plain (shape : PackageShape) : Prop :=
  (∀ field ∈ shape.unknown, field ∈ packageFields) ∧ (∀ target ∈ shape.targets, target.Plain) ∧
    shape.facets = some 0 ∧ (∀ declaration ∈ shape.declarations, declaration.2 ≠ .other) ∧
    (∀ extension ∈ shape.extensions, extension ∈ configExtensions) ∧
    (∀ module ∈ shape.imports, module.getRoot ∈ toolchainRoots) ∧ shape.attributes = 0 ∧
    shape.strayInlines = 0

/-- Whether `kind` is one of the two input kinds. -/
def TargetKind.input : TargetKind → Bool
  | .inputFile | .inputDir => true
  | _ => false

/-- `TargetKind.input` holds exactly for the two input kinds. -/
theorem TargetKind.input_iff (kind : TargetKind) :
    kind.input = true ↔ kind = .inputFile ∨ kind = .inputDir := by
  cases kind <;> simp [input]

/-- The test of `TargetShape.Plain` (`TargetShape.plain_iff`). -/
def TargetShape.plain (target : TargetShape) : Bool :=
  target.kind != .other && target.unknown.all (target.kind.fields.contains ·) &&
    target.needs.all TargetKind.input

/-- `TargetShape.plain` decides `TargetShape.Plain`. -/
theorem TargetShape.plain_iff (target : TargetShape) : target.plain = true ↔ target.Plain := by
  simp only [plain, Plain, Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true',
    List.contains_iff_mem, TargetKind.input_iff, and_assoc]

/-- The test of `PackageShape.Plain` (`PackageShape.plain_iff`). -/
def PackageShape.plain (shape : PackageShape) : Bool :=
  shape.unknown.all (packageFields.contains ·) && shape.targets.all TargetShape.plain &&
    shape.facets == some 0 && shape.declarations.all (·.2 != .other) &&
    shape.extensions.all (configExtensions.contains ·) &&
    shape.imports.all (toolchainRoots.contains ·.getRoot) && shape.attributes == 0 &&
    shape.strayInlines == 0

/-- `PackageShape.plain` decides `PackageShape.Plain`. -/
theorem PackageShape.plain_iff (shape : PackageShape) : shape.plain = true ↔ shape.Plain := by
  simp only [plain, Plain, Bool.and_eq_true, Array.all_eq_true', List.contains_iff_mem,
    TargetShape.plain_iff, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc]

/-- The first condition of `TargetShape.plain` that `target` fails, as text: its kind, a field
outside `TargetKind.fields`, or a `needs` entry that names no input target of its package. `none`
exactly when `target` is plain (`TargetShape.failure?_eq_none`). -/
def TargetShape.failure? (target : TargetShape) : Option String :=
  (if target.kind == .other then
      some s!"target {target.name} is not a lean_lib, lean_exe, input_file or input_dir"
    else none).or <|
  ((target.unknown.find? (!target.kind.fields.contains ·)).map
    (s!"target {target.name} sets the field {·}")).or <|
  (target.needs.find? (!·.input)).map
    (s!"target {target.name} needs a target of kind {·.label}, not an input target of its package")

/-- `TargetShape.failure?` gives no reason exactly for a plain target. -/
theorem TargetShape.failure?_eq_none (target : TargetShape) :
    target.failure? = none ↔ target.plain = true := by
  simp only [failure?, plain, Option.or_eq_none_iff, Option.map_eq_none_iff, Array.find?_eq_none,
    Bool.and_eq_true, Array.all_eq_true', Bool.not_eq_true', Bool.not_eq_false, bne_iff_ne, ne_eq]
  split <;> simp_all

/-- The first condition of `PackageShape.plain` that `shape` fails, as text: a package field, a
target (`TargetShape.failure?`), the facets, a declaration, an extension, an import, an attribute
command or a stray `inline` entry. `none` exactly when `shape` is plain
(`PackageShape.failure?_eq_none`). -/
def PackageShape.failure? (shape : PackageShape) : Option String :=
  ((shape.unknown.find? (!packageFields.contains ·)).map (s!"the package field {·}")).or <|
  (shape.targets.findSome? TargetShape.failure?).or <|
  (if shape.facets == some 0 then none
    else some (shape.facets.elim "facet declarations that Regula cannot read"
      (s!"{·} facet declaration(s)"))).or <|
  ((shape.declarations.find? fun (declaration : Name × ConfigDeclaration) =>
      declaration.2 == ConfigDeclaration.other).map
    fun (declaration : Name × ConfigDeclaration) =>
      s!"the declaration {declaration.1}, not one of Lake's configuration declarations").or <|
  ((shape.extensions.find? (!configExtensions.contains ·)).map
    (s!"entries of the environment extension {·}")).or <|
  ((shape.imports.find? fun (module : Name) => !toolchainRoots.contains module.getRoot).map
    (s!"the import {·}")).or <|
  (if shape.attributes == 0 then none
    else some s!"{shape.attributes} attribute command(s) or local or scoped attribute(s)").or <|
  if shape.strayInlines == 0 then none
  else some s!"{shape.strayInlines} inline entr(ies) unlike those of Lake's commands"

/-- `PackageShape.failure?` gives no reason exactly for a plain package. -/
theorem PackageShape.failure?_eq_none (shape : PackageShape) :
    shape.failure? = none ↔ shape.plain = true := by
  simp only [failure?, plain, Option.or_eq_none_iff, Option.map_eq_none_iff, Array.find?_eq_none,
    Array.findSome?_eq_none_iff, TargetShape.failure?_eq_none, Bool.and_eq_true,
    Array.all_eq_true', Bool.not_eq_true', Bool.not_eq_false, beq_iff_eq, bne_iff_ne, ne_eq]
  simp only [ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not, and_assoc]

/-- A module of the root package as the driver reads it: the source file that each of the
package's libraries and executables gives the name, the source file of the module that Lake
resolves the name to, and the modules that Lake reports it imports transitively. -/
structure ModuleEntry where
  /-- The module's name. -/
  name : Name
  /-- The real path of the source file that each library and each executable of the root package
  gives the name. -/
  sources : Array String
  /-- The real path of the source file of the module that Lake resolves the name to, if that
  module is of the root package. -/
  resolved : Option String
  /-- The modules that Lake's `transImports` facet reports for the name. -/
  imports : Array Name

/-- A module that Lake resolves to the one source file that the root package gives it. -/
def ModuleEntry.Resolved (entry : ModuleEntry) : Prop :=
  ∀ source ∈ entry.sources, entry.resolved = some source

/-- The test of `ModuleEntry.Resolved` (`ModuleEntry.resolvedTest_iff`). -/
def ModuleEntry.resolvedTest (entry : ModuleEntry) : Bool :=
  entry.sources.all (entry.resolved == some ·)

/-- `ModuleEntry.resolvedTest` decides `ModuleEntry.Resolved`. -/
theorem ModuleEntry.resolvedTest_iff (entry : ModuleEntry) :
    entry.resolvedTest = true ↔ entry.Resolved := by
  simp only [resolvedTest, Resolved, Array.all_eq_true', beq_iff_eq]

/-- What the `lint` driver reads of the workspace before its claimed build: the shape of each
package, and each module that the root package owns. Lake applies the root package's Lean options
to the modules that package owns: the buildable modules of its libraries and the roots of its
executables. -/
structure MarkerInputs where
  /-- The shape of each package of the workspace (`packageShape`). -/
  packages : Array PackageShape
  /-- Each buildable module of the root package's libraries (`buildableModules`) and each root of
  its executables (`moduleEntries`). -/
  modules : Array ModuleEntry

/-- Whether the `lint` driver's claimed build passes `auditLeanOptions`: a package is not
`PackageShape.Plain`, or a module of the root package is not `ModuleEntry.Resolved` or imports
`linterModule`, directly or transitively (`auditMarkerNeeded_iff`). -/
@[regula_decision]
def auditMarkerNeeded (inputs : MarkerInputs) : Bool :=
  !(inputs.packages.all PackageShape.plain) ||
    inputs.modules.any fun entry => !entry.resolvedTest || entry.imports.contains linterModule

/-- `auditMarkerNeeded` asks for the marker exactly when a package is not of the plain shape, or
a module of the root package is not resolved to its one source or has the linter's module among
its imports. -/
theorem auditMarkerNeeded_iff (inputs : MarkerInputs) :
    auditMarkerNeeded inputs = true ↔
      ¬ (∀ shape ∈ inputs.packages, shape.Plain) ∨
        ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports := by
  have plain : inputs.packages.all PackageShape.plain = true ↔
      ∀ shape ∈ inputs.packages, shape.Plain := by
    simp only [Array.all_eq_true', PackageShape.plain_iff]
  have modules : (inputs.modules.any fun entry =>
        !entry.resolvedTest || entry.imports.contains linterModule) = true ↔
      ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports := by
    simp only [Array.any_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      ModuleEntry.resolvedTest_iff, Array.contains_iff_mem]
    constructor
    · rintro ⟨i, bound, holds⟩
      exact ⟨inputs.modules[i], Array.getElem_mem bound, holds⟩
    · rintro ⟨entry, entered, holds⟩
      obtain ⟨i, bound, rfl⟩ := Array.getElem_of_mem entered
      exact ⟨i, bound, holds⟩
  rw [auditMarkerNeeded, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, plain,
    modules]

/-- `auditMarkerNeeded` is a sound and complete decision of "a package is not of the plain shape,
or a module of the root package is not resolved to its one source or imports the linter's module"
(`auditMarkerNeeded_iff`): it asks for the marker for a package whose facets it cannot read, and
not for an empty workspace. The specification is a statement about fields, kinds and membership;
it names no test of the implementation. It does not establish that `linterModule` is the only
reader of the marker, nor that the inputs describe the workspace: the first is checked by
inspection, and the second rests on `markerInputs`, Lake's configuration, its compiled
configuration files and its `transImports` facet. -/
theorem checked_auditMarkerNeeded : Regula.ExecutableContract auditMarkerNeeded
    (Regula.Decides (· = true) fun inputs : MarkerInputs =>
      ¬ (∀ shape ∈ inputs.packages, shape.Plain) ∨
        ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports) :=
  ⟨Regula.Decides.of_iff auditMarkerNeeded_iff
    ⟨⟨#[⟨.anonymous, #[], #[], none, #[], #[], #[], 0, 0⟩], #[]⟩,
      (auditMarkerNeeded_iff _).mpr (.inl fun plain => by
        have facets := (plain ⟨.anonymous, #[], #[], none, #[], #[], #[], 0, 0⟩ (by simp)).2.2.1
        simp at facets)⟩
    ⟨⟨#[], #[]⟩, fun accepted => by
      rcases (auditMarkerNeeded_iff _).mp accepted with notPlain | ⟨_, member, _⟩
      · exact notPlain fun _ member => by simp at member
      · simp at member⟩⟩

/-- Why `entry` asks for the marker, as text: it is not resolved to its one source, or it imports
`linterModule`. -/
def ModuleEntry.failure? (entry : ModuleEntry) : Option String :=
  if !entry.resolvedTest then some s!"module {entry.name} does not resolve to its one source"
  else if entry.imports.contains linterModule then
    some s!"module {entry.name} imports {linterModule}"
  else none

/-- Why the `lint` driver's claimed build keeps the audit-build marker, as text: the first package
that is not plain with its first failed condition (`PackageShape.failure?`), or the first module
of the root package that asks for the marker (`ModuleEntry.failure?`). It gives a reason exactly
when `auditMarkerNeeded` asks for the marker (`markerReason_isSome`). -/
def markerReason (inputs : MarkerInputs) : Option String :=
  (inputs.packages.findSome? fun shape => shape.failure?.map (s!"package {shape.name}: {·}")).or <|
    inputs.modules.findSome? ModuleEntry.failure?

/-- `markerReason` gives a reason exactly when `auditMarkerNeeded` asks for the marker. -/
theorem markerReason_isSome (inputs : MarkerInputs) :
    (markerReason inputs).isSome = auditMarkerNeeded inputs := by
  have module (entry : ModuleEntry) : entry.failure? = none ↔
      (!entry.resolvedTest || entry.imports.contains linterModule) = false := by
    unfold ModuleEntry.failure?
    split
    · simp_all
    · split <;> simp_all
  rw [Bool.eq_iff_iff, Option.isSome_iff_ne_none, ne_eq, ← Bool.not_eq_false, Bool.not_eq_false]
  simp only [markerReason, auditMarkerNeeded, Option.or_eq_none_iff, Array.findSome?_eq_none_iff,
    Option.map_eq_none_iff, PackageShape.failure?_eq_none, module, Bool.or_eq_true,
    Bool.not_eq_true', Array.any_eq_true', Bool.eq_false_iff]
  rw [← Array.all_eq_true']
  cases inputs.packages.all PackageShape.plain <;> simp [Decidable.imp_iff_not_or]

/-- Lake reads an explicit `+module` with `String.toName` and splits facets at `:`.
Use that spelling, with `facet`, only when it retains the exact discovered root name, as for
`moduleArtifactsTarget?`. -/
def moduleFacetTarget? (root : Name) (facet : String) : Option String :=
  let spelling := root.toString (escape := false)
  if spelling.toName = root ∧ spelling.contains ':' = false then
    some s!"+{spelling}:{facet}"
  else none

/-- Each of `modules`, in that order, with the modules that it imports transitively in `ws`, as
Lake's `transImports` facet reports them through its query API (`Lake.querySpecs`, the form of
`lake query --json`): the modules of the workspace's packages, not those of the toolchain. The
facet reads module headers and builds nothing. `none` when a module has no query target, Lake
does not resolve one, Lake cannot read the imports, or a result is not an array of module
names. -/
def moduleImports (ws : _root_.Lake.Workspace) (modules : Array Name) :
    IO (Option (Array (Name × Array Name))) := do
  let some targets := modules.mapM (moduleFacetTarget? · "transImports") | return none
  let .ok specs ← (_root_.Lake.parseTargetSpecs ws targets.toList).toBaseIO | return none
  -- Lake's own report of a header it cannot read is the build's to show: the build that follows
  -- reads the same headers.
  let discarded ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let answers ← try
      ws.runBuild (_root_.Lake.querySpecs specs .json)
        { out := .stream (IO.FS.Stream.ofBuffer discarded), ansiMode := .noAnsi }
    catch _ => return none
  unless answers.size == modules.size do return none
  return (modules.zip answers).mapM fun (name, answer) => do
    let imports ← (Json.parse answer >>= fromJson? (α := Array Name)).toOption
    pure (name, imports)

/-- The kind of a declaration from its Lake kind name. -/
def declarationKind (kind : Name) : TargetKind :=
  if kind == _root_.Lake.LeanLib.configKind then .leanLib
  else if kind == _root_.Lake.LeanExe.configKind then .leanExe
  else if kind == _root_.Lake.InputFile.configKind then .inputFile
  else if kind == _root_.Lake.InputDir.configKind then .inputDir
  else .other

/-- The kind of the target that the `needs` entry `key` of a library or an executable of
`package` names: a target of `package` written `@/NAME` or `@PACKAGE/NAME`, with no facet. Every
other entry, such as a module, a facet or a target of another package, is `other`. -/
def needKind (package : _root_.Lake.Package) (key : _root_.Lake.PartialBuildKey) : TargetKind :=
  match key with
  | .packageTarget owner target =>
      if owner.isAnonymous || owner == package.baseName || owner == package.keyName then
        match package.targetDecls.find? (·.name == target) with
        | some declaration => declarationKind declaration.kind
        | none => .other
      else .other
  | _ => .other

/-- The canonical fields that Lake lists for a configuration type (`Lake.ConfigFields`) that
`checks` does not show to have Lake's default value: each field with no test in `checks`, and each
whose test is `false`. A field that Lake adds in another release has no test, so it is listed. -/
def unknownFields (fields : Array _root_.Lake.ConfigFieldInfo) (checks : List (Name × Bool)) :
    Array Name :=
  fields.filterMap fun field =>
    if field.canonical && checks.lookup field.name != some true then some field.name else none

/-- The tests against Lake's defaults of the fields of `LeanConfig`, which a package, a library and
an executable share. `leanOptions` has no test. -/
def leanConfigChecks (config : _root_.Lake.LeanConfig) : List (Name × Bool) :=
  [(`buildType, config.buildType == .release), (`moreLeanArgs, config.moreLeanArgs.isEmpty),
    (`weakLeanArgs, config.weakLeanArgs.isEmpty), (`moreLeancArgs, config.moreLeancArgs.isEmpty),
    (`moreServerOptions, config.moreServerOptions.isEmpty),
    (`weakLeancArgs, config.weakLeancArgs.isEmpty), (`moreLinkObjs, config.moreLinkObjs.isEmpty),
    (`moreLinkLibs, config.moreLinkLibs.isEmpty), (`moreLinkArgs, config.moreLinkArgs.isEmpty),
    (`weakLinkArgs, config.weakLinkArgs.isEmpty), (`backend, config.backend == .default),
    (`platformIndependent, config.platformIndependent.isNone),
    (`dynlibs, config.dynlibs.isEmpty), (`plugins, config.plugins.isEmpty),
    (`requiresModuleSystem, !config.requiresModuleSystem),
    (`allowNonModules, !config.allowNonModules)]

/-- The tests against Lake's defaults of the fields of a package's configuration. The fields of
`packageFields` have no test. -/
def packageChecks {key origin : Name} (config : _root_.Lake.PackageConfig key origin) :
    List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`bootstrap, !config.bootstrap), (`extraDepTargets, config.extraDepTargets.isEmpty),
      (`precompileModules, !config.precompileModules),
      (`moreGlobalServerArgs, config.moreGlobalServerArgs.isEmpty),
      (`buildDir, decide (config.buildDir = _root_.Lake.defaultBuildDir)),
      (`leanLibDir, decide (config.leanLibDir = _root_.Lake.defaultLeanLibDir)),
      (`nativeLibDir, decide (config.nativeLibDir = _root_.Lake.defaultNativeLibDir)),
      (`binDir, decide (config.binDir = _root_.Lake.defaultBinDir)),
      (`irDir, decide (config.irDir = _root_.Lake.defaultIrDir)),
      (`releaseRepo, config.releaseRepo.isNone), (`buildArchive, config.buildArchive.isNone),
      (`preferReleaseBuild, !config.preferReleaseBuild),
      (`enableArtifactCache?, config.enableArtifactCache?.isNone),
      (`restoreAllArtifacts?, config.restoreAllArtifacts?.isNone),
      (`libPrefixOnWindows, !config.libPrefixOnWindows),
      (`allowImportAll, !config.allowImportAll), (`builtinLint?, config.builtinLint?.isNone),
      (`fixedToolchain, !config.fixedToolchain),
      (`packagesDir, decide (config.packagesDir = _root_.Lake.defaultPackagesDir))]

/-- The tests against Lake's defaults of the fields of a library's configuration;
`nativeFacets` is the given reading of the compiled configuration (`leanConfigReading`). The
fields of `TargetKind.fields` have no test. -/
def libraryChecks {name : Name} (config : _root_.Lake.LeanLibConfig name) (nativeFacets : Bool) :
    List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`libName, config.libName.isEmpty), (`libPrefixOnWindows, !config.libPrefixOnWindows),
      (`extraDepTargets, config.extraDepTargets.isEmpty),
      (`precompileModules, !config.precompileModules),
      (`defaultFacets, config.defaultFacets == #[_root_.Lake.LeanLib.leanArtsFacet]),
      (`nativeFacets, nativeFacets), (`allowImportAll, !config.allowImportAll)]

/-- The tests against Lake's defaults of the fields of an executable's configuration;
`nativeFacets` is the given reading of the compiled configuration (`leanConfigReading`). The
fields of `TargetKind.fields` have no test. -/
def executableChecks {name : Name} (config : _root_.Lake.LeanExeConfig name)
    (nativeFacets : Bool) : List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`extraDepTargets, config.extraDepTargets.isEmpty), (`nativeFacets, nativeFacets)]

/-- Lake's default `nativeFacets` as a configuration file elaborates it at the pinned Lake,
`fun shouldExport => #[if shouldExport then Module.oExportFacet else Module.oFacet]`, with a
metavariable in place of each of its two proofs that the facet's output is a file path. -/
def defaultNativeFacetsTerm : Expr :=
  let facetType := mkApp (.const ``_root_.Lake.ModuleFacet []) (.const ``System.FilePath [])
  let one : Level := .succ .zero
  let facet (name : Name) (proof : Nat) : Expr :=
    mkApp3 (.const ``_root_.Lake.ModuleFacet.mk []) (.const ``System.FilePath []) (.const name [])
      (.mvar ⟨.num `proof proof⟩)
  let choice := mkAppN (.const ``ite [one]) #[facetType,
    mkApp3 (.const ``Eq [one]) (.const ``Bool []) (.bvar 0) (.const ``Bool.true []),
    mkApp2 (.const ``instDecidableEqBool []) (.bvar 0) (.const ``Bool.true []),
    facet ``_root_.Lake.Module.oExportFacet 1, facet ``_root_.Lake.Module.oFacet 2]
  .lam `shouldExport (.const ``Bool []) (mkApp2 (.const ``List.toArray [.zero]) facetType
    (mkApp3 (.const ``List.cons [.zero]) facetType choice
      (mkApp (.const ``List.nil [.zero]) facetType))) .default

/-- Lake's `Pattern.star` for paths, the default filter of an `input_dir`, as a configuration file
elaborates it at the pinned Lake. -/
def starPatternTerm : Expr :=
  mkApp2 (.const ``_root_.Lake.Pattern.star [.zero, .zero]) (.const ``System.FilePath [])
    (.const ``_root_.Lake.PathPatDescr [])

/-- Whether `term` is the whole term `expected`, except that each metavariable of `expected`
stands for a constant that `theorems` names: a proof, which the compiler erases. Binder names are
not compared; everything else is. -/
def sameUpToProofs (theorems : NameSet) : Expr → Expr → Bool
  | .mvar _, term => match term with
    | .const name _ => theorems.contains name
    | _ => false
  | .app function argument, term => match term with
    | .app function' argument' =>
        sameUpToProofs theorems function function' && sameUpToProofs theorems argument argument'
    | _ => false
  | .lam _ type body info, term => match term with
    | .lam _ type' body' info' =>
        info == info' && sameUpToProofs theorems type type' && sameUpToProofs theorems body body'
    | _ => false
  | expected, term => expected == term

/-- Whether every target that the compiled configuration `config` declares is Lake's DSL form whose
function fields are Lake's defaults. Each tagged target is a constant of type `ConfigDecl` whose
value is `KConfigDecl.toConfigDecl` of a constant of the file, whose value is
`DSL.mkConfigDecl` of a configuration constant of the file. That constant is a `LeanLibConfig.mk`
or `LeanExeConfig.mk` whose `nativeFacets` is the whole term `defaultNativeFacetsTerm`, its proofs
aside (`sameUpToProofs` with the theorems of the file), an `InputDirConfig.mk` whose filter is the
whole term `starPatternTerm`, or an `InputFileConfig`. A custom target, whose constant's value is
`DSL.mkTargetDecl`, is left to its kind, which `TargetShape.Plain` never admits. Any other term
gives `false`; the positions are those of Lake's constructors, and a term at another position is
not one of these terms. -/
def defaultFunctionFields (config : ModuleData) : Bool :=
  let value? (name : Name) := (config.constants.find? (·.name == name)).bind (·.value?)
  let theorems : NameSet := config.constants.foldl (init := {}) fun names constant =>
    match constant with
    | .thmInfo _ => names.insert constant.name
    | _ => names
  config.constants.all fun constant =>
    constant.type != .const ``_root_.Lake.ConfigDecl [] || Option.isSome do
      let tagged ← constant.value?
      guard (tagged.isAppOfArity ``_root_.Lake.KConfigDecl.toConfigDecl 2)
      let declaration ← value? (← tagged.appArg!.constName?)
      if declaration.isAppOfArity ``_root_.Lake.DSL.mkTargetDecl 7 then return ()
      guard (declaration.isAppOfArity ``_root_.Lake.DSL.mkConfigDecl 6)
      let name ← (declaration.getArg! 3).constName?
      let some configuration := config.constants.find? (·.name == name) | none
      let value ← configuration.value?
      match configuration.type.getAppFn.constName? with
      | some ``_root_.Lake.LeanLibConfig =>
          guard (value.isAppOfArity ``_root_.Lake.LeanLibConfig.mk 13 &&
            sameUpToProofs theorems defaultNativeFacetsTerm (value.getArg! 11))
      | some ``_root_.Lake.LeanExeConfig =>
          guard (value.isAppOfArity ``_root_.Lake.LeanExeConfig.mk 9 &&
            sameUpToProofs theorems defaultNativeFacetsTerm (value.getArg! 8))
      | some ``_root_.Lake.InputDirConfig =>
          guard (value.isAppOfArity ``_root_.Lake.InputDirConfig.mk 4 &&
            sameUpToProofs theorems starPatternTerm (value.getArg! 3))
      | some ``_root_.Lake.InputFileConfig => pure ()
      | _ => none

/-- Lake's configuration declarations in a compiled configuration file, by name, linked as Lake's
commands generate them (`configurationNames`). -/
structure ConfigurationNames where
  /-- Each configuration declaration. -/
  declarations : NameSet
  /-- Those to which Lake's commands give the `inline` attribute: the package declaration, the
  package-name helper and each target's declaration. -/
  inlined : NameSet

/-- The configuration declarations of the compiled configuration file `config`, each a definition
linked as Lake's commands generate it: a `ConfigDecl` whose value is `KConfigDecl.toConfigDecl` of
a definition of the file whose value is `DSL.mkConfigDecl` of a definition of the file, with those
two; a `ConfigDecl` whose value is `KConfigDecl.toConfigDecl` of a definition of the file whose
value is `DSL.mkTargetDecl`, a custom target, with that definition; a `PackageDecl` whose value is
`PackageDecl.mk` of a definition of the file, with that definition; a `Dependency` whose value is
a `Dependency.mk`; and the package-name helper `_package.name` of type `Name`. -/
def configurationNames (config : ModuleData) : ConfigurationNames := Id.run do
  let definition? (name : Name) : Option Expr :=
    match config.constants.find? (·.name == name) with
    | some (.defnInfo info) => some info.value
    | _ => none
  let mut names : ConfigurationNames := { declarations := {}, inlined := {} }
  for constant in config.constants do
    let .defnInfo info := constant | continue
    let value := info.value
    if constant.type == .const ``_root_.Lake.ConfigDecl [] &&
        value.isAppOfArity ``_root_.Lake.KConfigDecl.toConfigDecl 2 then
      let some declaration := value.appArg!.constName? | continue
      let some declared := definition? declaration | continue
      if declared.isAppOfArity ``_root_.Lake.DSL.mkTargetDecl 7 then
        names := {
          declarations := (names.declarations.insert constant.name).insert declaration
          inlined := names.inlined.insert declaration }
        continue
      unless declared.isAppOfArity ``_root_.Lake.DSL.mkConfigDecl 6 do continue
      let some configuration := (declared.getArg! 3).constName? | continue
      unless (definition? configuration).isSome do continue
      names := {
        declarations :=
          ((names.declarations.insert constant.name).insert declaration).insert configuration
        inlined := names.inlined.insert declaration }
    else if constant.type == .const ``_root_.Lake.PackageDecl [] &&
        value.isAppOfArity ``_root_.Lake.PackageDecl.mk 4 then
      let some configuration := (value.getArg! 3).constName? | continue
      unless (definition? configuration).isSome do continue
      names := {
        declarations := (names.declarations.insert constant.name).insert configuration
        inlined := names.inlined.insert constant.name }
    else if constant.type == .const ``_root_.Lake.Dependency [] &&
        value.isAppOf ``_root_.Lake.Dependency.mk then
      names := { names with declarations := names.declarations.insert constant.name }
    else if constant.name == `_package.name && constant.type == .const ``Lean.Name [] then
      names := {
        declarations := names.declarations.insert constant.name
        inlined := names.inlined.insert constant.name }
  return names

/-- The `ConfigDeclaration` of a declaration of a compiled configuration file whose configuration
declarations are `names`: one of them, a theorem or an axiom whose statement is a
`Lake.FamilyDef` or an equation in `Type`, or any other declaration. -/
def configDeclaration (names : NameSet) (constant : ConstantInfo) : ConfigDeclaration :=
  let typeFact := constant.type.isAppOf ``_root_.Lake.FamilyDef ||
    (constant.type.isAppOfArity ``Eq 3 && constant.type.getArg! 0 == .sort (.succ .zero))
  match constant with
  | .defnInfo _ => if names.contains constant.name then .configuration else .other
  | .thmInfo _ | .axiomInfo _ => if typeFact then .typeFact else .other
  | _ => .other

/-- The entries of the `inline` attributes (`Lean.Compiler.inlineAttrs`) of the compiled
configuration file whose module data is `config`, each declaration with its kind, read through
Lean's typed attribute API. As Lake's `importConfigFileCore` applies a configuration file's entries
of Lake's extensions, the file's entries of the attribute's extension, whose exported and added
entries have one type, are added to `imported`, the environment of the file's imports, and read
back as the extension's state, which starts empty in an imported environment. Importing the file
itself would load its imports again, and the process would keep that data until it exits. -/
def inlineEntries (imported : Environment) (config : ModuleData) :
    IO (Array (Name × Lean.Compiler.InlineAttributeKind)) := do
  let ext := Lean.Compiler.inlineAttrs.ext
  let some descriptor := (← persistentEnvExtensionsRef.get).find? (·.name == ext.name)
    | throw <| IO.userError s!"lake-config-inline: the extension {ext.name} is not registered"
  let entries := ((config.entries.find? (·.1 == ext.name)).map (·.2)).getD #[]
  let env := entries.foldl (descriptor.addEntry (asyncMode := .sync)) imported
  return (ext.getState env (asyncMode := .sync)).foldl (init := #[]) fun all name kind =>
    all.push (name, kind)

/-- The number of `inline` entries in `entries` that differ from those Lake's commands give: an
entry for a declaration outside `inlined` or of a kind other than `inline`, and a declaration of
`inlined` with no entry. -/
def strayInlines (entries : Array (Name × Lean.Compiler.InlineAttributeKind)) (inlined : NameSet) :
    Nat :=
  let stray := entries.filter fun (name, kind) =>
    !(inlined.contains name && match kind with | .inline => true | _ => false)
  let missing := (inlined.toList.filter fun name => !entries.any (·.1 == name)).length
  stray.size + missing

/-- `env` with the scoped entries of the namespaces `Lake` and `Lake.DSL` active, as after a
configuration file's `open Lake DSL`, so that Lake's scoped syntax parses. -/
def withLakeSyntax (env : Environment) : IO Environment := do
  let mut env := env
  for ext in ← scopedEnvExtensionsRef.get do
    env := ext.activateScoped (ext.activateScoped env `Lake) `Lake.DSL
  return env

/-- The number of `attribute` commands, and of local or scoped attributes, in the configuration
file at `path`, parsed with the parsers of `env`, the environment of the file's imports. Lake's scoped syntax is active
(`withLakeSyntax`). A parse error raises, so a file that needs other syntax keeps the marker. -/
def attributeCommands (env : Environment) (path : FilePath) : IO Nat := do
  let env ← withLakeSyntax env
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (_, state, messages) ← Parser.parseHeader inputCtx
  let mut state := state
  let mut messages := messages
  let mut count := 0
  for _ in [0:source.length + 1] do
    let (command, state', messages') :=
      Parser.parseCommand inputCtx { env, options := {} } state messages
    state := state'
    messages := messages'
    for node in command.topDown do
      if node.isOfKind ``Lean.Parser.Command.attribute ||
          (node.isOfKind ``Lean.Parser.Term.attrKind && !node[0].isNone) then
        count := count + 1
    if Parser.isTerminalCommand command then
      if messages.hasErrors then
        throw <| IO.userError s!"lake-config-parse: {path} does not parse"
      return count
  throw <| IO.userError s!"lake-config-parse: {path} has no end"

/-- What Regula reads of the compiled configuration file of a package. -/
structure ConfigReading where
  /-- The number of facets that the file declares; `none` when an import declares a target. -/
  facets : Option Nat
  /-- Whether its targets have Lake's default function fields (`defaultFunctionFields`). -/
  functions : Bool
  /-- The `ConfigDeclaration` of each declaration of the file, by name. -/
  declarations : Array (Name × ConfigDeclaration)
  /-- Each environment extension with entries of the file itself. -/
  extensions : Array String
  /-- The modules that the file imports. -/
  imports : Array Name
  /-- `attributeCommands` of the configuration file. -/
  attributes : Nat
  /-- `strayInlines` of the file. -/
  strayInlines : Nat

/-- What Regula reads of a `lakefile.toml`, which has no compiled configuration file: Lake's TOML
loader gives it no facet and no declaration. -/
def tomlReading : ConfigReading :=
  { facets := some 0, functions := false, declarations := #[], extensions := #[], imports := #[],
    attributes := 0, strayInlines := 0 }

/-- What Regula reads of the compiled configuration of a package whose configuration file is
`lakefile.lean` (`ConfigReading`). Lake keeps the compiled file at `.lake/config/<index>/` of the
workspace and imports its imports through `importModulesUsingCache`, which this reads again. The
facets are the entries of Lake's three facet attributes in the file and in its imports, which are
what Lake loaded. The declarations, the extensions and the `inline` entries are the file's own.
An attribute whose scope ends in the file leaves no entry, so its command is counted in the
file's syntax. -/
def leanConfigReading (ws : _root_.Lake.Workspace) (package : _root_.Lake.Package) :
    IO ConfigReading := do
  let some file := package.configFile.fileName | return { tomlReading with facets := none }
  let compiled := ws.root.dir / _root_.Lake.defaultLakeDir / "config" / toString package.wsIdx /
    (FilePath.mk file).withExtension "olean"
  let (config, _) ← readModuleData compiled
  let imported ← _root_.Lake.importModulesUsingCache config.imports {} 1024
  let own (extension : Name) : Nat :=
    ((config.entries.find? (·.1 == extension)).map (·.2.size)).getD 0
  let facets := [_root_.Lake.moduleFacetAttr, _root_.Lake.packageFacetAttr,
    _root_.Lake.libraryFacetAttr].foldl (init := 0) fun count facetAttribute =>
      count + (facetAttribute.getAllEntries imported).size + own facetAttribute.ext.name
  let names := configurationNames config
  return {
    facets := if (_root_.Lake.targetAttr.getAllEntries imported).isEmpty then some facets else none
    functions := defaultFunctionFields config
    declarations := config.constants.map fun constant =>
      (constant.name, configDeclaration names.declarations constant)
    extensions := config.entries.filterMap fun (extension, entries) =>
      if entries.isEmpty then none else some extension.toString
    imports := config.imports.map (·.module)
    attributes := ← attributeCommands imported package.configFile
    strayInlines := strayInlines (← inlineEntries imported config) names.inlined }

/-- What the plain shape reads of a target of `package` (`TargetShape`). For a `lakefile.lean`,
`functions` is the reading of its compiled configuration (`leanConfigReading`). For a
`lakefile.toml` (`toml`), Lake's TOML loader never sets `nativeFacets`, and it gives an `input_dir`
Lake's `Pattern.star`, which is named `star`, only for an omitted filter or `"*"`; it gives every
other filter `Pattern.ofDescr`, which has no name. -/
def targetShape (package : _root_.Lake.Package)
    (declaration : _root_.Lake.PConfigDecl package.keyName) (toml functions : Bool) :
    TargetShape :=
  let kind := declarationKind declaration.kind
  let nativeFacets := toml || functions
  if let some config := declaration.config? _root_.Lake.LeanLib.configKind then
    { name := declaration.name, kind, needs := config.needs.map (needKind package)
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.LeanLibConfig declaration.name)) (libraryChecks config nativeFacets) }
  else if let some config := declaration.config? _root_.Lake.LeanExe.configKind then
    { name := declaration.name, kind, needs := config.needs.map (needKind package)
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.LeanExeConfig declaration.name)) (executableChecks config nativeFacets) }
  else if let some config := declaration.config? _root_.Lake.InputDir.configKind then
    { name := declaration.name, kind, needs := #[]
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.InputDirConfig declaration.name))
        [(`filter, if toml then config.filter.name == `star else functions)] }
  else if kind == .inputFile then
    { name := declaration.name, kind, needs := #[]
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.InputFileConfig declaration.name)) [] }
  else { name := declaration.name, kind := .other, unknown := #[], needs := #[] }

/-- What the plain shape reads of `package`: Lake's configuration of the package and of each
target, and for `lakefile.lean` its compiled configuration (`leanConfigReading`). A `lakefile.toml`
declares no facet and has no compiled configuration file: Lake's TOML loader gives it no facet. -/
def packageShape (ws : _root_.Lake.Workspace) (package : _root_.Lake.Package) :
    IO PackageShape := do
  let toml := package.configFile.extension == some "toml"
  let reading ← if toml then pure tomlReading else leanConfigReading ws package
  return {
    name := package.baseName
    unknown := unknownFields (_root_.Lake.ConfigFields.fields
      (σ := _root_.Lake.PackageConfig package.keyName package.origName))
      (packageChecks package.config)
    targets := package.targetDecls.map (targetShape package · toml reading.functions)
    facets := reading.facets, declarations := reading.declarations
    extensions := reading.extensions, imports := reading.imports, attributes := reading.attributes
    strayInlines := reading.strayInlines }

/-- Each buildable module of the root package's libraries and each root of its executables, with
the real path of each source file that a library or an executable gives it, the source file of the
module that Lake resolves the name to (`Workspace.findTargetModule?`, which the `+NAME` targets of
`moduleImports` also use) when that module is of the root package, and its imports. `none` when
`moduleImports` reads none. -/
def moduleEntries (ws : _root_.Lake.Workspace) : IO (Option (Array ModuleEntry)) := do
  let root := ws.root
  let mut sources : Array (Name × FilePath) := #[]
  for library in root.leanLibs do
    for name in ← buildableModules library do
      sources := sources.push (name, Lean.modToFilePath library.srcDir name "lean")
  for exe in root.leanExes do
    sources := sources.push (exe.root.name, exe.root.leanFile)
  let mut names : Array Name := #[]
  let mut seen : NameSet := {}
  for (name, _) in sources do
    unless seen.contains name do
      names := names.push name
      seen := seen.insert name
  let some closure ← moduleImports ws names | return none
  let real (path : FilePath) : IO String := return (← IO.FS.realPath path).toString
  some <$> closure.mapM fun (name, imports) => do
    let mut paths : Array String := #[]
    for (other, source) in sources do
      if other == name then
        let path ← real source
        unless paths.contains path do paths := paths.push path
    let resolved ← match ws.findTargetModule? name with
      | some found =>
          if found.pkg.keyName == root.keyName then some <$> real found.leanFile else pure none
      | none => pure none
    return { name, sources := paths, resolved, imports }

/-- The `MarkerInputs` of `ws`. `none` when Lake cannot read the imports of a module of the root
package; the caller also keeps the marker when this raises. -/
def markerInputs (ws : _root_.Lake.Workspace) : IO (Option MarkerInputs) := do
  let packages ← ws.packages.mapM (packageShape ws)
  let some modules ← moduleEntries ws | return none
  return some { packages, modules }

/-- `buildTargets`, run in-process through Lake's build API because the `lake build` command line
sets no Lean options, with `auditLeanOptions` on the root package. Without `ordinary` that is every
build, as before the plain shape existed. With `ordinary`, the workspace owner's assertion that the
workspace's lakefiles are ordinary configuration (`lake lint -- --ordinary-lakefiles`), the marker
is omitted when `auditMarkerNeeded` decides that the workspace is of the plain shape and that each
module of the root package resolves to its one source and does not import `linterModule`; each
failure to read the workspace, by an exception or by an unknown, keeps it. It then prints one line
before the build, outside the build output: that the build omits the marker, or that it keeps it
with the reason, which is `markerReason` (a reason exactly when `auditMarkerNeeded` asks for the
marker, `markerReason_isSome`) or the failure to read the workspace. The plain shape is a
conservative guard under that assertion, not a guarantee against a lakefile written to defeat it.
For that shape the marked build and the unmarked one give the same verdict: a build of `lean_lib`
and `lean_exe` targets in it runs no custom build step, so it compiles only modules that the root
package owns, whose imports the decision read (or modules of other packages, which the root
package's options do not reach), and Regula's only reader of the marker is loaded in none of them.
That no project module reads the marker itself is assumed. Without the marker the ordinary build
output is reused as it is. The inherited search paths are ignored as in `buildTargets`; the build
monitor's text is the output, and a failed build exits 1. Lake's progress line for each job is also
shown as the build runs, as by `buildTargetsShowing`. -/
def buildAuditTargets (ordinary : Bool) (repo : FilePath) (targets : Array String) :
    IO ProcessResult := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) isLakeProgressLine
  let exitCode ← try
      Workspace.withRootWorkspace repo (scrubSearchPath := true) fun ws => do
        let specs ← match ← (_root_.Lake.parseTargetSpecs ws targets.toList).toBaseIO with
          | .ok specs => pure specs
          | .error error => throw <| IO.userError (toString error)
        let marked ← if !ordinary then pure true else do
          let reading : Except String MarkerInputs ← try
              pure <| match ← markerInputs ws with
                | some inputs => .ok inputs
                | none => .error "Lake did not report the imports of a module of the root package"
            catch error => pure (.error s!"the workspace could not be read: {error}")
          let (marked, reason) := match reading with
            | .ok inputs => (checked_auditMarkerNeeded.run inputs, markerReason inputs)
            | .error reason => (true, some reason)
          IO.println <| match reason with
            | some reason =>
                s!"regula lint: the claimed build keeps the audit-build marker: {reason}"
            | none => "regula lint: the claimed build omits the audit-build marker: the workspace \
                has the plain shape"
          (← IO.getStdout).flush
          pure marked
        let overrides : NameMap LeanOptions :=
          if marked then ({} : NameMap LeanOptions).insert ws.root.baseName auditLeanOptions else {}
        ws.runBuild (_root_.Lake.buildSpecs specs) {
          out := .stream out, ansiMode := .noAnsi, showSuccess := true,
          leanOptOverrides := overrides }
      pure (0 : UInt32)
    catch error =>
      out.putStrLn s!"error: {error}"
      pure 1
  let some stdout := String.fromUTF8? (← buffer.get).data
    | return { exitCode := 1, stdout := "", stderr := "error: build output is not UTF-8" }
  return { exitCode, stdout, stderr := "" }

end Regula.Checker.Lake
