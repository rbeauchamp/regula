/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Domain
import RegulaSpecification.Proofs.Language

/-!
# The domain, on cases

`Configuration.check` decides `Configuration.InDomain` (`check_iff`), so the kernel can evaluate a configuration. The cases here are
those of the audit, with its neighbour, and those that a second model gave from the owner's account and Lake's document, without reading
the code or this statement (`confirmation.md` holds each difference and how it was settled). Each case is a statement about what the domain
says of that configuration, and what a run does with it is the business of `reason_excluded` and `domain_owed`.

`inDomain_respell` is the statement that the domain reads a directory only through what `dirShape` keeps: two configurations that differ at most in how each
`srcDir` is spelled are in the domain together, and `Cases.audit_respelling` is the audit's pair.
-/

namespace RegulaSpecification.Domain

open Lean (Name)
open Regula.Language
open RegulaSpecification.Language

namespace Configuration

/-- Whether a `globs` entry is a single module. -/
def isOne : Lake.Glob → Bool
  | .one _ => true
  | _ => false

theorem isOne_iff (g : Lake.Glob) : isOne g = true ↔ ∃ n, g = .one n := by
  cases g <;> simp [isOne]

/-- Whether a spelling is `Relative`. -/
def relativeCheck (s : String) : Bool :=
  s.front != '/' && (components s).all (·.front != '.')

theorem relativeCheck_iff (s : String) : relativeCheck s = true ↔ Relative s := by
  simp [relativeCheck, Relative]

variable (c : Configuration)

/-- `InDomain`, as a function the kernel can evaluate. -/
def check : Bool :=
  c.keys.all configKeyAdmitted && c.keys.contains `name && c.keys.all (·.getRoot != `require) && decide (c.nesting < 8) &&
    c.sourceDirs.all relativeCheck && c.libraries.all (·.globs.all isOne) && c.targetNames.all closedModuleName &&
    decide c.targetNames.Nodup && decide (c.executables.map (·.root)).Nodup && !c.claim.isEmpty &&
    c.claim.all (fun x => c.claim.all fun y => x.1 != y.1 || x.2 == y.2) &&
    c.claim.all (fun x => (c.resolve x.1).all (· == x.2)) && c.defaultTargets.all (c.targetNames.contains ·)

/-- The function decides the statement. -/
theorem check_iff : c.check = true ↔ c.InDomain := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    bne_iff_ne, Bool.or_eq_true, beq_iff_eq, Option.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hn⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hr⟩, h8⟩, h9⟩, h10⟩, h11⟩
    refine ⟨fun k hk => (configKeyAdmitted_iff k).mp (h1 k hk), hn, h2, h3, fun s hs => (relativeCheck_iff s).mp (h4 s hs),
      fun lib hl g hg => (isOne_iff g).mp (h5 lib hl g hg), fun n hn => (closedModuleName_iff n).mp (h6 n hn), h7, hr, h8, ?_, ?_, h11⟩
    · intro x hx y hy he
      rcases h9 x hx y hy with hne | heq
      · exact absurd he hne
      · exact heq
    · intro x hx rel hr
      exact (h10 x hx rel hr).symm ▸ rfl
  · intro h
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun k hk => (configKeyAdmitted_iff k).mpr (h.keys k hk), h.named⟩, h.noDependency⟩, h.shallow⟩,
      fun s hs => (relativeCheck_iff s).mpr (h.sourceDirs s hs)⟩, fun lib hl g hg => (isOne_iff g).mpr (h.globs lib hl g hg)⟩,
      fun n hn => (closedModuleName_iff n).mpr (h.targetNames n hn)⟩, h.distinctTargets⟩, h.distinctRoots⟩, h.claimsSomething⟩, ?_⟩, ?_⟩, h.defaultsDeclared⟩
    · intro x hx y hy
      by_cases he : x.1 = y.1
      · exact .inr (h.oneFile x hx y hy he)
      · exact .inl he
    · intro x hx rel hr
      exact (h.resolvesToClaim x hx rel hr).symm ▸ rfl

/-! ## Spelling -/

/-- What the domain reads of a directory's spelling. -/
def dirShape (s : String) : List String × Bool :=
  (components s, s.front == '/')

/-- What the domain reads of a library. -/
def libShape (lib : Library) : Name × (List String × Bool) × List Name × List Lake.Glob :=
  (lib.name, dirShape lib.srcDir, lib.roots, lib.globs)

/-- What the domain reads of an executable. -/
def exeShape (exe : Executable) : Name × (List String × Bool) × Name :=
  (exe.name, dirShape exe.srcDir, exe.root)

/-- Two configurations that differ at most in how each `srcDir` is spelled, pointwise, so that each directory may have its own new spelling. -/
structure Respelling (c c' : Configuration) : Prop where
  /-- The keys. -/
  keys : c.keys = c'.keys
  /-- The nesting. -/
  nesting : c.nesting = c'.nesting
  /-- The package's directory. -/
  srcDir : dirShape c.srcDir = dirShape c'.srcDir
  /-- Each library. -/
  libraries : c.libraries.map libShape = c'.libraries.map libShape
  /-- Each executable. -/
  executables : c.executables.map exeShape = c'.executables.map exeShape
  /-- The default targets. -/
  defaultTargets : c.defaultTargets = c'.defaultTargets

variable {c c' : Configuration}

private theorem components_of_shape {a b : String} (h : dirShape a = dirShape b) : components a = components b :=
  congrArg Prod.fst h

private theorem relative_of_shape {a b : String} (h : dirShape a = dirShape b) (ha : Relative a) : Relative b := by
  have h1 : components a = components b := congrArg Prod.fst h
  have h2 : (a.front == '/') = (b.front == '/') := congrArg Prod.snd h
  refine ⟨fun hb => ha.1 ?_, fun x hx => ha.2 x (h1 ▸ hx)⟩
  have : (b.front == '/') = true := beq_iff_eq.mpr hb
  rw [← h2] at this
  exact beq_iff_eq.mp this

/-- A find on one side and on the other, by a test of the shape, gives one shape. -/
private theorem find?_shape {α β : Type} (κ : α → β) (q : β → Bool) {l l' : List α} (h : l.map κ = l'.map κ) :
    (l.find? (q ∘ κ)).map κ = (l'.find? (q ∘ κ)).map κ := by
  have := congrArg (List.find? q) h
  rwa [List.find?_map, List.find?_map] at this

private theorem map_cases {α β : Type} {κ : α → β} {a b : Option α} (h : a.map κ = b.map κ) :
    (a = none ∧ b = none) ∨ ∃ x y, a = some x ∧ b = some y ∧ κ x = κ y := by
  cases a <;> cases b <;> simp_all

private theorem listed_of_shape {a b : Library} (h : libShape a = libShape b) : listed a = listed b := by
  have : a.globs = b.globs := congrArg (fun x => x.2.2.2) h
  simp [listed, this]

private theorem fileIn_of_shape (hc : Respelling c c') {a b : Library} (h : libShape a = libShape b) (m : Name) :
    c.fileIn a m = c'.fileIn b m := by
  have h1 : components a.srcDir = components b.srcDir := congrArg (fun x => x.2.1.1) h
  simp only [fileIn, h1, components_of_shape hc.srcDir]

private theorem exeFile_of_shape (hc : Respelling c c') {a b : Executable} (h : exeShape a = exeShape b) :
    c.exeFile a = c'.exeFile b := by
  have h1 : components a.srcDir = components b.srcDir := congrArg (fun x => x.2.1.1) h
  have h2 : a.root = b.root := congrArg (fun x => x.2.2) h
  simp only [exeFile, h1, h2, components_of_shape hc.srcDir]

theorem Respelling.modulesOf (hc : Respelling c c') (target : Name) : c.modulesOf target = c'.modulesOf target := by
  have h1 := find?_shape libShape (fun x => x.1 == target) hc.libraries
  have h2 := find?_shape exeShape (fun x => x.1 == target) hc.executables
  have e1 : ((fun x : Name × (List String × Bool) × List Name × List Lake.Glob => x.1 == target) ∘ libShape) = (·.name == target) := rfl
  have e2 : ((fun x : Name × (List String × Bool) × Name => x.1 == target) ∘ exeShape) = (·.name == target) := rfl
  rw [e1] at h1
  rw [e2] at h2
  unfold Configuration.modulesOf
  rcases map_cases h1 with ⟨ha, hb⟩ | ⟨x, y, ha, hb, hxy⟩
  · rw [ha, hb]
    rcases map_cases h2 with ⟨hx, hy⟩ | ⟨a, b, hx, hy, hab⟩
    · rw [hx, hy]
    · have h3 : a.root = b.root := congrArg (fun x => x.2.2) hab
      rw [hx, hy]
      simp only [h3, exeFile_of_shape hc hab]
  · rw [ha, hb]
    simp only [listed_of_shape hxy, fileIn_of_shape hc hxy]

theorem Respelling.claim (hc : Respelling c c') : c.claim = c'.claim := by
  show c.defaultTargets.flatMap c.modulesOf = c'.defaultTargets.flatMap c'.modulesOf
  rw [hc.defaultTargets, funext hc.modulesOf]

theorem Respelling.resolve (hc : Respelling c c') (m : Name) : c.resolve m = c'.resolve m := by
  have hrev : c.libraries.reverse.map libShape = c'.libraries.reverse.map libShape := by
    rw [List.map_reverse, List.map_reverse, hc.libraries]
  have h1 := find?_shape libShape (fun x => x.2.2.2.any (Lake.Glob.matches m) ||
    x.2.2.1.any fun root => root.isPrefixOf m && x.2.2.2.any (Lake.Glob.matches root)) hrev
  have e1 : ((fun x : Name × (List String × Bool) × List Name × List Lake.Glob => x.2.2.2.any (Lake.Glob.matches m) ||
      x.2.2.1.any fun root => root.isPrefixOf m && x.2.2.2.any (Lake.Glob.matches root)) ∘ libShape) = (buildable · m) := rfl
  rw [e1] at h1
  unfold Configuration.resolve
  rcases map_cases h1 with ⟨ha, hb⟩ | ⟨x, y, ha, hb, hxy⟩
  · rw [ha, hb]
    rfl
  · rw [ha, hb]
    simp only [Option.map_some, fileIn_of_shape hc hxy]

theorem Respelling.targetNames (hc : Respelling c c') : c.targetNames = c'.targetNames := by
  have h1 : c.libraries.map (·.name) = c'.libraries.map (·.name) := by
    have := congrArg (List.map Prod.fst) hc.libraries
    simpa [List.map_map, Function.comp_def, libShape] using this
  have h2 : c.executables.map (·.name) = c'.executables.map (·.name) := by
    have := congrArg (List.map Prod.fst) hc.executables
    simpa [List.map_map, Function.comp_def, exeShape] using this
  simp only [Configuration.targetNames, h1, h2]

/-- **The domain reads a directory only through one spelling.** Two configurations that differ at most in how each `srcDir` is spelled, each directory on its
own, are in the domain together. -/
theorem inDomain_respell (hc : Respelling c c') (h : c.InDomain) : c'.InDomain := by
  have hlib : ∀ lib' ∈ c'.libraries, ∃ lib ∈ c.libraries, libShape lib = libShape lib' := by
    intro lib' hl
    have : libShape lib' ∈ c.libraries.map libShape := hc.libraries ▸ List.mem_map_of_mem hl
    obtain ⟨lib, h1, h2⟩ := List.mem_map.mp this
    exact ⟨lib, h1, h2⟩
  have hexe : ∀ exe' ∈ c'.executables, ∃ exe ∈ c.executables, exeShape exe = exeShape exe' := by
    intro exe' hx
    have : exeShape exe' ∈ c.executables.map exeShape := hc.executables ▸ List.mem_map_of_mem hx
    obtain ⟨exe, h1, h2⟩ := List.mem_map.mp this
    exact ⟨exe, h1, h2⟩
  have hroots : c.executables.map (·.root) = c'.executables.map (·.root) := by
    have := congrArg (List.map fun x : Name × (List String × Bool) × Name => x.2.2) hc.executables
    simpa [List.map_map, Function.comp_def, exeShape] using this
  have hsrc : ∀ {s}, s ∈ c.sourceDirs → Relative s := fun hs => h.sourceDirs _ hs
  refine ⟨hc.keys ▸ h.keys, hc.keys ▸ h.named, hc.keys ▸ h.noDependency, hc.nesting ▸ h.shallow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [sourceDirs, List.mem_cons, List.mem_append, List.mem_map] at hs
    rcases hs with (rfl | ⟨lib', hl, rfl⟩) | ⟨exe', hx, rfl⟩
    · exact relative_of_shape hc.srcDir (hsrc (by simp [sourceDirs]))
    · obtain ⟨lib, h1, h2⟩ := hlib _ hl
      refine relative_of_shape (a := lib.srcDir) (congrArg (fun x => x.2.1) h2) (hsrc ?_)
      simp only [sourceDirs, List.mem_cons, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨lib, h1, rfl⟩)
    · obtain ⟨exe, h1, h2⟩ := hexe _ hx
      refine relative_of_shape (a := exe.srcDir) (congrArg (fun x => x.2.1) h2) (hsrc ?_)
      simp only [sourceDirs, List.mem_cons, List.mem_append, List.mem_map]
      exact .inr ⟨exe, h1, rfl⟩
  · intro lib' hl g hg
    obtain ⟨lib, h1, h2⟩ := hlib _ hl
    have : lib.globs = lib'.globs := congrArg (fun x => x.2.2.2) h2
    exact h.globs lib h1 g (this ▸ hg)
  · rw [← hc.targetNames]
    exact h.targetNames
  · rw [← hc.targetNames]
    exact h.distinctTargets
  · rw [← hroots]
    exact h.distinctRoots
  · rw [← hc.claim]
    exact h.claimsSomething
  · rw [← hc.claim]
    exact h.oneFile
  · rw [← hc.claim]
    intro x hx rel hr
    rw [← hc.resolve] at hr
    exact h.resolvesToClaim x hx rel hr
  · rw [← hc.targetNames, ← hc.defaultTargets]
    exact h.defaultsDeclared

end Configuration

/-- **A project reads a directory only through one spelling, too.** -/
theorem Project.inDomain_respell {p : Project} {c' : Configuration} (hc : Configuration.Respelling p.config c') (h : p.InDomain) :
    ({ p with config := c' } : Project).InDomain := by
  refine ⟨h.toolchain, h.noLeanConfig, h.plainConfig, Configuration.inDomain_respell hc h.config, ?_, ?_, h.oneSource, ?_, h.moduleNames,
    h.toolchainNames, h.noMathlib, h.language, h.oneText, h.oneRole, h.sourcePath, ?_⟩
  · simpa [← hc.claim] using h.claimRead
  · simpa [← hc.claim, ← hc.resolve] using h.sourceFile
  · simpa [← hc.claim, ← hc.resolve] using h.imports
  · simpa [← hc.claim] using h.bounded

/-! ## Cases -/

namespace Cases

open Configuration

/-- The keys these cases use. -/
private def keys : List Name :=
  [`name, `srcDir, `defaultTargets, `lean_lib.name, `lean_lib.srcDir, `lean_lib.roots, `lean_lib.globs, `lean_exe.name, `lean_exe.root,
    `lean_exe.srcDir]

/-- A library with the name `n`, its `srcDir` and the one root and glob `m`. -/
private def lib (n : Name) (s : String) (m : Name) : Library := ⟨n, s, [m], [.one m]⟩

/-- A configuration of these keys, with its package `srcDir`. -/
private def config (s : String) (libs : List Library) (exes : List Executable) (targets : List Name) : Configuration :=
  ⟨keys, 1, s, libs, exes, targets⟩

/-- The audit's project: two default libraries that hold one module, with `srcDir` spelled `.` and `./`. -/
def audit : Configuration := config "." [lib `A "." `Demo, lib `B "./" `Demo] [] [`A, `B]

/-- Its neighbour, with two `.`. -/
def auditNeighbour : Configuration := config "." [lib `A "." `Demo, lib `B "." `Demo] [] [`A, `B]

/-- The audit's project is in the domain. -/
theorem audit_in : audit.InDomain := (check_iff _).mp (by decide +kernel)

/-- And so is its neighbour. -/
theorem auditNeighbour_in : auditNeighbour.InDomain := (check_iff _).mp (by decide +kernel)

/-- The two claims are one. -/
theorem audit_claim : audit.claim = auditNeighbour.claim := by decide +kernel

/-- The audit's project and its neighbour are two spellings of one configuration. -/
theorem audit_respelling : Respelling auditNeighbour audit :=
  ⟨rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

/-- A configuration outside the domain, by evaluation. -/
private theorem outside {c : Configuration} (h : c.check = false) : ¬ c.InDomain :=
  fun hc => by rw [(check_iff c).mpr hc] at h; cases h

/-! Both readings put these in the domain. -/

theorem oneLibrary_in : (config "." [lib `Demo "." `Demo] [] [`Demo]).InDomain := (check_iff _).mp (by decide +kernel)
theorem oneExecutable_in : (config "." [] [⟨`demo, ".", `Main⟩] [`demo]).InDomain := (check_iff _).mp (by decide +kernel)
theorem composedDirs_in : (config "src" [lib `Demo "lib" `Demo] [] [`Demo]).InDomain := (check_iff _).mp (by decide +kernel)
theorem dotsAndSeparators_in : (config "./src//" [lib `Demo "./lib/./" `Demo] [] [`Demo]).InDomain := (check_iff _).mp (by decide +kernel)
theorem libraryAndExecutable_in : (config "." [lib `L "." `Main] [⟨`demo, "./", `Main⟩] [`L, `demo]).InDomain :=
  (check_iff _).mp (by decide +kernel)
theorem descendantGlob_in : (config "." [⟨`L, ".", [`a], [.one `a.b]⟩] [] [`L]).InDomain := (check_iff _).mp (by decide +kernel)

/-! Both readings put these outside it. -/

theorem parentDir_out : ¬ (config ".." [lib `Demo "." `Demo] [] [`Demo]).InDomain := outside (by decide +kernel)
theorem parentInLibrary_out : ¬ (config "." [lib `Demo "a/../b" `Demo] [] [`Demo]).InDomain := outside (by decide +kernel)
theorem absoluteDir_out : ¬ (config "." [lib `Demo "/abs" `Demo] [] [`Demo]).InDomain := outside (by decide +kernel)
theorem doubleSlashDir_out : ¬ (config "//abs" [lib `Demo "." `Demo] [] [`Demo]).InDomain := outside (by decide +kernel)
theorem hiddenDir_out : ¬ (config "." [lib `Demo ".lake" `Demo] [] [`Demo]).InDomain := outside (by decide +kernel)
theorem twoFiles_out : ¬ (config "." [lib `A "a" `Demo, lib `B "b" `Demo] [] [`A, `B]).InDomain := outside (by decide +kernel)
theorem libraryAndExecutableTwoFiles_out : ¬ (config "." [lib `L "a" `Main] [⟨`demo, "b", `Main⟩] [`L, `demo]).InDomain :=
  outside (by decide +kernel)
theorem wildcardGlob_out : ¬ (config "." [⟨`L, ".", [`Data], [.andSubmodules `Data]⟩] [] [`L]).InDomain := outside (by decide +kernel)
theorem noDefaultTarget_out : ¬ (config "." [lib `L "." `Demo] [] []).InDomain := outside (by decide +kernel)
theorem defaultNamesNothingAlone_out : ¬ (config "." [lib `L "." `Demo] [] [`Other]).InDomain := outside (by decide +kernel)
theorem defaultNamesNothing_out : ¬ (config "." [lib `L "." `Demo] [] [`L, `Other]).InDomain := outside (by decide +kernel)
theorem targetNameReused_out : ¬ (config "." [lib `same "." `Demo] [⟨`same, ".", `Main⟩] [`same]).InDomain := outside (by decide +kernel)
theorem twoExecutablesOneRoot_out : ¬ (config "." [] [⟨`a, ".", `Main⟩, ⟨`b, ".", `Main⟩] [`a]).InDomain := outside (by decide +kernel)
theorem targetNameOpen_out : ¬ (config "." [lib (.str .anonymous "a-b") "." `Demo] [] [.str .anonymous "a-b"]).InDomain :=
  outside (by decide +kernel)
theorem dependency_out : ¬ ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `require.name] }).InDomain := outside (by decide +kernel)
theorem pluginKey_out : ¬ ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `plugins] }).InDomain := outside (by decide +kernel)
theorem buildDirKey_out : ¬ ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `buildDir] }).InDomain := outside (by decide +kernel)
theorem unknownKey_out : ¬ ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `harmless] }).InDomain := outside (by decide +kernel)
theorem moreLeanArgs_out : ¬ ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `moreLeanArgs] }).InDomain := outside (by decide +kernel)

/-! The two readings differ on these. Each states what this domain says, and `confirmation.md` records why. -/

/-- The second reading excludes an empty `srcDir`. Here it is one spelling of `.`. -/
theorem emptyDir_in : (config "" [lib `Demo "" `Demo] [] [`Demo]).InDomain := (check_iff _).mp (by decide +kernel)
/-- The second reading excludes one file with two names. Here each name is read and judged, and the file holds one text. -/
theorem twoNames_in : (config "." [lib `A "x" `Foo, lib `B "." `x.Foo] [] [`A, `B]).InDomain := (check_iff _).mp (by decide +kernel)
/-- The second reading excludes a `globs` entry outside `roots`. Regula's own configuration has one, and Lake builds it. -/
theorem globOutsideRoots_in : (config "." [⟨`RegulaChecker, ".", [`RegulaChecker], [.one `Regula.Effect]⟩] [] [`RegulaChecker]).InDomain :=
  (check_iff _).mp (by decide +kernel)
/-- The second reading excludes a repeated default target. Here it claims one module at one file. -/
theorem repeatedDefault_in : (config "." [lib `L "." `Demo] [] [`L, `L]).InDomain := (check_iff _).mp (by decide +kernel)
/-- The second reading excludes metadata keys and `supportInterpreter`. Here each is in the closed set, since none selects a file or runs code. -/
theorem metadataKeys_in : ({ config "." [lib `L "." `Demo] [] [`L] with keys := [`name, `version, `description, `license, `lean_exe.supportInterpreter] }).InDomain :=
  (check_iff _).mp (by decide +kernel)
/-- An odd name for a directory is a name for a directory: the second reading excludes it. -/
theorem spacedDir_in : (config "a b" [lib `L "." `Demo] [] [`L]).InDomain := (check_iff _).mp (by decide +kernel)

end Cases

end RegulaSpecification.Domain
