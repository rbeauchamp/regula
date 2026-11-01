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

`inDomain_respell` is the statement that the domain reads a directory only through what `OneSpelling` keeps: replacing each `srcDir` by another
spelling of it changes nothing.
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
  c.keys.all configKeyAdmitted && c.keys.all (·.getRoot != `require) && decide (c.nesting < 8) &&
    c.sourceDirs.all relativeCheck && c.libraries.all (·.globs.all isOne) && c.targetNames.all closedModuleName &&
    decide c.targetNames.Nodup && !c.claim.isEmpty &&
    c.claim.all (fun x => c.claim.all fun y => x.1 != y.1 || x.2 == y.2) &&
    c.claim.all fun x => (c.resolve x.1).all (· == x.2)

/-- The function decides the statement. -/
theorem check_iff : c.check = true ↔ c.InDomain := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    bne_iff_ne, Bool.or_eq_true, beq_iff_eq, Option.all_eq_true, Option.mem_def]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
    refine ⟨fun k hk => (configKeyAdmitted_iff k).mp (h1 k hk), h2, h3, fun s hs => (relativeCheck_iff s).mp (h4 s hs),
      fun lib hl g hg => (isOne_iff g).mp (h5 lib hl g hg), fun n hn => (closedModuleName_iff n).mp (h6 n hn), h7, h8, ?_, ?_⟩
    · intro x hx y hy he
      rcases h9 x hx y hy with hne | heq
      · exact absurd he hne
      · exact heq
    · intro x hx rel hr
      exact (h10 x hx rel hr).symm ▸ rfl
  · intro h
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨fun k hk => (configKeyAdmitted_iff k).mpr (h.keys k hk), h.noDependency⟩, h.shallow⟩,
      fun s hs => (relativeCheck_iff s).mpr (h.sourceDirs s hs)⟩, fun lib hl g hg => (isOne_iff g).mpr (h.globs lib hl g hg)⟩,
      fun n hn => (closedModuleName_iff n).mpr (h.targetNames n hn)⟩, h.distinctTargets⟩, h.claimsSomething⟩, ?_⟩, ?_⟩
    · intro x hx y hy
      by_cases he : x.1 = y.1
      · exact .inr (h.oneFile x hx y hy he)
      · exact .inl he
    · intro x hx rel hr
      exact (h.resolvesToClaim x hx rel hr).symm ▸ rfl

/-! ## Spelling -/

/-- The same configuration, with each `srcDir` spelled by `f`. -/
def mapDirs (f : String → String) : Configuration :=
  { c with
    srcDir := f c.srcDir
    libraries := c.libraries.map fun lib => { lib with srcDir := f lib.srcDir }
    executables := c.executables.map fun exe => { exe with srcDir := f exe.srcDir } }

variable {c} {f : String → String}

private theorem find?_map_same {α : Type} (g : α → α) (p : α → Bool) (h : ∀ a, p (g a) = p a) (l : List α) :
    (l.map g).find? p = (l.find? p).map g := by
  rw [List.find?_map]
  have : (p ∘ g) = p := funext h
  rw [this]

theorem mapDirs_fileIn (hf : ∀ s, OneSpelling s (f s)) (lib : Library) (m : Name) :
    (c.mapDirs f).fileIn { lib with srcDir := f lib.srcDir } m = c.fileIn lib m := by
  simp only [fileIn, mapDirs, ← (hf _).1]

theorem mapDirs_exeFile (hf : ∀ s, OneSpelling s (f s)) (exe : Executable) :
    (c.mapDirs f).exeFile { exe with srcDir := f exe.srcDir } = c.exeFile exe := by
  simp only [exeFile, mapDirs, ← (hf _).1]

theorem mapDirs_modulesOf (hf : ∀ s, OneSpelling s (f s)) (target : Name) : (c.mapDirs f).modulesOf target = c.modulesOf target := by
  have h1 : (c.mapDirs f).libraries.find? (·.name == target) =
      (c.libraries.find? (·.name == target)).map fun lib => { lib with srcDir := f lib.srcDir } :=
    find?_map_same (fun lib : Library => { lib with srcDir := f lib.srcDir }) _ (fun _ => rfl) _
  have h2 : (c.mapDirs f).executables.find? (·.name == target) =
      (c.executables.find? (·.name == target)).map fun exe => { exe with srcDir := f exe.srcDir } :=
    find?_map_same (fun exe : Executable => { exe with srcDir := f exe.srcDir }) _ (fun _ => rfl) _
  unfold modulesOf
  rw [h1, h2]
  cases c.libraries.find? (·.name == target) with
  | some lib =>
    simp only [Option.map_some, listed, mapDirs_fileIn hf]
  | none =>
    cases c.executables.find? (·.name == target) with
    | some exe =>
      simp only [Option.map_none, Option.map_some, mapDirs_exeFile hf]
    | none => rfl

theorem mapDirs_claim (hf : ∀ s, OneSpelling s (f s)) : (c.mapDirs f).claim = c.claim := by
  show c.defaultTargets.flatMap (c.mapDirs f).modulesOf = c.defaultTargets.flatMap c.modulesOf
  rw [funext (mapDirs_modulesOf (c := c) hf)]

theorem mapDirs_resolve (hf : ∀ s, OneSpelling s (f s)) (m : Name) : (c.mapDirs f).resolve m = c.resolve m := by
  have h1 : (c.mapDirs f).libraries.reverse.find? (buildable · m) =
      (c.libraries.reverse.find? (buildable · m)).map fun lib => { lib with srcDir := f lib.srcDir } := by
    have : (c.mapDirs f).libraries.reverse = c.libraries.reverse.map fun lib => { lib with srcDir := f lib.srcDir } := by
      simp [mapDirs]
    rw [this]
    exact find?_map_same (fun lib : Library => { lib with srcDir := f lib.srcDir }) _ (fun _ => rfl) _
  unfold resolve
  rw [h1]
  cases c.libraries.reverse.find? (buildable · m) with
  | none => rfl
  | some lib => simp only [Option.map_some, mapDirs_fileIn hf]

/-- **The domain reads a directory only through one spelling.** Replacing each `srcDir` of a configuration by another spelling of it keeps the
configuration in the domain, whatever the spellings. -/
theorem inDomain_respell (hf : ∀ s, OneSpelling s (f s)) (h : c.InDomain) : (c.mapDirs f).InDomain := by
  have hclaim := mapDirs_claim (c := c) hf
  have hnames : (c.mapDirs f).targetNames = c.targetNames := by
    simp [targetNames, mapDirs, Function.comp_def]
  have hrelative : ∀ s, Relative s → Relative (f s) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hf s
    refine ⟨fun hx => hs.1 (h2.mpr hx), fun x hx => hs.2 x (h1 ▸ hx)⟩
  refine ⟨h.keys, h.noDependency, h.shallow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [sourceDirs, mapDirs, List.map_map, List.mem_cons, List.mem_append, List.mem_map, Function.comp_def] at hs
    rcases hs with (rfl | ⟨lib, hl, rfl⟩) | ⟨exe, hx, rfl⟩
    · exact hrelative _ (h.sourceDirs _ (by simp [sourceDirs]))
    · exact hrelative _ (h.sourceDirs _ (by simp only [sourceDirs, List.mem_cons, List.mem_append, List.mem_map]; exact .inl (.inr ⟨lib, hl, rfl⟩)))
    · exact hrelative _ (h.sourceDirs _ (by simp only [sourceDirs, List.mem_cons, List.mem_append, List.mem_map]; exact .inr ⟨exe, hx, rfl⟩))
  · intro lib hl g hg
    simp only [mapDirs, List.mem_map] at hl
    obtain ⟨lib₀, hl₀, rfl⟩ := hl
    exact h.globs lib₀ hl₀ g hg
  · rw [hnames]
    exact h.targetNames
  · rw [hnames]
    exact h.distinctTargets
  · rw [hclaim]
    exact h.claimsSomething
  · rw [hclaim]
    exact h.oneFile
  · rw [hclaim]
    intro x hx rel hr
    rw [mapDirs_resolve hf] at hr
    exact h.resolvesToClaim x hx rel hr

end Configuration

/-- **A project reads a directory only through one spelling, too.** -/
theorem Project.inDomain_respell {p : Project} {f : String → String} (hf : ∀ s, OneSpelling s (f s)) (h : p.InDomain) :
    ({ p with config := p.config.mapDirs f } : Project).InDomain := by
  have hc := Configuration.mapDirs_claim (c := p.config) hf
  have hr := Configuration.mapDirs_resolve (c := p.config) hf
  refine ⟨h.toolchain, h.noLeanConfig, h.plainConfig, Configuration.inDomain_respell hf h.config, ?_, ?_, h.oneSource, ?_, h.moduleNames,
    h.toolchainNames, h.noMathlib, h.language, h.oneText, h.oneRole, h.sourcePath, ?_⟩
  · simpa [hc] using h.claimRead
  · simpa [hc, hr] using h.sourceFile
  · simpa [hc, hr] using h.imports
  · simpa [hc] using h.bounded

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

/-- Both claim one module at one file. -/
theorem audit_claim : audit.claim = auditNeighbour.claim := by decide +kernel

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
theorem targetNameReused_out : ¬ (config "." [lib `same "." `Demo] [⟨`same, ".", `Main⟩] [`same]).InDomain := outside (by decide +kernel)
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
