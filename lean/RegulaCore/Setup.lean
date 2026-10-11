import RegulaPolicy.Community
import RegulaPolicy.Compiler

/-! # Project setup that `regula init` writes and `regula doctor` checks

A project adopts Regula with four pieces of setup beside the `require`: the lint driver, the
options every claimed target is built with (standard §7.1 and §6.7, checked by RG2006), a
foundation manifest (RG2002), and guidance for coding agents. This module is the decision both
commands execute over what they observe of a project.

## Main declarations

- `Observation`: the facts `init` and `doctor` read, from Lake's loaded package and the files.
- `Issue`, `issues`, `Issue.fixable`: what is missing or wrong, and whether `init` writes it.
- `Edit`, `plan`, `apply`, `run`: the edits `init` derives from an observation, each writing only
  what is missing, and their effect on the observation.
- `plan_idempotent`: after `init` applies its plan, the plan of the result is empty, so a second
  run writes nothing.
- `Coverage`, `Coverage.globbing`, `globEdits`, `coverage_run`, `unglobbed_run`, `uncovered_run`:
  which modules each library leaves out, and which of them a claimed module imports, is one
  function of the root package's facts. `init` gives the libraries of `Coverage.globbing`, each
  setting no `globs`, the glob `Lakefile.globsSetting`, the one `doctor` asks for. The glob edit
  changes the facts (`Coverage.glob`), and after the plan they are the facts with those globs
  written (`coverage_run`), in which no library needs one (`unglobbed_run`) and what libraries
  leave out otherwise is unchanged (`uncovered_run`). A library with `globs` of its own keeps
  them, and its left-out modules stay an issue `init` does not fix. The findings read the imports
  of `Coverage.reads` alone (`coverage_congr`).
- `Settled`, `plan_eq_nil_iff_settled`, `issues_unfixable_iff_settled`, `plan_eq_nil_iff`: the plan
  is empty exactly when no fixable issue remains.
- `issues_run`: applying the plan removes exactly the fixable issues and adds none.
- `Pin`, `toolchainIssues`, `toolchainIssues_eq_nil_iff`: `doctor` reports no toolchain issue
  exactly when the project's `lean-toolchain` resolves to a compiler whose reported version and
  commit `RegulaPolicy.Compiler.Supports`, under any selector; a pin that resolves
  to no installed compiler is an issue.
- `Observation.starter`, `plan_manifest_mem`: the starter manifest is planned only when the package
  has a `lean_lib` for it to claim; a package with none has an issue `init` does not fix.
- `Target`, `Observation.targets`, `Observation.allClaimed`: the option check covers exactly the
  claimed targets, as RG2006 does.
- `Target.argues`, `Observation.without`: a `-D` candidate among a target's extra `lean` arguments
  sets an option, read as RG2006 reads them (`RegulaPolicy.Community.argumentSettings`, a superset
  of the `-D` settings `lean` reads under the command-line assumption stated there); a target
  builds without a required option when neither `leanOptions` nor such a candidate gives it one.
- `Observation.lacks`, `missing`, `targetMissing`, `optionEdits`: the options `init` adds. It adds
  a required option to the package when every root target is claimed, some claimed target builds
  without it and no claimed target's `-D` sets it; otherwise it adds the option to each claimed
  target that builds without it, so no option reaches a target the manifest excludes
  (`run_options_unclaimed`).
- `added_unargued`: no option the plan adds reaches a target whose `-D` also sets it, so the
  plan never creates a second setting beside a `-D`; `argued` lists the required options a
  claimed target sets only with a `-D`, which `doctor` reports once and `init` leaves to the user,
  and `arguedBy_run` states that the plan leaves `Observation.arguedBy`, those of each claimed
  target, unchanged.
- `run_plan_targets`, `run_sets`, `resolved_run`: after the plan, a claimed target that built
  without a required option builds with its required value (`RegulaPolicy.Community.sets`, which
  meets RG2006's requirement on that option by `meets_of_sets`), and every claimed target has a
  value for every required option or a `-D` of its own sets it.
- `run_options_prefix`, `withAdded_prefix`: the plan never changes or removes an option the
  package or a claimed target already sets, nor a target's extra `lean` arguments.
- `Issue.message`, `Issue.fix`, `unimportedNote`, `Edit.summary`: the text `doctor` and `init`
  print; a note is not an issue and does not fail `doctor`. A finding about modules a library
  leaves out states their count and names at most `shownModules` of them, wrapped
  (`moduleLines`, by definition `moduleSummary`'s names grouped by `wrapFrom`):
  `moduleSummary_complete` shows those names are a prefix of the modules and the count exactly the
  rest, and `wrapFrom_flatten` that grouping keeps each name, in order.

## Boundaries

The observation is supplied by the operational `regula` command: Lake's loaded root package
(its `lintDriver`, package-level `leanOptions`, and the own `leanOptions` and resolved extra
`lean` arguments of each root target the manifest does not exclude), whether the workspace
contains Mathlib, whether `foundation_manifest.json` and the agent guidance exist and which
`AGENTS.md` holds or receives the section, whether the root package has a `lean_lib` for a starter
manifest to claim, whether each skill file at the repository root equals the installed skill, the
version and commit reported by the compiler of the toolchain `elan toolchain list` names for the
project's `lean-toolchain` (a trusted listing and self-report,
independent of the compiler running `regula`), and the
modules below a library root that no library includes, split by whether a claimed module
imports them as Lean's import-header parser reads the package's sources (not a build), and the
imported ones by whether the library sets `globs` of its own. The command supplies these as the
facts of `Coverage` (each library's roots, modules, the modules below its roots and whether it
sets `globs`, the executable roots, and each source module's imports within the package); the
decision over them is defined here, so the edited facts are observed by the same function. The
command writes each edit into the lakefile, the
manifest and the guidance files, then observes the project again and refuses unless the new plan
is empty and each claimed target of both observations, matched by kind and name, has the same
`Observation.arguedBy` (`arguedBy_run`); that the file edits realize `apply` is that runtime
check, not a theorem. RG2006 itself is decided per claimed target over Lake's resolved options by
`RegulaPolicy.Community.failures`, reading the same `-D` candidates as `Target.argues`; `init`
writes an option into the package's configuration only when every root target is claimed and no
claimed target's `-D` candidate sets it, into claimed targets' own configurations otherwise, never
into a configuration that reaches a target whose `-D` candidate sets it, and never changes a value
the package or a target already gives. That `allClaimed` holds only when `targets` is every root
target is how the command builds the observation, not a field of this model. Which of Lean's
inputs wins when `leanOptions` and a `-D` both set an option is not modelled: the plan avoids the
situation. -/

namespace Regula.Setup

open Lean (Name)
open RegulaPolicy.Community (OptionValue required baseline mathlibBaseline valuesOf sets optionOf
  argumentSettings)

/-- The `lintDriver` value that makes `lake lint` run Regula. -/
def lintDriver : String := "regula/lint"

/-- Where `init` writes agent guidance when the project has none. -/
inductive Guidance where
  /-- A short section in `AGENTS.md` that tells the agent to run `lake exe regula agent-guide`;
  it names no version, so it never goes stale. -/
  | agentsMd
  /-- The installed briefing as an Agent Skills `SKILL.md` at `Observation.skillFile`, which
  `init` rewrites whenever it differs from the installed Regula's. -/
  | skill
  deriving DecidableEq, Repr

/-- The skill file `init --skill` writes, relative to the repository root. -/
def skillPath : String := ".agents/skills/regula/SKILL.md"

/-- The skill files `init` and `doctor` recognize, relative to the repository root (the root of
the Git repository that contains the project, else the project root): `skillPath`, and the path
where Claude Code discovers project skills. `init` owns both and replaces one that differs from
the installed skill, local edits included. -/
def skillPaths : List String := [skillPath, ".claude/skills/regula/SKILL.md"]

/-- The heading of the `AGENTS.md` section; its presence as a line marks the section. -/
def agentsHeading : String := "## Lean standard: Regula"

/-- The `AGENTS.md` section `init` appends. -/
def agentsSection : String :=
  agentsHeading ++ "\n\n" ++
  "This project's Lean code and proofs must meet the Regula strict standard, which may not\n" ++
  "be in your training data. Before writing or changing Lean, run\n" ++
  "`lake exe regula agent-guide` and follow it. `lake lint` enforces the rules and exits\n" ++
  "0 accepted, 1 violation, 2 invalid configuration, 3 incomplete. Each finding states what\n" ++
  "is wrong, where, and the fix; for any rule ID, `lake exe regula explain <ID>` prints the\n" ++
  "full rule offline. For machine-readable findings run\n" ++
  "`lake lint -- --json-out tmp/regula.json`. Never disable a Lean warning, weaken a statement\n" ++
  "or remove a registration to make a check pass; disable a community linter only for one\n" ++
  "declaration, where its guidance allows, with the reason.\n"

/-- The section for an `AGENTS.md` whose directory holds the Lake project at relative path `dir`:
`agentsSection`, followed, when `dir` is not the file's own directory, by where its `lake`
commands run. -/
def agentsSectionFor (dir : String) : String :=
  if dir.isEmpty then agentsSection
  else agentsSection ++ "Run these `lake` commands in `" ++ dir ++ "`, the Lake project.\n"

/-- A claimed root target: a `lean_lib` or `lean_exe` the manifest does not exclude (every root
target before a manifest exists, since the starter manifest claims them all, and none while a
manifest exists that does not load or classify every root target). -/
structure Target where
  /-- The target is a `lean_exe`; otherwise it is a `lean_lib`. -/
  exe : Bool
  /-- The target's name. -/
  name : String
  /-- The target's own `leanOptions`. Lake builds a target with the package's options followed by
  the target's own, a later value for a key replacing an earlier one; the build type adds only
  `debugAssertions`. -/
  options : List (Name × OptionValue)
  /-- The extra `lean` arguments Lake passes when it builds the target, as RG2006 reads them: the
  package's and the target's own `weakLeanArgs`, then the build type's, the package's and the
  target's own `moreLeanArgs`. -/
  arguments : List String
  deriving DecidableEq, Repr

/-- A `-D` among target `t`'s extra `lean` arguments sets option `name`, under either spelling: some
candidate of `RegulaPolicy.Community.argumentSettings`, the `-D` reading of RG2006, names it. -/
def Target.argues (t : Target) (name : Name) : Bool :=
  (argumentSettings t.arguments).any fun s => decide (optionOf s.1 = name)

/-- What the project's `lean-toolchain` selects: the toolchain `elan toolchain list` names for it
(`installedName?`) and the identity its compiler reports. -/
inductive Pin where
  /-- `selector`, the file's content, resolves to an installed compiler that reports this version
  and full commit. -/
  | compiler (selector version commit : String)
  /-- `selector` (empty when the file names no toolchain) resolves to no installed compiler that
  reports an identity; `reason` is the resolver's or the probe's error. -/
  | unresolved (selector reason : String)
  deriving DecidableEq, Repr

/-! ## Library coverage

Which modules each library leaves out, and which of them a claimed module imports, is one
function of the facts `Coverage` records. `init`'s glob edit changes those facts
(`Coverage.glob`), and the observation after it is the same function of the changed facts. -/

/-- A root `lean_lib` as the coverage decision reads it; module names are written as Lean prints
them. -/
structure Library where
  /-- The library's Lake target name. -/
  name : String
  /-- Its roots. -/
  roots : List String
  /-- The manifest does not exclude it. -/
  claimed : Bool
  /-- It sets `globs` of its own: Lake reports other globs than its roots alone, Lake's default,
  or its declaration writes a `globs` field. -/
  globbed : Bool
  /-- The modules it includes, as Lake lists them. -/
  modules : List String
  /-- The modules whose source files lie below its roots, such as `Foo.Basic` for root `Foo`: the
  modules its glob adds. -/
  below : List String
  deriving DecidableEq, Repr

/-- The facts of the root package that decide which modules its libraries leave out. -/
structure Coverage where
  /-- Each root `lean_lib`. -/
  libraries : List Library
  /-- The root module of each root `lean_exe`, which the audit counts as included. -/
  executables : List String
  /-- The root module of each root `lean_exe` the manifest does not exclude. -/
  claimedExecutables : List String
  /-- Each module whose import header the command read, with the modules of the package it imports
  as Lean's import-header parser reads them. It reads those of `Coverage.reads`, and the findings
  are the same for every table that lists the same imports for them (`coverage_congr`). -/
  imports : List (String × List String)
  deriving DecidableEq, Repr

/-- The modules library `l` includes when each library named in `S` that sets no `globs` has its
glob: then also every module below its roots. -/
def Library.modulesAt (S : List String) (l : Library) : List String :=
  if !l.globbed && S.contains l.name then l.modules ++ l.below else l.modules

/-- Library `l` with its glob: it sets `globs` and, unless it already set them, includes every
module below its roots as well. Giving it a second time changes nothing (`Library.glob_glob`). -/
def Library.glob (l : Library) : Library :=
  if l.globbed then l else { l with globbed := true, modules := l.modules ++ l.below }

theorem Library.glob_glob (l : Library) : l.glob.glob = l.glob := by
  unfold Library.glob
  split <;> simp_all

theorem Library.glob_name (l : Library) : l.glob.name = l.name := by
  unfold Library.glob
  split <;> rfl

/-- `l` with its glob when `S` names it. -/
def Library.globIn (S : List String) (l : Library) : Library :=
  if S.contains l.name then l.glob else l

theorem Library.globIn_name (S : List String) (l : Library) : (l.globIn S).name = l.name := by
  unfold Library.globIn
  split
  · exact l.glob_name
  · rfl

theorem Library.globIn_roots (S : List String) (l : Library) : (l.globIn S).roots = l.roots := by
  unfold Library.globIn Library.glob
  split <;> (try split) <;> rfl

theorem Library.globIn_claimed (S : List String) (l : Library) :
    (l.globIn S).claimed = l.claimed := by
  unfold Library.globIn Library.glob
  split <;> (try split) <;> rfl

theorem Library.globIn_below (S : List String) (l : Library) : (l.globIn S).below = l.below := by
  unfold Library.globIn Library.glob
  split <;> (try split) <;> rfl

theorem Library.globIn_globbed (S : List String) (l : Library) :
    (l.globIn S).globbed = (l.globbed || S.contains l.name) := by
  unfold Library.globIn
  cases h : S.contains l.name
  · simp
  · unfold Library.glob
    cases hg : l.globbed
    · simp
    · simp [hg]

namespace Coverage

/-- Some library, with the libraries named in `S` given their globs, or an executable root includes
module `m`. -/
def included (c : Coverage) (S : List String) (m : String) : Bool :=
  c.libraries.any (fun l => (l.modulesAt S).contains m) || c.executables.contains m

/-- The modules `m` imports, among those `imports` lists. -/
def importsOf (imports : List (String × List String)) (m : String) : List String :=
  (imports.lookup m).getD []

/-- The modules reached from `frontier`, after `seen`, following `imports`, for at most `fuel`
rounds; each round adds the modules of the frontier not seen yet, and the walk stops at a round
that adds none. -/
def reach (imports : List (String × List String)) :
    Nat → List String → List String → List String
  | 0, seen, _ => seen
  | fuel + 1, seen, frontier =>
    let new := (frontier.filter (!seen.contains ·)).eraseDups
    if new.isEmpty then seen else reach imports fuel (seen ++ new) (new.flatMap (importsOf imports))

/-- The modules whose imports the walk of `reach` reads: those each round adds. -/
def reachReads (imports : List (String × List String)) :
    Nat → List String → List String → List String
  | 0, _, _ => []
  | fuel + 1, seen, frontier =>
    let new := (frontier.filter (!seen.contains ·)).eraseDups
    if new.isEmpty then []
    else new ++ reachReads imports fuel (seen ++ new) (new.flatMap (importsOf imports))

/-- The walk reads only the imports of the modules `reachReads` names: two import tables that list
the same imports for each of them give the same walk. -/
theorem reach_congr (A B : List (String × List String)) (fuel : Nat) (seen frontier : List String)
    (h : ∀ m ∈ reachReads A fuel seen frontier, importsOf A m = importsOf B m) :
    reach A fuel seen frontier = reach B fuel seen frontier ∧
      reachReads A fuel seen frontier = reachReads B fuel seen frontier := by
  induction fuel generalizing seen frontier with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    simp only [reach, reachReads] at h ⊢
    by_cases hn : ((frontier.filter (!seen.contains ·)).eraseDups).isEmpty = true
    · simp only [hn, ↓reduceIte, and_self]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h ⊢
      have hmap : ((frontier.filter (!seen.contains ·)).eraseDups).flatMap (importsOf A) =
          ((frontier.filter (!seen.contains ·)).eraseDups).flatMap (importsOf B) := by
        simp only [List.flatMap_def]
        congr 1
        exact List.map_congr_left fun m hm => h m (List.mem_append_left _ hm)
      have := ih _ _ fun m hm => h m (List.mem_append_right _ hm)
      rw [hmap] at this ⊢
      exact ⟨this.1, by rw [this.2]⟩

/-- The modules library `l` includes once it has its glob: also every module below its roots
unless it sets `globs` of its own. -/
def _root_.Regula.Setup.Library.globbedModules (l : Library) : List String :=
  if l.globbed then l.modules else l.modules ++ l.below

/-- The rounds the walk of `witnesses` may take: one more than the modules the facts name, each
library's counted as `Library.globbedModules` and its `below` again, which a glob leaves unchanged
(`fuel_globAll`). Each round that runs adds a module an import names, and the command lists only
imports of modules the facts name, so the bound lets each such round run; that is by counting,
not a theorem. -/
def fuel (c : Coverage) : Nat :=
  (c.libraries.map fun l => l.globbedModules.length + l.below.length).sum +
    c.executables.length + 1

/-- The modules a claimed module of the facts is: each module of a claimed library, with the
libraries named in `S` that set no `globs` given their globs, and each claimed executable root. -/
def starts (c : Coverage) (S : List String) : List String :=
  (c.libraries.filter (·.claimed)).flatMap (·.modulesAt S) ++ c.claimedExecutables

/-- The modules a claimed module imports, directly or through other modules of the package, when
each library named in `S` that sets no `globs` has its glob, so that the modules below its roots
are claimed when it is. A module counts only when an import names it, never as a start of the
walk. -/
def witnesses (c : Coverage) (S : List String) : List String :=
  reach c.imports c.fuel [] ((c.starts S).flatMap (importsOf c.imports))

/-- The modules whose imports `witnesses` reads: the starts and each module the walk adds. -/
def readsAt (c : Coverage) (S : List String) : List String :=
  c.starts S ++ reachReads c.imports c.fuel [] ((c.starts S).flatMap (importsOf c.imports))

/-- Facts that differ at most in their imports, and list the same imports for each module of `R`. -/
def Agree (c c' : Coverage) (R : List String) : Prop :=
  c.libraries = c'.libraries ∧ c.executables = c'.executables ∧
    c.claimedExecutables = c'.claimedExecutables ∧
    ∀ m ∈ R, importsOf c.imports m = importsOf c'.imports m

theorem witnesses_congr {c c' : Coverage} {S : List String} (h : c.Agree c' (c.readsAt S)) :
    c.witnesses S = c'.witnesses S := by
  obtain ⟨hl, he, hc, hi⟩ := h
  have hs : c.starts S = c'.starts S := by simp only [starts, hl, hc]
  have hf : c.fuel = c'.fuel := by simp only [fuel, hl, he]
  have hmap : (c.starts S).flatMap (importsOf c.imports) =
      (c.starts S).flatMap (importsOf c'.imports) := by
    simp only [List.flatMap_def]
    congr 1
    exact List.map_congr_left fun m hm => hi m (List.mem_append_left _ hm)
  unfold witnesses
  rw [← hs, ← hf, (reach_congr c.imports c'.imports c.fuel [] _
    fun m hm => hi m (List.mem_append_right _ hm)).1, hmap]

/-- The modules below the roots of `l` that no library includes and that a claimed module imports
(`w`, the `witnesses`), when each library named in `S` that sets no `globs` has its glob. -/
def uncoveredIn (c : Coverage) (S w : List String) (l : Library) : List String :=
  l.below.filter fun m => !c.included S m && w.contains m

/-- The libraries that set no `globs`, are not named in `S`, and leave out a module that a claimed
module imports when those of `S` have their globs. -/
def nextGlobs (c : Coverage) (S : List String) : List String :=
  let w := c.witnesses S
  (c.libraries.filter fun l =>
    !l.globbed && !S.contains l.name && !(c.uncoveredIn S w l).isEmpty).map (·.name)

/-- The libraries that set no `globs` and are not named in `S`. -/
def pending (c : Coverage) (S : List String) : Nat :=
  (c.libraries.filter fun l => !l.globbed && !S.contains l.name).length

/-- Of the elements of `l`, no more satisfy `q` than `p` when each that satisfies `q` satisfies
`p`. -/
theorem length_filter_le {α : Type} (l : List α) (p q : α → Bool)
    (hqp : ∀ x ∈ l, q x = true → p x = true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih := ih fun x hx => hqp x (List.mem_cons_of_mem a hx)
    by_cases hq : q a = true
    · have hp : p a = true := hqp a (by simp) hq
      simp [hq, hp]
      omega
    · by_cases hp : p a = true
      · simp [hq, hp]
        omega
      · simp [hq, hp]
        omega

/-- Of the elements of `l`, fewer satisfy `q` than `p` when each that satisfies `q` satisfies `p`
and one satisfies `p` but not `q`. -/
theorem length_filter_lt {α : Type} (l : List α) (p q : α → Bool)
    (hqp : ∀ x ∈ l, q x = true → p x = true) (hx : ∃ x ∈ l, p x = true ∧ q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    have hle := length_filter_le t p q fun x hx => hqp x (List.mem_cons_of_mem a hx)
    obtain ⟨x, hx, hpx, hqx⟩ := hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hpx, hqx]
      omega
    · have ih := ih (fun y hy => hqp y (List.mem_cons_of_mem a hy)) ⟨x, hx, hpx, hqx⟩
      by_cases hq : q a = true
      · have hp : p a = true := hqp a (by simp) hq
        simp [hq, hp]
        omega
      · by_cases hp : p a = true
        · simp [hq, hp]
          omega
        · simp [hq, hp]
          omega

/-- A round that adds a library leaves fewer libraries pending. -/
theorem pending_lt (c : Coverage) (S : List String) (h : c.nextGlobs S ≠ []) :
    c.pending (S ++ c.nextGlobs S) < c.pending S := by
  obtain ⟨n, hn⟩ := List.exists_mem_of_ne_nil _ h
  have hn' := hn
  simp only [nextGlobs] at hn'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn'
  obtain ⟨hmem, hp⟩ := List.mem_filter.mp hl
  unfold pending
  apply length_filter_lt
  · intro k _ hk
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_append,
      Bool.or_eq_false_iff] at hk ⊢
    exact ⟨hk.1, hk.2.1⟩
  · refine ⟨l, hmem, ?_, ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
      exact ⟨hp.1.1, hp.1.2⟩
    · simp [hn]

/-- The libraries `init` gives a glob, from those of `S`: rounds of `nextGlobs` until one adds
none. -/
def globsFrom (c : Coverage) (S : List String) : List String :=
  if _h : c.nextGlobs S = [] then S else globsFrom c (S ++ c.nextGlobs S)
termination_by c.pending S
decreasing_by exact c.pending_lt S (by assumption)

/-- The libraries `init` gives a glob. -/
def globbing (c : Coverage) : List String := c.globsFrom []

/-- At the libraries `globsFrom` returns, no further library needs a glob. -/
theorem nextGlobs_globsFrom (c : Coverage) (S : List String) : c.nextGlobs (c.globsFrom S) = [] := by
  rw [globsFrom]
  split
  · assumption
  · exact nextGlobs_globsFrom c _
termination_by c.pending S
decreasing_by exact c.pending_lt S (by assumption)

/-- The modules whose imports `globsFrom` reads, round by round (`readsAt`), ending with those
read at the libraries it returns. -/
def globReads (c : Coverage) (S : List String) : List String :=
  c.readsAt S ++ if _h : c.nextGlobs S = [] then [] else globReads c (S ++ c.nextGlobs S)
termination_by c.pending S
decreasing_by exact c.pending_lt S (by assumption)

/-- The modules whose imports the decision reads: `globReads` from no library. The command reads
the import header of these modules alone, and the decision is the same for every import table
that lists the same imports for them (`globbing_congr`, `witnesses_globbing_congr`). -/
def reads (c : Coverage) : List String := c.globReads []

theorem Agree.mono {c c' : Coverage} {R R' : List String} (h : c.Agree c' R)
    (hR : ∀ m ∈ R', m ∈ R) : c.Agree c' R' :=
  ⟨h.1, h.2.1, h.2.2.1, fun m hm => h.2.2.2 m (hR m hm)⟩

theorem readsAt_subset_globReads (c : Coverage) (S : List String) :
    ∀ m ∈ c.readsAt S, m ∈ c.globReads S := by
  intro m hm
  rw [globReads]
  exact List.mem_append_left _ hm

theorem readsAt_globsFrom (c : Coverage) (S : List String) :
    ∀ m ∈ c.readsAt (c.globsFrom S), m ∈ c.globReads S := by
  intro m hm
  rw [globsFrom] at hm
  rw [globReads]
  by_cases h : c.nextGlobs S = []
  · simp only [h, ↓reduceDIte] at hm ⊢
    exact List.mem_append_left _ hm
  · simp only [h, ↓reduceDIte] at hm ⊢
    exact List.mem_append_right _ (readsAt_globsFrom c _ m hm)
termination_by c.pending S
decreasing_by exact c.pending_lt S h

theorem nextGlobs_congr {c c' : Coverage} {S : List String} (h : c.Agree c' (c.readsAt S)) :
    c.nextGlobs S = c'.nextGlobs S := by
  have hw := witnesses_congr h
  obtain ⟨hl, he, -, -⟩ := h
  simp only [nextGlobs, uncoveredIn, included, hw, hl, he]

/-- Facts that list the same imports for each module `globReads` names give the same globs. -/
theorem globsFrom_congr {c c' : Coverage} (S : List String) (h : c.Agree c' (c.globReads S)) :
    c.globsFrom S = c'.globsFrom S := by
  have hn : c.nextGlobs S = c'.nextGlobs S :=
    nextGlobs_congr (h.mono (readsAt_subset_globReads c S))
  conv => lhs; rw [globsFrom]
  conv => rhs; rw [globsFrom]
  by_cases hx : c.nextGlobs S = []
  · have hx' : c'.nextGlobs S = [] := hn ▸ hx
    simp only [hx, hx', ↓reduceDIte]
  · have hx' : ¬c'.nextGlobs S = [] := hn ▸ hx
    simp only [hx, hx', ↓reduceDIte]
    rw [← hn]
    refine globsFrom_congr _ (h.mono fun m hm => ?_)
    rw [globReads]
    simp only [hx, ↓reduceDIte]
    exact List.mem_append_right _ hm
termination_by c.pending S
decreasing_by exact c.pending_lt S hx

theorem globbing_congr {c c' : Coverage} (h : c.Agree c' c.reads) : c.globbing = c'.globbing :=
  globsFrom_congr [] h

theorem witnesses_globbing_congr {c c' : Coverage} (h : c.Agree c' c.reads) :
    c.witnesses c.globbing = c'.witnesses c'.globbing := by
  rw [← globbing_congr h]
  exact witnesses_congr (h.mono (readsAt_globsFrom c []))

/-- The facts with the library named `name` given its glob (`Library.glob`). -/
def glob (c : Coverage) (name : String) : Coverage :=
  { c with libraries := c.libraries.map fun l => if l.name == name then l.glob else l }

/-- The facts with each library named in `S` given its glob. -/
def globAll (c : Coverage) (S : List String) : Coverage :=
  { c with libraries := c.libraries.map (Library.globIn S) }

theorem globAll_libraries (c : Coverage) (S : List String) :
    (c.globAll S).libraries = c.libraries.map (Library.globIn S) := rfl

/-- Giving the libraries named in `N` their globs one at a time gives each of them its glob. -/
theorem foldl_glob (c : Coverage) (N : List String) : N.foldl glob c = c.globAll N := by
  induction N generalizing c with
  | nil =>
    have h : c.libraries.map (Library.globIn []) = c.libraries := by
      conv => rhs; rw [← List.map_id c.libraries]
      exact List.map_congr_left fun l _ => by simp [Library.globIn]
    rw [List.foldl_nil, globAll, h]
  | cons n N ih =>
    rw [List.foldl_cons, ih]
    simp only [glob, globAll, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply, Library.globIn, List.contains_cons]
    by_cases h : l.name = n
    · simp [h, Library.glob_glob]
    · simp [h]

/-- With the libraries of `S` given their globs, a library includes what it would include, with
those globs, before. -/
theorem modulesAt_globIn (S : List String) (l : Library) :
    (l.globIn S).modulesAt [] = l.modulesAt S := by
  unfold Library.globIn Library.modulesAt
  cases h : S.contains l.name <;> cases hg : l.globbed <;> simp [Library.glob, hg]

theorem included_globAll (c : Coverage) (S : List String) (m : String) :
    (c.globAll S).included [] m = c.included S m := by
  simp [included, globAll, List.any_map, Function.comp_def, modulesAt_globIn]

theorem _root_.Regula.Setup.Library.globIn_globbedModules (S : List String) (l : Library) :
    (l.globIn S).globbedModules = l.globbedModules := by
  unfold Library.globIn Library.glob Library.globbedModules
  cases h : S.contains l.name <;> cases hg : l.globbed <;> simp [hg]

theorem fuel_globAll (c : Coverage) (S : List String) : (c.globAll S).fuel = c.fuel := by
  simp only [fuel, globAll, List.map_map, Function.comp_def, Library.globIn_globbedModules,
    Library.globIn_below]

theorem starts_globAll (c : Coverage) (S : List String) : (c.globAll S).starts [] = c.starts S := by
  simp [starts, globAll, List.filter_map, List.flatMap_map, Function.comp_def,
    modulesAt_globIn, Library.globIn_claimed]

theorem witnesses_globAll (c : Coverage) (S : List String) :
    (c.globAll S).witnesses [] = c.witnesses S := by
  simp only [witnesses, fuel_globAll, starts_globAll]
  rfl

theorem uncoveredIn_globAll (c : Coverage) (S w : List String) (l : Library) :
    (c.globAll S).uncoveredIn [] w (l.globIn S) = c.uncoveredIn S w l := by
  simp only [uncoveredIn, Library.globIn_below, included_globAll]

/-- With the libraries `nextGlobs` would add given their globs, no further one needs a glob. -/
theorem nextGlobs_globAll (c : Coverage) (S : List String) (h : c.nextGlobs S = []) :
    (c.globAll S).nextGlobs [] = [] := by
  simp only [nextGlobs, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h ⊢
  rw [witnesses_globAll, globAll_libraries]
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  rw [uncoveredIn_globAll, Library.globIn_globbed]
  have := h l hl
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, List.contains_nil,
    Bool.not_false, and_true, not_and] at this ⊢
  intro hg hu
  exact this hg hu

/-- After the globs of `globbing` are written, no library needs one. -/
theorem globbing_globAll (c : Coverage) : (c.globAll c.globbing).globbing = [] := by
  have h := nextGlobs_globAll c _ (nextGlobs_globsFrom c [])
  rw [globbing, globsFrom]
  exact dite_eq_left_of_eq_true (eq_true h)

end Coverage

/-- What `init` and `doctor` observe of a project. -/
structure Observation where
  /-- The root package's `lintDriver`; empty when it is not set. -/
  driver : String
  /-- The root package's own `leanOptions`, each key once, as Lake resolves the package
  configuration (without build-type or target options). -/
  options : List (Name × OptionValue)
  /-- The claimed root targets, the targets RG2006 checks. -/
  targets : List Target
  /-- Every root `lean_lib` and `lean_exe` is claimed, so the package's options reach only claimed
  targets. -/
  allClaimed : Bool
  /-- The workspace contains Mathlib, so a claimed target may import it. -/
  mathlib : Bool
  /-- `foundation_manifest.json` exists at the project root. -/
  manifest : Bool
  /-- The root package has a `lean_lib`. A manifest claims each surface per library, an executable
  belonging to a library's surface, so without one there is nothing for the starter to claim. -/
  libraries : Bool
  /-- The agent-guidance file, relative to the project root: among the `AGENTS.md` files from the
  project root up to the repository root, the nearest with the `agentsHeading` line, else the
  nearest that exists, else the repository root's (the project root outside a Git repository). -/
  agentsFile : String
  /-- `agentsFile` contains the `agentsHeading` line. -/
  agentsSection : Bool
  /-- The skill file `init --skill` writes, relative to the project root: `skillPath` at the
  repository root, such as `../.agents/skills/regula/SKILL.md`. -/
  skillFile : String
  /-- Each file of `skillPaths` at the repository root that exists, relative to the project root,
  and whether it equals the installed skill. -/
  skills : List (String × Bool)
  /-- The compiler the project's own `lean-toolchain` selects, whichever compiler runs `regula`. -/
  pin : Pin
  /-- The root package's libraries, executables and imports (`Coverage`). -/
  coverage : Coverage
  deriving DecidableEq, Repr

/-- Each library `init` gives a glob (`Coverage.globbing`), with its roots and the modules below
them that no library includes and that a claimed module imports once those globs are written. -/
def Observation.unglobbed (o : Observation) : List (String × List String × List String) :=
  let c := o.coverage
  let S := c.globbing
  let w := c.witnesses S
  (c.libraries.filter fun l => !l.globbed && S.contains l.name).map fun l =>
    (l.name, l.roots, l.below.filter fun m => !c.included [] m && w.contains m)

/-- Each library with its roots and the modules below them that no library includes and that a
claimed module imports, once the globs of `unglobbed` are written: the audit finds them outside
every library. -/
def Observation.uncovered (o : Observation) : List (String × List String × List String) :=
  let c := o.coverage
  let S := c.globbing
  let w := c.witnesses S
  (c.libraries.filter fun l => !(c.uncoveredIn S w l).isEmpty).map fun l =>
    (l.name, l.roots, c.uncoveredIn S w l)

/-- The same for the modules that no library includes and no claimed module imports: the audit
neither inspects them nor fails, so `doctor` only notes them. -/
def Observation.unimported (o : Observation) : List (String × List String × List String) :=
  let c := o.coverage
  let S := c.globbing
  let w := c.witnesses S
  let gone (l : Library) := l.below.filter fun m => !c.included S m && !w.contains m
  (c.libraries.filter fun l => !(gone l).isEmpty).map fun l => (l.name, l.roots, gone l)

/-- The coverage findings read only the imports of `Coverage.reads`: facts that list the same
imports for each of those modules give the same findings, whatever they list for any other. -/
theorem coverage_congr (o : Observation) (c : Coverage) (h : o.coverage.Agree c o.coverage.reads) :
    { o with coverage := c }.unglobbed = o.unglobbed ∧
      { o with coverage := c }.uncovered = o.uncovered ∧
      { o with coverage := c }.unimported = o.unimported := by
  have hg := Coverage.globbing_congr h
  have hw := Coverage.witnesses_globbing_congr h
  obtain ⟨hl, he, -, -⟩ := h
  simp only [Observation.unglobbed, Observation.uncovered, Observation.unimported,
    Coverage.uncoveredIn, Coverage.included]
  rw [← hw, ← hg, ← hl, ← he]
  exact ⟨rfl, rfl, rfl⟩

/-- The key `init` writes for option `name`: Mathlib's options under `weak.`, which Lean ignores
in a module that does not import Mathlib, and every other option as it is. -/
def key (name : Name) : Name :=
  if (mathlibBaseline.map Prod.fst).contains name then `weak ++ name else name

/-- Claimed target `t` builds without required option `r`: neither the package's nor its own
`leanOptions` give it a value under either spelling, and no `-D` among its extra `lean` arguments
sets it. -/
def Observation.without (o : Observation) (t : Target) (r : Name × OptionValue) : Bool :=
  (valuesOf ⟨o.options ++ t.options, []⟩ r.1).isEmpty && !t.argues r.1

/-- A required option `init` adds to the package: every root target is claimed, so the package's
options reach only claimed targets; some claimed target builds without it; and no claimed target's
`-D` sets it, so the entry reaches no target where a `-D` also sets the option. -/
def Observation.lacks (o : Observation) (r : Name × OptionValue) : Bool :=
  o.allClaimed && o.targets.any (o.without · r) && !o.targets.any (·.argues r.1)

/-- The options `init` adds to the package: every required option the observation `lacks`, with
its required value, keyed by `key`. An option given a wrong value is left for its owner to change
(`doctor` reports it through RG2006). -/
def missing (o : Observation) : List (Name × OptionValue) :=
  ((required o.mathlib).filter o.lacks).map fun r => (key r.1, r.2)

/-- The options `init` adds to claimed target `t`: every required option `t` builds without that
the package does not receive (`lacks`), with its required value, keyed by `key`. When every root
target is claimed, these are the options some other claimed target sets with a `-D`. -/
def targetMissing (o : Observation) (t : Target) : List (Name × OptionValue) :=
  ((required o.mathlib).filter fun r => o.without t r && !o.lacks r).map fun r => (key r.1, r.2)

/-- Claimed target `t` sets required option `r` only with a `-D`: the package's and its own
`leanOptions` give it no value under either spelling, and a `-D` among its extra `lean` arguments
sets it. -/
def Observation.onlyArgued (o : Observation) (t : Target) (r : Name × OptionValue) : Bool :=
  (valuesOf ⟨o.options ++ t.options, []⟩ r.1).isEmpty && t.argues r.1

/-- The required options claimed target `t` sets only with a `-D`. -/
def Observation.arguedBy (o : Observation) (t : Target) : List (Name × OptionValue) :=
  (required o.mathlib).filter (o.onlyArgued t)

/-- The required options some claimed target sets only with a `-D`. RG2006 requires the value in
`leanOptions`, and `init` adds none beside the `-D`. Each comes with its required value, keyed by
`key`: the entry to write in `leanOptions` instead. -/
def argued (o : Observation) : List (Name × OptionValue) :=
  ((required o.mathlib).filter fun r => o.targets.any (o.onlyArgued · r)).map
    fun r => (key r.1, r.2)

/-- One missing or wrong piece of setup. -/
inductive Issue where
  /-- The package sets no `lintDriver`, so `lake lint` does not run Regula. -/
  | driverUnset
  /-- The package's `lintDriver` is another driver; Lake has one per package. -/
  | driverOther (driver : String)
  /-- The package gives no value to these required options (the entries `init` adds to it). -/
  | optionsMissing (entries : List (Name × OptionValue))
  /-- Claimed target `name`, a `lean_exe` when `exe` and otherwise a `lean_lib`, builds without
  these required options, which neither the package nor the target sets (the entries `init` adds
  to the target, because some root target is excluded or another claimed target's `-D` sets
  them). -/
  | targetOptionsMissing (exe : Bool) (name : String) (entries : List (Name × OptionValue))
  /-- A claimed target sets these required options only with a `-D` among its extra `lean`
  arguments, where RG2006 requires them in `leanOptions`; `init` adds no second setting. The
  entries are the ones to write there instead. -/
  | argued (entries : List (Name × OptionValue))
  /-- There is no `foundation_manifest.json`. -/
  | manifestMissing
  /-- The root package has no `lean_lib`, so no surface can be claimed. -/
  | noLibrary
  /-- There is neither an `agentsHeading` section in `file` nor a skill file; `skill` is the one
  `init --skill` writes. -/
  | guidanceMissing (file skill : String)
  /-- The skill file at `path` differs from the installed Regula's skill. -/
  | skillStale (path : String)
  /-- The project's `lean-toolchain`, `selector`, selects the compiler reporting `version` and
  `commit`, which is not the compiler this Regula revision declares. -/
  | toolchain (selector version commit : String)
  /-- The project's `lean-toolchain`, `selector`, selects no installed compiler that reports its
  identity (`reason`), so it cannot be compared with the compiler this Regula revision declares. -/
  | toolchainUnresolved (selector reason : String)
  /-- `lean_lib` `library`, with roots `roots` and `globs` of its own, includes none of `modules`,
  which lie below them. -/
  | uncovered (library : String) (roots modules : List String)
  /-- `lean_lib` `library`, with roots `roots` and no `globs`, includes none of `modules`, which
  lie below them (the glob `init` adds includes them). -/
  | unglobbed (library : String) (roots modules : List String)
  deriving DecidableEq, Repr

/-- Whether `init` writes the fix. It never replaces another lint driver, nor changes the `globs`
a library sets. -/
def Issue.fixable : Issue → Bool
  | .driverUnset => true
  | .driverOther _ => false
  | .optionsMissing _ => true
  | .targetOptionsMissing _ _ _ => true
  | .argued _ => false
  | .manifestMissing => true
  | .noLibrary => false
  | .guidanceMissing _ _ => true
  | .skillStale _ => true
  | .toolchain _ _ _ => false
  | .toolchainUnresolved _ _ => false
  | .uncovered _ _ _ => false
  | .unglobbed _ _ _ => true

/-- `init` writes the starter manifest: there is none, and the package has a library for it to
claim. -/
def Observation.starter (o : Observation) : Bool := !o.manifest && o.libraries

/-- The skill files that differ from the installed skill. -/
def staleSkills (o : Observation) : List String := (o.skills.filter (!·.2)).map (·.1)

/-- The project has agent guidance: the `AGENTS.md` section or a skill file. -/
def Observation.guided (o : Observation) : Bool := o.agentsSection || !o.skills.isEmpty

/-- The lint-driver issue, if any. -/
def driverIssues (o : Observation) : List Issue :=
  if o.driver = "" then [.driverUnset] else if o.driver = lintDriver then [] else
    [.driverOther o.driver]

/-- The issue of one library entry of `Observation.uncovered`. -/
def uncoveredIssue (entry : String × List String × List String) : Issue :=
  .uncovered entry.1 entry.2.1 entry.2.2

/-- The issue of one library entry of `Observation.unglobbed`. -/
def unglobbedIssue (entry : String × List String × List String) : Issue :=
  .unglobbed entry.1 entry.2.1 entry.2.2

/-- The option issues: the options the package must add, then each claimed target's own. -/
def optionIssues (o : Observation) : List Issue :=
  (if missing o = [] then [] else [.optionsMissing (missing o)]) ++
  o.targets.filterMap fun t =>
    if targetMissing o t = [] then none
    else some (.targetOptionsMissing t.exe t.name (targetMissing o t))

/-- The issue of the required options claimed targets set only with a `-D`, reported once. -/
def arguedIssues (o : Observation) : List Issue :=
  if argued o = [] then [] else [.argued (argued o)]

/-- The toolchain issue, if any: the compiler the project's `lean-toolchain` selects must have the
identity this Regula revision declares (`RegulaPolicy.Compiler.accepts`), under any selector, and
a pin that resolves to no compiler is an issue. -/
def toolchainIssues (o : Observation) : List Issue :=
  match o.pin with
  | .compiler selector version commit =>
    if RegulaPolicy.Compiler.accepts version commit then []
    else [.toolchain selector version commit]
  | .unresolved selector reason => [.toolchainUnresolved selector reason]

/-- `doctor` reports no toolchain issue exactly when the project's `lean-toolchain` resolves to a
compiler whose reported identity is the one this Regula revision declares (`Compiler.Supports`). -/
theorem toolchainIssues_eq_nil_iff (o : Observation) :
    toolchainIssues o = [] ↔ ∃ selector version commit,
      o.pin = .compiler selector version commit ∧
        RegulaPolicy.Compiler.Supports version commit := by
  unfold toolchainIssues
  split
  · next s v c hp =>
    rw [hp]
    constructor
    · intro h
      refine ⟨s, v, c, rfl, (RegulaPolicy.Compiler.accepts_iff v c).mp ?_⟩
      by_cases ha : RegulaPolicy.Compiler.accepts v c = true
      · exact ha
      · simp [ha] at h
    · rintro ⟨_, _, _, heq, hs⟩
      cases heq
      simp [(RegulaPolicy.Compiler.accepts_iff v c).mpr hs]
  · next s r hp =>
    rw [hp]
    constructor
    · intro h
      exact absurd h (List.cons_ne_nil _ _)
    · rintro ⟨_, _, _, heq, _⟩
      cases heq

/-- `init` writes no fix for a toolchain issue. -/
theorem toolchainIssues_unfixable (o : Observation) :
    ∀ i ∈ toolchainIssues o, i.fixable = false := by
  intro i hi
  unfold toolchainIssues at hi
  split at hi
  · split at hi
    · simp at hi
    · rw [List.mem_singleton] at hi
      rw [hi]
      rfl
  · rw [List.mem_singleton] at hi
    rw [hi]
    rfl

/-- Every setup issue of an observation, in a fixed order. -/
def issues (o : Observation) : List Issue :=
  driverIssues o ++
  optionIssues o ++
  arguedIssues o ++
  (if o.starter then [.manifestMissing] else []) ++
  (if o.libraries then [] else [.noLibrary]) ++
  (if o.guided then [] else [.guidanceMissing o.agentsFile o.skillFile]) ++
  (staleSkills o).map .skillStale ++
  toolchainIssues o ++
  o.unglobbed.map unglobbedIssue ++
  o.uncovered.map uncoveredIssue

/-- One edit `init` writes. -/
inductive Edit where
  /-- Set the package's `lintDriver` to `lintDriver`. -/
  | driver
  /-- Add these entries to the package's `leanOptions`. -/
  | options (entries : List (Name × OptionValue))
  /-- Add the `options` of each entry of `added` to the `leanOptions` of the claimed target at the
  same position of `Observation.targets`. -/
  | targetOptions (added : List Target)
  /-- Write the starter `foundation_manifest.json`. -/
  | manifest
  /-- Append `agentsSectionFor` the Lake project's directory to the agent-guidance file `file`,
  creating it if needed. -/
  | agentsSection (file : String)
  /-- Write the installed skill at `path`. -/
  | skill (path : String)
  /-- Give `lean_lib` `library`, which sets no `globs`, the glob that includes every module below
  its roots `roots`. -/
  | globs (library : String) (roots : List String)
  deriving DecidableEq, Repr

/-- The guidance edit when the project has none: the preference `g`. -/
def guidanceEdits (g : Guidance) (o : Observation) : List Edit :=
  if o.guided then [] else
    match g with
    | .agentsMd => [.agentsSection o.agentsFile]
    | .skill => [.skill o.skillFile]

/-- The option edits: the package's missing options, then each claimed target's own, so that no
option reaches a target the manifest excludes or a target whose `-D` sets it. -/
def optionEdits (o : Observation) : List Edit :=
  (if missing o = [] then [] else [.options (missing o)]) ++
  if o.targets.all (fun t => targetMissing o t = []) then []
  else [.targetOptions (o.targets.map fun t => { t with options := targetMissing o t })]

/-- The glob edits: one for each library of `Observation.unglobbed`. -/
def globEdits (o : Observation) : List Edit :=
  o.unglobbed.map fun e => .globs e.1 e.2.1

/-- The edits that fix `o`'s fixable issues, each writing only what is missing. -/
def plan (g : Guidance) (o : Observation) : List Edit :=
  (if o.driver = "" then [.driver] else []) ++
  optionEdits o ++
  (if o.starter then [.manifest] else []) ++
  guidanceEdits g o ++
  (staleSkills o).map .skill ++
  globEdits o

/-- Record that the skill file at `path` equals the installed skill. -/
def markCurrent (path : String) (skills : List (String × Bool)) : List (String × Bool) :=
  if skills.any (·.1 == path) then skills.map fun s => if s.1 == path then (s.1, true) else s
  else skills ++ [(path, true)]

/-- Each target of `ts` with the options of the entry of `added` at its position appended. -/
def addTargets (ts added : List Target) : List Target :=
  List.zipWith (fun t a => { t with options := t.options ++ a.options }) ts added

/-- The effect of one edit on the observation. -/
def apply (o : Observation) : Edit → Observation
  | .driver => { o with driver := lintDriver }
  | .options entries => { o with options := o.options ++ entries }
  | .targetOptions added => { o with targets := addTargets o.targets added }
  | .manifest => { o with manifest := true }
  | .agentsSection _ => { o with agentsSection := true }
  | .skill path => { o with skills := markCurrent path o.skills }
  | .globs library _ => { o with coverage := o.coverage.glob library }

/-- The observation after applying `edits` in order. -/
def run (o : Observation) (edits : List Edit) : Observation := edits.foldl apply o

/-! ## The effect of an edit list, field by field -/

/-- The options entries an edit adds. -/
def Edit.entries : Edit → List (Name × OptionValue)
  | .options entries => entries
  | _ => []

/-- The skill file an edit writes. -/
def Edit.skillFile? : Edit → Option String
  | .skill path => some path
  | _ => none

/-- The target entries an edit adds. -/
def Edit.added? : Edit → Option (List Target)
  | .targetOptions added => some added
  | _ => none

/-- The edit appends the agent-guidance section. -/
def Edit.writesSection : Edit → Bool
  | .agentsSection _ => true
  | _ => false

/-- The library an edit gives a glob. -/
def Edit.library? : Edit → Option String
  | .globs library _ => some library
  | _ => none

/-- Mark each of `paths` current, in order. -/
def markAll (skills : List (String × Bool)) (paths : List String) : List (String × Bool) :=
  paths.foldl (fun l p => markCurrent p l) skills

theorem run_driver (o : Observation) (es : List Edit) :
    (run o es).driver = if Edit.driver ∈ es then lintDriver else o.driver := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply]

theorem run_options (o : Observation) (es : List Edit) :
    (run o es).options = o.options ++ es.flatMap Edit.entries := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.entries]

theorem run_mathlib (o : Observation) (es : List Edit) : (run o es).mathlib = o.mathlib := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> rfl

theorem run_libraries (o : Observation) (es : List Edit) :
    (run o es).libraries = o.libraries := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> rfl

theorem run_allClaimed (o : Observation) (es : List Edit) :
    (run o es).allClaimed = o.allClaimed := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> rfl

theorem run_targets (o : Observation) (es : List Edit) :
    (run o es).targets = (es.filterMap Edit.added?).foldl addTargets o.targets := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.added?, List.filterMap_cons]

theorem run_toolchain (o : Observation) (es : List Edit) : (run o es).pin = o.pin := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> rfl

theorem run_manifest (o : Observation) (es : List Edit) :
    (run o es).manifest = (o.manifest || decide (Edit.manifest ∈ es)) := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply]

theorem run_agentsSection (o : Observation) (es : List Edit) :
    (run o es).agentsSection = (o.agentsSection || es.any Edit.writesSection) := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.writesSection]

theorem run_skills (o : Observation) (es : List Edit) :
    (run o es).skills = markAll o.skills (es.filterMap Edit.skillFile?) := by
  induction es generalizing o with
  | nil => simp [run, markAll]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.skillFile?, markAll, List.filterMap_cons]

theorem run_coverage (o : Observation) (es : List Edit) :
    (run o es).coverage = (es.filterMap Edit.library?).foldl Coverage.glob o.coverage := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.library?, List.filterMap_cons]

/-! ## Skill files -/

/-- An entry after `markCurrent` is the marked path, or an entry at another path unchanged. -/
theorem mem_markCurrent {path : String} {skills : List (String × Bool)} {s : String × Bool}
    (h : s ∈ markCurrent path skills) : (s ∈ skills ∧ s.1 ≠ path) ∨ s = (path, true) := by
  unfold markCurrent at h
  split at h
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    by_cases hp : t.1 = path
    · exact .inr (by simp [hp])
    · exact .inl ⟨by simp [hp, ht], by simp [hp]⟩
  · rename_i hany
    rcases List.mem_append.mp h with h | h
    · refine .inl ⟨h, fun hp => hany ?_⟩
      exact List.any_eq_true.mpr ⟨s, h, by simp [hp]⟩
    · exact .inr (by simpa using h)

/-- `markCurrent` never yields the empty list. -/
theorem markCurrent_ne_nil (path : String) (skills : List (String × Bool)) :
    markCurrent path skills ≠ [] := by
  unfold markCurrent
  split
  · rename_i h
    intro hn
    rw [List.map_eq_nil_iff] at hn
    simp [hn] at h
  · simp

/-- After marking `paths`, every entry is a marked path, or an entry at an unmarked path. -/
theorem mem_markAll {skills : List (String × Bool)} {paths : List String} {s : String × Bool}
    (h : s ∈ markAll skills paths) : (s ∈ skills ∧ s.1 ∉ paths) ∨ s.2 = true := by
  induction paths generalizing skills with
  | nil => exact .inl ⟨h, by simp⟩
  | cons p ps ih =>
    simp only [markAll, List.foldl_cons] at h
    rcases ih h with ⟨hm, hn⟩ | ht
    · rcases mem_markCurrent hm with ⟨hs, hp⟩ | rfl
      · exact .inl ⟨hs, by simp_all⟩
      · exact .inr rfl
    · exact .inr ht

theorem markAll_ne_nil {skills : List (String × Bool)} (paths : List String)
    (h : skills ≠ [] ∨ paths ≠ []) : markAll skills paths ≠ [] := by
  induction paths generalizing skills with
  | nil => simpa [markAll] using h
  | cons p ps ih =>
    simp only [markAll, List.foldl_cons]
    exact ih (.inl (markCurrent_ne_nil p skills))

/-! ## Options -/

theorem valuesOf_append (a b : List (Name × OptionValue)) (n : Name) :
    valuesOf ⟨a ++ b, []⟩ n = valuesOf ⟨a, []⟩ n ++ valuesOf ⟨b, []⟩ n := by
  simp [valuesOf, List.filterMap_append]

/-- `key` spells every required option as an option of the same name. -/
theorem optionOf_key (mathlib : Bool) : ∀ r ∈ required mathlib, optionOf (key r.1) = r.1 := by
  cases mathlib <;> decide

/-- A required option's name determines its required value. -/
theorem required_name_inj (mathlib : Bool) :
    ∀ a ∈ required mathlib, ∀ b ∈ required mathlib, a.1 = b.1 → a = b := by
  cases mathlib <;> decide

/-- The required options are listed once each. -/
theorem required_nodup (mathlib : Bool) : (required mathlib).Nodup := by
  cases mathlib <;> decide

/-- Lean reads every value as itself. -/
theorem readsAs_self (v : OptionValue) : v.readsAs v = true := by
  cases v <;> simp [OptionValue.readsAs]

/-- The values that the entries `init` adds for the required options in `l` give option
`r.1`: its required value when `r` is among them, nothing otherwise. -/
theorem valuesOf_keyed (mathlib : Bool) (r : Name × OptionValue) (hr : r ∈ required mathlib)
    (l : List (Name × OptionValue)) (hl : ∀ q ∈ l, q ∈ required mathlib) (hnd : l.Nodup) :
    valuesOf ⟨l.map (fun q => (key q.1, q.2)), []⟩ r.1 = if r ∈ l then [r.2] else [] := by
  induction l with
  | nil => simp [valuesOf]
  | cons q qs ih =>
    have hq := hl q (by simp)
    have ih := ih (fun x hx => hl x (by simp [hx])) (List.nodup_cons.mp hnd).2
    have hnot : q ∉ qs := (List.nodup_cons.mp hnd).1
    simp only [valuesOf, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [optionOf_key mathlib q hq]
    by_cases hqr : q = r
    · subst hqr
      simp only [hnot, ↓reduceIte] at ih
      simp [ih]
    · have hname : q.1 ≠ r.1 := fun h => hqr (required_name_inj mathlib q hq r hr h)
      rw [ih]
      simp [hname, Ne.symm hqr]

/-- The values that the entries `init` adds for the required options satisfying `p` give a
required option: its required value when it satisfies `p`, and nothing otherwise. -/
theorem valuesOf_filter (mathlib : Bool) (p : Name × OptionValue → Bool)
    (r : Name × OptionValue) (hr : r ∈ required mathlib) :
    valuesOf ⟨((required mathlib).filter p).map fun q => (key q.1, q.2), []⟩ r.1 =
      if p r then [r.2] else [] := by
  have hnd : ((required mathlib).filter p).Nodup :=
    (required_nodup mathlib).sublist List.filter_sublist
  rw [valuesOf_keyed mathlib r hr _ (fun q hq => (List.mem_filter.mp hq).1) hnd]
  by_cases h : p r <;> simp [h, List.mem_filter, hr]

/-- The values the package entries give a required option: its required value when the
observation `lacks` it, and nothing otherwise. -/
theorem valuesOf_missing (o : Observation) (r : Name × OptionValue)
    (hr : r ∈ required o.mathlib) :
    valuesOf ⟨missing o, []⟩ r.1 = if o.lacks r then [r.2] else [] :=
  valuesOf_filter o.mathlib o.lacks r hr

/-- The values the entries of claimed target `t` give a required option: its required value when
`t` builds without it and the package does not receive it, and nothing otherwise. -/
theorem valuesOf_targetMissing (o : Observation) (t : Target) (r : Name × OptionValue)
    (hr : r ∈ required o.mathlib) :
    valuesOf ⟨targetMissing o t, []⟩ r.1 =
      if o.without t r && !o.lacks r then [r.2] else [] :=
  valuesOf_filter o.mathlib _ r hr

/-- The package receives no option that a claimed target's `-D` sets. -/
theorem lacks_argues (o : Observation) (r : Name × OptionValue) (h : o.lacks r = true)
    (t : Target) (ht : t ∈ o.targets) : t.argues r.1 = false := by
  simp only [Observation.lacks, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  simpa using h.2 t ht

/-- When some root target is excluded, the package receives no option. -/
theorem missing_unclaimed (o : Observation) (h : o.allClaimed = false) : missing o = [] := by
  simp [missing, Observation.lacks, h]

/-- No option the plan adds reaches a claimed target whose `-D` sets it: the package's entries
and `t`'s own name only options that no `-D` among `t`'s extra `lean` arguments sets. With
`run_plan_resolved`, which states that these are exactly the entries `t`'s options gain, the plan
never gives an option a second setting beside a `-D`. -/
theorem added_unargued (o : Observation) (t : Target) (ht : t ∈ o.targets) :
    ∀ e ∈ missing o ++ targetMissing o t, t.argues (optionOf e.1) = false := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    obtain ⟨hreq, hl⟩ := List.mem_filter.mp hr
    rw [optionOf_key o.mathlib r hreq]
    exact lacks_argues o r hl t ht
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    obtain ⟨hreq, hw⟩ := List.mem_filter.mp hr
    rw [optionOf_key o.mathlib r hreq]
    cases ha : t.argues r.1
    · rfl
    · simp [Observation.without, ha] at hw

/-! ## The plan, part by part -/

theorem guidanceEdits_entries (g : Guidance) (o : Observation) :
    (guidanceEdits g o).flatMap Edit.entries = [] := by
  unfold guidanceEdits
  split
  · rfl
  · cases g <;> rfl

theorem driver_not_mem_guidanceEdits (g : Guidance) (o : Observation) :
    Edit.driver ∉ guidanceEdits g o := by
  unfold guidanceEdits
  split
  · simp
  · cases g <;> simp

theorem manifest_not_mem_guidanceEdits (g : Guidance) (o : Observation) :
    Edit.manifest ∉ guidanceEdits g o := by
  unfold guidanceEdits
  split
  · simp
  · cases g <;> simp

theorem guidanceEdits_skillFiles (g : Guidance) (o : Observation) :
    (guidanceEdits g o).filterMap Edit.skillFile? =
      if o.guided then [] else match g with | .agentsMd => [] | .skill => [o.skillFile] := by
  unfold guidanceEdits
  split
  · rfl
  · cases g <;> rfl

theorem guidanceEdits_added (g : Guidance) (o : Observation) :
    (guidanceEdits g o).filterMap Edit.added? = [] := by
  unfold guidanceEdits
  split
  · rfl
  · cases g <;> rfl

theorem optionEdits_entries (o : Observation) :
    (optionEdits o).flatMap Edit.entries = missing o := by
  unfold optionEdits
  split <;> split <;> simp_all [Edit.entries]

theorem driver_not_mem_optionEdits (o : Observation) : Edit.driver ∉ optionEdits o := by
  unfold optionEdits
  split <;> split <;> simp

theorem manifest_not_mem_optionEdits (o : Observation) : Edit.manifest ∉ optionEdits o := by
  unfold optionEdits
  split <;> split <;> simp

theorem optionEdits_skillFiles (o : Observation) :
    (optionEdits o).filterMap Edit.skillFile? = [] := by
  unfold optionEdits
  split <;> split <;> simp [Edit.skillFile?]

theorem skills_added (paths : List String) :
    (paths.map Edit.skill).filterMap Edit.added? = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp he
  rfl

theorem globEdits_entries (o : Observation) : (globEdits o).flatMap Edit.entries = [] := by
  simp [globEdits, List.flatMap_map, Edit.entries]

theorem driver_not_mem_globEdits (o : Observation) : Edit.driver ∉ globEdits o := by
  simp [globEdits]

theorem manifest_not_mem_globEdits (o : Observation) : Edit.manifest ∉ globEdits o := by
  simp [globEdits]

theorem globEdits_skillFiles (o : Observation) :
    (globEdits o).filterMap Edit.skillFile? = [] := by
  simp [globEdits, List.filterMap_map, Function.comp_def, Edit.skillFile?]

theorem globEdits_added (o : Observation) : (globEdits o).filterMap Edit.added? = [] := by
  simp [globEdits, List.filterMap_map, Function.comp_def, Edit.added?]

/-- The plan's package entries: the missing ones. -/
theorem plan_entries (g : Guidance) (o : Observation) :
    (plan g o).flatMap Edit.entries = missing o := by
  simp only [plan, List.flatMap_append, guidanceEdits_entries, optionEdits_entries,
    globEdits_entries]
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [hd, Edit.entries, List.flatMap_map]

theorem plan_driver_mem (g : Guidance) (o : Observation) :
    Edit.driver ∈ plan g o ↔ o.driver = "" := by
  have h1 := driver_not_mem_guidanceEdits g o
  have h2 := driver_not_mem_optionEdits o
  have h3 := driver_not_mem_globEdits o
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [plan, hd, hf, h1, h2, h3]

theorem plan_manifest_mem (g : Guidance) (o : Observation) :
    Edit.manifest ∈ plan g o ↔ o.starter = true := by
  have h1 := manifest_not_mem_guidanceEdits g o
  have h2 := manifest_not_mem_optionEdits o
  have h3 := manifest_not_mem_globEdits o
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [plan, hd, hf, h1, h2, h3]

theorem plan_skillFiles (g : Guidance) (o : Observation) :
    (plan g o).filterMap Edit.skillFile? =
      (if o.guided then [] else match g with | .agentsMd => [] | .skill => [o.skillFile]) ++
        staleSkills o := by
  simp only [plan, List.filterMap_append, guidanceEdits_skillFiles, optionEdits_skillFiles,
    globEdits_skillFiles, List.filterMap_map, List.append_nil]
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [hd, Edit.skillFile?, Function.comp_def, List.filterMap_cons]

theorem plan_added (g : Guidance) (o : Observation) :
    (plan g o).filterMap Edit.added? = (optionEdits o).filterMap Edit.added? := by
  simp only [plan, List.filterMap_append, guidanceEdits_added, skills_added, globEdits_added,
    List.append_nil]
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [hd, Edit.added?, List.filterMap_cons]

/-- The libraries the plan gives a glob: those of `Observation.unglobbed`. -/
theorem plan_libraries (g : Guidance) (o : Observation) :
    (plan g o).filterMap Edit.library? = o.unglobbed.map (·.1) := by
  have hg : (guidanceEdits g o).filterMap Edit.library? = [] := by
    unfold guidanceEdits
    split
    · rfl
    · cases g <;> rfl
  have ho : (optionEdits o).filterMap Edit.library? = [] := by
    unfold optionEdits
    split <;> split <;> simp [Edit.library?]
  simp only [plan, List.filterMap_append, hg, ho, globEdits, List.filterMap_map]
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;>
    simp [hd, Edit.library?, Function.comp_def, List.filterMap_cons]

/-! ## Main theorems -/

/-- The package's options after the plan: its own, then its missing ones. -/
theorem run_plan_options (g : Guidance) (o : Observation) :
    (run o (plan g o)).options = o.options ++ missing o := by
  rw [run_options, plan_entries]

/-- When some root target is excluded, the plan leaves the package's options unchanged, so no
option reaches a target the manifest excludes. -/
theorem run_options_unclaimed (g : Guidance) (o : Observation) (h : o.allClaimed = false) :
    (run o (plan g o)).options = o.options := by
  rw [run_plan_options, missing_unclaimed o h, List.append_nil]

/-- The plan never changes or removes an option the package already gives. -/
theorem run_options_prefix (g : Guidance) (o : Observation) :
    o.options <+: (run o (plan g o)).options := by
  rw [run_plan_options]
  exact List.prefix_append _ _

/-- Claimed target `t` with the options the plan adds to it. -/
def withAdded (o : Observation) (t : Target) : Target :=
  { t with options := t.options ++ targetMissing o t }

/-- The plan keeps a claimed target's kind, name, extra `lean` arguments and every option it
already gives. -/
theorem withAdded_prefix (o : Observation) (t : Target) :
    (withAdded o t).exe = t.exe ∧ (withAdded o t).name = t.name ∧
      (withAdded o t).arguments = t.arguments ∧ t.options <+: (withAdded o t).options :=
  ⟨rfl, rfl, rfl, List.prefix_append _ _⟩

/-- A target the plan adds nothing to is unchanged. -/
theorem withAdded_eq_self (o : Observation) (t : Target) (h : targetMissing o t = []) :
    withAdded o t = t := by
  cases t
  simp [withAdded, h]

/-- The claimed targets after the plan: each with the options the plan adds to it. -/
theorem run_plan_targets (g : Guidance) (o : Observation) :
    (run o (plan g o)).targets = o.targets.map (withAdded o) := by
  rw [run_targets, plan_added]
  unfold optionEdits
  have hpkg : ((if missing o = [] then [] else [Edit.options (missing o)]) : List Edit).filterMap
      Edit.added? = [] := by
    split <;> rfl
  rw [List.filterMap_append, hpkg, List.nil_append]
  split
  · rename_i hall
    have hid : ∀ t ∈ o.targets, withAdded o t = t := fun t ht =>
      withAdded_eq_self o t (by simpa using List.all_eq_true.mp hall t ht)
    simp only [List.filterMap_nil, List.foldl_nil]
    exact ((List.map_congr_left hid).trans (List.map_id' _)).symm
  · simp only [List.filterMap_cons, Edit.added?, List.filterMap_nil, List.foldl_cons,
      List.foldl_nil, addTargets, List.zipWith_map_right, List.zipWith_self]
    rfl

/-- The options claimed target `t` builds with after the plan: the package's after the plan,
then its own after the plan. -/
theorem run_plan_resolved (g : Guidance) (o : Observation) (t : Target) :
    (run o (plan g o)).options ++ (withAdded o t).options =
      (o.options ++ missing o) ++ (t.options ++ targetMissing o t) := by
  rw [run_plan_options]
  rfl

/-- The values the options of claimed target `t` give option `n` after the plan: the package's,
its missing ones, `t`'s own, then those the plan adds to `t`. -/
theorem valuesOf_run (g : Guidance) (o : Observation) (t : Target) (n : Name) :
    valuesOf ⟨(run o (plan g o)).options ++ (withAdded o t).options, []⟩ n =
      (valuesOf ⟨o.options, []⟩ n ++ valuesOf ⟨missing o, []⟩ n) ++
        (valuesOf ⟨t.options, []⟩ n ++ valuesOf ⟨targetMissing o t, []⟩ n) := by
  rw [run_plan_resolved, valuesOf_append, valuesOf_append, valuesOf_append]

/-- A claimed target that built without a required option builds with exactly its required value
after the plan. -/
theorem valuesOf_withAdded (g : Guidance) (o : Observation) (t : Target)
    (r : Name × OptionValue) (hr : r ∈ required o.mathlib) (h : o.without t r = true) :
    valuesOf ⟨(run o (plan g o)).options ++ (withAdded o t).options, []⟩ r.1 = [r.2] := by
  have hnil : valuesOf ⟨o.options ++ t.options, []⟩ r.1 = [] := by
    simp only [Observation.without, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.1
  rw [valuesOf_append, List.append_eq_nil_iff] at hnil
  rw [valuesOf_run, hnil.1, hnil.2, valuesOf_missing o r hr, valuesOf_targetMissing o t r hr, h]
  cases o.lacks r <;> simp

/-- A claimed target that built without a required option builds with it after the plan, set to
its required value, as the RG2006 decision reads the options Lake resolves for the target: the
package's, then the target's own. -/
theorem run_sets (g : Guidance) (o : Observation) (t : Target) (ht : t ∈ o.targets)
    (r : Name × OptionValue) (hr : r ∈ required o.mathlib) (h : o.without t r = true) :
    withAdded o t ∈ (run o (plan g o)).targets ∧
      sets ⟨(run o (plan g o)).options ++ (withAdded o t).options, []⟩ r.1 r.2 = true := by
  refine ⟨?_, ?_⟩
  · rw [run_plan_targets]
    exact List.mem_map_of_mem ht
  · simp [sets, valuesOf_withAdded g o t r hr h, readsAs_self]

/-- After the plan, every claimed target builds with a value for every required option, or a `-D`
among its extra `lean` arguments sets the option. -/
theorem resolved_run (g : Guidance) (o : Observation) (t' : Target)
    (ht' : t' ∈ (run o (plan g o)).targets) (r : Name × OptionValue)
    (hr : r ∈ required o.mathlib) :
    valuesOf ⟨(run o (plan g o)).options ++ t'.options, []⟩ r.1 ≠ [] ∨ t'.argues r.1 = true := by
  rw [run_plan_targets, List.mem_map] at ht'
  obtain ⟨t, -, rfl⟩ := ht'
  cases ha : t.argues r.1
  · by_cases hv : valuesOf ⟨o.options ++ t.options, []⟩ r.1 = []
    · have hw : o.without t r = true := by simp [Observation.without, hv, ha]
      left
      rw [valuesOf_withAdded g o t r hr hw]
      simp
    · left
      intro hnil
      apply hv
      rw [valuesOf_run, List.append_eq_nil_iff, List.append_eq_nil_iff,
        List.append_eq_nil_iff] at hnil
      rw [valuesOf_append, hnil.1.1, hnil.2.1, List.append_nil]
  · right
    exact ha

/-- After the plan, no claimed target builds without a required option. -/
theorem without_run (g : Guidance) (o : Observation) (t' : Target)
    (ht' : t' ∈ (run o (plan g o)).targets) (r : Name × OptionValue)
    (hr : r ∈ required o.mathlib) : (run o (plan g o)).without t' r = false := by
  rcases resolved_run g o t' ht' r hr with h | h
  · have he : (valuesOf ⟨(run o (plan g o)).options ++ t'.options, []⟩ r.1).isEmpty = false :=
      Bool.eq_false_iff.mpr fun he => h (List.isEmpty_iff.mp he)
    simp [Observation.without, he]
  · simp [Observation.without, h]

/-- After the plan, no required option is missing from the package. -/
theorem missing_run (g : Guidance) (o : Observation) : missing (run o (plan g o)) = [] := by
  unfold missing
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro r hr h
  rw [run_mathlib] at hr
  simp only [Observation.lacks, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨-, t', ht', hw⟩, -⟩ := h
  rw [without_run g o t' ht' r hr] at hw
  exact Bool.noConfusion hw

/-- After the plan, no claimed target is missing a required option. -/
theorem targetMissing_run (g : Guidance) (o : Observation) :
    ∀ t' ∈ (run o (plan g o)).targets, targetMissing (run o (plan g o)) t' = [] := by
  intro t' ht'
  unfold targetMissing
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro r hr
  rw [run_mathlib] at hr
  simp [without_run g o t' ht' r hr]

/-- After the plan, no option edit is left. -/
theorem optionEdits_run (g : Guidance) (o : Observation) :
    optionEdits (run o (plan g o)) = [] := by
  unfold optionEdits
  simp only [missing_run g o, ↓reduceIte, List.nil_append, ite_eq_left_iff]
  intro h
  exact absurd (List.all_eq_true.mpr fun t' ht' => by simp [targetMissing_run g o t' ht']) h

/-- Whether a claimed target sets a required option only with a `-D` is the same after the plan:
the plan gives such a target no value for the option. -/
theorem onlyArgued_run (g : Guidance) (o : Observation) (t : Target) (ht : t ∈ o.targets)
    (r : Name × OptionValue) (hr : r ∈ required o.mathlib) :
    (run o (plan g o)).onlyArgued (withAdded o t) r = o.onlyArgued t r := by
  change ((valuesOf ⟨(run o (plan g o)).options ++ (withAdded o t).options, []⟩ r.1).isEmpty &&
      t.argues r.1) = ((valuesOf ⟨o.options ++ t.options, []⟩ r.1).isEmpty && t.argues r.1)
  cases ha : t.argues r.1
  · simp
  · have hl : o.lacks r = false := by
      cases hl : o.lacks r
      · rfl
      · rw [lacks_argues o r hl t ht] at ha
        exact Bool.noConfusion ha
    have hw : o.without t r = false := by simp [Observation.without, ha]
    rw [valuesOf_run, valuesOf_missing o r hr, valuesOf_targetMissing o t r hr, hl, hw,
      valuesOf_append]
    simp

/-- The plan leaves the required options each claimed target sets only with a `-D` as they were:
it adds none of them to that target. `init` checks this target by target after writing. -/
theorem arguedBy_run (g : Guidance) (o : Observation) (t : Target) (ht : t ∈ o.targets) :
    (run o (plan g o)).arguedBy (withAdded o t) = o.arguedBy t := by
  unfold Observation.arguedBy
  rw [run_mathlib]
  exact List.filter_congr fun r hr => onlyArgued_run g o t ht r hr

/-- The plan leaves the required options that claimed targets set only with a `-D` as they
were: it adds none of them. -/
theorem argued_run (g : Guidance) (o : Observation) : argued (run o (plan g o)) = argued o := by
  unfold argued
  rw [run_mathlib, run_plan_targets]
  congr 1
  apply List.filter_congr
  intro r hr
  rw [List.any_map, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  show (run o (plan g o)).onlyArgued (withAdded o t) r = true ↔ o.onlyArgued t r = true
  rw [onlyArgued_run g o t ht r hr]

/-- After the plan, every skill file equals the installed skill. -/
theorem staleSkills_run (g : Guidance) (o : Observation) :
    staleSkills (run o (plan g o)) = [] := by
  unfold staleSkills
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff, run_skills, plan_skillFiles]
  intro s hs
  rcases mem_markAll hs with ⟨hmem, hnot⟩ | ht
  · cases hs2 : s.2
    · exfalso
      apply hnot
      refine List.mem_append_right _ ?_
      simp only [staleSkills, List.mem_map, List.mem_filter]
      exact ⟨s, ⟨hmem, by simp [hs2]⟩, rfl⟩
    · simp
  · simp [ht]

/-- The project has agent guidance after the plan. -/
theorem guided_run (g : Guidance) (o : Observation) : (run o (plan g o)).guided = true := by
  unfold Observation.guided
  rw [run_agentsSection, run_skills, plan_skillFiles]
  by_cases hg : o.guided = true
  · rcases Bool.or_eq_true_iff.mp hg with h | h
    · simp [h]
    · have hne : o.skills ≠ [] := by simpa using h
      have := markAll_ne_nil (skills := o.skills)
        ((if o.guided then [] else match g with | .agentsMd => [] | .skill => [o.skillFile]) ++
          staleSkills o) (.inl hne)
      simp [this]
  · have hg' : o.guided = false := by simpa using hg
    cases g
    · have hmem : (plan .agentsMd o).any Edit.writesSection = true := by
        simp [plan, guidanceEdits, hg', Edit.writesSection]
      simp [hmem]
    · have := markAll_ne_nil (skills := o.skills) (o.skillFile :: staleSkills o) (.inr (by simp))
      simp [hg', this]

/-- The driver after the plan: Regula's when the package set none, otherwise unchanged. -/
theorem run_plan_driver (g : Guidance) (o : Observation) :
    (run o (plan g o)).driver = if o.driver = "" then lintDriver else o.driver := by
  rw [run_driver]
  by_cases hd : o.driver = ""
  · have h : Edit.driver ∈ plan g o := (plan_driver_mem g o).mpr hd
    simp [h, hd]
  · have h : Edit.driver ∉ plan g o := fun h => hd ((plan_driver_mem g o).mp h)
    simp [h, hd]

/-- The driver after the plan is set. -/
theorem driver_run (g : Guidance) (o : Observation) : (run o (plan g o)).driver ≠ "" := by
  rw [run_plan_driver]
  split
  · simp [lintDriver]
  · assumption

/-- After the plan, no starter manifest is left to write: the manifest exists, or the package has
no library for it to claim. -/
theorem starter_run (g : Guidance) (o : Observation) : (run o (plan g o)).starter = false := by
  unfold Observation.starter
  rw [run_manifest, run_libraries]
  cases hs : o.starter
  · have h : Edit.manifest ∉ plan g o := fun h => by
      rw [(plan_manifest_mem g o).mp h] at hs
      exact Bool.noConfusion hs
    simpa [h, Observation.starter] using hs
  · have h : Edit.manifest ∈ plan g o := (plan_manifest_mem g o).mpr hs
    simp [h]

/-- The facts after the plan are the facts with each library of `Coverage.globbing` given its
glob: the state the decision assumed when it chose them. -/
theorem coverage_run (g : Guidance) (o : Observation) :
    (run o (plan g o)).coverage = o.coverage.globAll o.coverage.globbing := by
  rw [run_coverage, plan_libraries, Coverage.foldl_glob]
  simp only [Coverage.globAll]
  congr 1
  apply List.map_congr_left
  intro l hl
  cases hg : l.globbed
  · have key : ((o.unglobbed.map (·.1)).contains l.name) = o.coverage.globbing.contains l.name := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      simp only [Observation.unglobbed, List.map_map, List.mem_map, List.mem_filter,
        Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem]
      constructor
      · rintro ⟨k, ⟨-, -, hk⟩, he⟩
        rwa [← he]
      · intro h
        exact ⟨l, ⟨hl, hg, h⟩, rfl⟩
    simp only [Library.globIn, key]
  · simp [Library.globIn, Library.glob, hg]

/-- After the plan, no library needs a glob. -/
theorem unglobbed_run (g : Guidance) (o : Observation) : (run o (plan g o)).unglobbed = [] := by
  simp only [Observation.unglobbed, coverage_run, Coverage.globbing_globAll]
  simp

/-- The plan leaves the modules that libraries with `globs` of their own leave out as they were
(`Observation.uncovered` already counts them with the plan's globs written). -/
theorem uncovered_run (g : Guidance) (o : Observation) :
    (run o (plan g o)).uncovered = o.uncovered := by
  simp only [Observation.uncovered, coverage_run, Coverage.globbing_globAll,
    Coverage.witnesses_globAll, Coverage.globAll_libraries, List.filter_map, List.map_map]
  simp only [Function.comp_def, Coverage.uncoveredIn_globAll, Library.globIn_name,
    Library.globIn_roots]

/-- After `init` applies its plan, the plan of the result is empty: a second run writes
nothing. -/
theorem plan_idempotent (g : Guidance) (o : Observation) : plan g (run o (plan g o)) = [] := by
  have h1 := driver_run g o
  have h2 := optionEdits_run g o
  have h3 := starter_run g o
  have h4 := guided_run g o
  have h5 := staleSkills_run g o
  have h6 := unglobbed_run g o
  generalize run o (plan g o) = r at h1 h2 h3 h4 h5 h6
  simp [plan, guidanceEdits, globEdits, h1, h2, h3, h4, h5, h6]

theorem guidanceEdits_eq_nil_iff (g : Guidance) (o : Observation) :
    guidanceEdits g o = [] ↔ o.guided = true := by
  unfold guidanceEdits
  cases o.guided <;> cases g <;> simp

/-- The conditions under which nothing is left for `init` to write. -/
def Settled (o : Observation) : Prop :=
  o.driver ≠ "" ∧ optionEdits o = [] ∧ o.starter = false ∧ o.guided = true ∧
    staleSkills o = [] ∧ o.unglobbed = []

/-- The plan is empty exactly when the observation is settled. -/
theorem plan_eq_nil_iff_settled (g : Guidance) (o : Observation) :
    plan g o = [] ↔ Settled o := by
  unfold plan Settled globEdits
  rw [← guidanceEdits_eq_nil_iff g o]
  by_cases hd : o.driver = "" <;> cases hf : o.starter <;> simp_all

/-- Every option issue is one `init` writes a fix for. -/
theorem optionIssues_fixable (o : Observation) : ∀ i ∈ optionIssues o, i.fixable = true := by
  intro i hi
  unfold optionIssues at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · simp at hi
    · rw [List.mem_singleton] at hi
      rw [hi]
      rfl
  · obtain ⟨t, -, ht⟩ := List.mem_filterMap.mp hi
    split at ht
    · simp at ht
    · rw [← Option.some.inj ht]
      rfl

/-- The issue of the options set only with a `-D` is not one `init` writes a fix for. -/
theorem arguedIssues_unfixable (o : Observation) : ∀ i ∈ arguedIssues o, i.fixable = false := by
  intro i hi
  unfold arguedIssues at hi
  split at hi
  · simp at hi
  · rw [List.mem_singleton] at hi
    rw [hi]
    rfl

/-- No option issue is left exactly when no option edit is. -/
theorem optionIssues_eq_nil_iff (o : Observation) : optionIssues o = [] ↔ optionEdits o = [] := by
  unfold optionIssues optionEdits
  have hf : ∀ t : Target, ((if targetMissing o t = [] then none
      else some (Issue.targetOptionsMissing t.exe t.name (targetMissing o t))) = none) ↔
        targetMissing o t = [] := by
    intro t
    split <;> simp_all
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  simp only [hf]
  apply and_congr
  · split <;> simp
  · split <;> simp_all

/-- No fixable issue is left exactly when the observation is settled. -/
theorem issues_unfixable_iff_settled (o : Observation) :
    (∀ i ∈ issues o, i.fixable = false) ↔ Settled o := by
  constructor
  · intro h
    refine ⟨fun hd => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h .driverUnset (by simp [issues, driverIssues, hd])
      exact Bool.noConfusion this
    · rw [← optionIssues_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
      intro i hi
      have h1 := h i (by simp [issues, hi])
      rw [optionIssues_fixable o i hi] at h1
      exact Bool.noConfusion h1
    · cases hm : o.starter
      · rfl
      · have := h .manifestMissing (by simp [issues, hm])
        exact Bool.noConfusion this
    · cases hg : o.guided
      · have := h (.guidanceMissing o.agentsFile o.skillFile) (by simp [issues, hg])
        exact Bool.noConfusion this
      · rfl
    · rw [List.eq_nil_iff_forall_not_mem]
      intro p hp
      have := h (.skillStale p) (by simp [issues, hp])
      exact Bool.noConfusion this
    · rw [List.eq_nil_iff_forall_not_mem]
      intro e he
      have := h (unglobbedIssue e) (by
        unfold issues
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he)))
      exact Bool.noConfusion this
  · rintro ⟨hd, hm, hf, hg, hs, hu⟩ i hi
    have hopt : optionIssues o = [] := (optionIssues_eq_nil_iff o).mpr hm
    have hdrv : ∀ j ∈ driverIssues o, j.fixable = false := by
      intro j hj
      unfold driverIssues at hj
      simp only [hd, ↓reduceIte] at hj
      split at hj
      · simp at hj
      · rw [List.mem_singleton] at hj
        rw [hj]
        rfl
    have hlib : ∀ j ∈ (if o.libraries then [] else [Issue.noLibrary]), j.fixable = false := by
      intro j hj
      split at hj
      · simp at hj
      · rw [List.mem_singleton] at hj
        rw [hj]
        rfl
    have htc := toolchainIssues_unfixable o
    have hun : ∀ j ∈ o.uncovered.map uncoveredIssue, j.fixable = false := by
      intro j hj
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hj
      rfl
    simp only [issues, hopt, hf, hg, hs, hu, Bool.false_eq_true, ↓reduceIte, List.map_nil,
      List.append_nil, List.mem_append] at hi
    rcases hi with (((hi | hi) | hi) | hi) | hi
    · exact hdrv i hi
    · exact arguedIssues_unfixable o i hi
    · exact hlib i hi
    · exact htc i hi
    · exact hun i hi

/-- The plan is empty exactly when every setup issue is one `init` does not write. -/
theorem plan_eq_nil_iff (g : Guidance) (o : Observation) :
    plan g o = [] ↔ ∀ i ∈ issues o, i.fixable = false :=
  (plan_eq_nil_iff_settled g o).trans (issues_unfixable_iff_settled o).symm

/-- Applying the plan removes exactly the issues `init` writes a fix for and adds none. -/
theorem issues_run (g : Guidance) (o : Observation) :
    issues (run o (plan g o)) = (issues o).filter (!·.fixable) := by
  have h1 := run_plan_driver g o
  have h2 : optionIssues (run o (plan g o)) = [] :=
    (optionIssues_eq_nil_iff _).mpr (optionEdits_run g o)
  have h3 := starter_run g o
  have h4 := guided_run g o
  have h5 := staleSkills_run g o
  have h7 := unglobbed_run g o
  have h8 := uncovered_run g o
  have h6 : toolchainIssues (run o (plan g o)) = toolchainIssues o := by
    unfold toolchainIssues
    rw [run_toolchain o (plan g o)]
  have h9 := run_libraries o (plan g o)
  have h10 : arguedIssues (run o (plan g o)) = arguedIssues o := by
    unfold arguedIssues
    rw [argued_run]
  have hu : (o.uncovered.map uncoveredIssue).filter (!·.fixable) =
      o.uncovered.map uncoveredIssue := by
    rw [List.filter_eq_self]
    intro j hj
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hj
    rfl
  have hs : ((staleSkills o).map Issue.skillStale).filter (!·.fixable) = [] := by
    induction staleSkills o <;> simp_all [Issue.fixable]
  have ht : (toolchainIssues o).filter (!·.fixable) = toolchainIssues o := by
    rw [List.filter_eq_self]
    intro i hi
    simp [toolchainIssues_unfixable o i hi]
  have hopt : (optionIssues o).filter (!·.fixable) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    simp [optionIssues_fixable o i hi]
  have ha : (arguedIssues o).filter (!·.fixable) = arguedIssues o := by
    rw [List.filter_eq_self]
    intro i hi
    simp [arguedIssues_unfixable o i hi]
  have hl : (if o.libraries = true then [] else [Issue.noLibrary]).filter (!·.fixable) =
      if o.libraries = true then [] else [Issue.noLibrary] := by
    split <;> rfl
  have hug : (o.unglobbed.map unglobbedIssue).filter (!·.fixable) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hj
    simp [unglobbedIssue, Issue.fixable]
  generalize run o (plan g o) = r at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [issues, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte,
    List.map_nil, List.append_nil, List.filter_append, hs, ht, hu, hl, hopt, ha, hug]
  have hf : (if o.starter = true then [Issue.manifestMissing] else []).filter
      (!·.fixable) = [] := by split <;> rfl
  have hg : (if o.guided = true then []
      else [Issue.guidanceMissing o.agentsFile o.skillFile]).filter (!·.fixable) = [] := by
    split <;> rfl
  rw [hf, hg]
  unfold driverIssues
  rw [h1]
  by_cases hd : o.driver = ""
  · simp [hd, lintDriver, Issue.fixable]
  · by_cases hl : o.driver = lintDriver
    · simp [hl, lintDriver]
    · simp [hd, hl, Issue.fixable]

/-! ## Finding text

`doctor` prints each issue as the linter prints a finding: what is wrong and where on the first
line, the modules it names on indented lines (at most `shownModules` of them, wrapped, and the
count of the rest), then the fix. -/

/-- The two Lake configuration formats. -/
inductive Lakefile where
  /-- `lakefile.lean`. -/
  | lean
  /-- `lakefile.toml`. -/
  | toml
  deriving DecidableEq, Repr

/-- The configuration file's name. -/
def Lakefile.name : Lakefile → String
  | .lean => "lakefile.lean"
  | .toml => "lakefile.toml"

/-- An option value as a TOML value. -/
def tomlValue : OptionValue → String
  | .string s => s.quote
  | .bool b => toString b
  | .nat n => toString n

/-- An option value as a `lakefile.lean` `LeanOptionValue`. -/
def leanValue : OptionValue → String
  | .string s => ".ofString " ++ s.quote
  | .bool b => toString b
  | .nat n => ".ofNat " ++ toString n

/-- One `leanOptions` entry as written in each format. -/
def Lakefile.entry : Lakefile → Name × OptionValue → String
  | .toml, (n, v) => toString n ++ " = " ++ tomlValue v
  | .lean, (n, v) => "⟨`" ++ toString n ++ ", " ++ leanValue v ++ "⟩"

/-- The lint-driver setting as written in each format. -/
def Lakefile.driverSetting : Lakefile → String
  | .lean => "`lintDriver := \"" ++ lintDriver ++ "\"` in the `package` declaration"
  | .toml => "`lintDriver = \"" ++ lintDriver ++ "\"` at the top level"

/-- The `name` a `lakefile.toml` table writes for the target Lake names `name`: Lake's
`Name.toString` escapes a name that is not an identifier (`«my-tool»` for `name = "my-tool"`). -/
def tomlName (name : String) : String :=
  match name.toName with
  | .anonymous => name
  | n => n.toString (escape := false)

/-- The `globs` setting that makes a library with roots `rs` include every module below them, as
each format writes it: the text `doctor` asks for and `init` writes. -/
def Lakefile.globsSetting : Lakefile → List String → String
  | .toml, rs => "globs = [" ++
      ", ".intercalate (rs.flatMap fun r => [r.quote, (r ++ ".+").quote]) ++ "]"
  | .lean, rs => "globs := #[" ++ ", ".intercalate (rs.map fun r => ".andSubmodules `" ++ r) ++ "]"

/-- `globsSetting` as a code span: the `lakefile.lean` setting contains a backtick, so it takes
two. -/
def Lakefile.globsCode (f : Lakefile) (rs : List String) : String :=
  let fence := match f with | .toml => "`" | .lean => "``"
  fence ++ f.globsSetting rs ++ fence

/-- Where options go in each format. -/
def Lakefile.optionsPlace : Lakefile → String
  | .lean => "the `package` declaration's `leanOptions`"
  | .toml => "the `[leanOptions]` table"

/-- A root target as each format declares it, `exe` for a `lean_exe` and otherwise a `lean_lib`. -/
def Lakefile.target (f : Lakefile) (exe : Bool) (name : String) : String :=
  let kind := if exe then "lean_exe" else "lean_lib"
  match f with
  | .toml => "the `[[" ++ kind ++ "]]` table named \"" ++ tomlName name ++ "\""
  | .lean => "`" ++ kind ++ " " ++ name ++ "`"

/-- The phrase that adds the glob of library `l` with roots `rs` (`globsSetting`). -/
def Lakefile.globs (f : Lakefile) (l : String) (rs : List String) : String :=
  "add " ++ f.globsCode rs ++ " to " ++ f.target false l

/-- A library as each format declares it. -/
def Lakefile.library : Lakefile → String
  | .lean => "`lean_lib` declaration"
  | .toml => "`[[lean_lib]]` table"

/-- `it` for one module, `them` for several. -/
private def pronoun (modules : List String) : String :=
  if modules.length == 1 then "it" else "them"

/-- `1 module` or `N modules`. -/
private def moduleCount (modules : List String) : String :=
  toString modules.length ++ if modules.length == 1 then " module" else " modules"

/-- The most module names one finding prints; it counts the rest, which the glob in its fix
includes with them. -/
def shownModules : Nat := 12

/-- The names a finding prints of `modules`, in order, and how many more it only counts. -/
def moduleSummary (modules : List String) : List String × Nat :=
  (modules.take shownModules, modules.length - shownModules)

/-- `moduleSummary` accounts for every module: its names are a prefix of them and its count is
exactly the rest. -/
theorem moduleSummary_complete (modules : List String) :
    (moduleSummary modules).1 ++ modules.drop shownModules = modules ∧
      (moduleSummary modules).1.length + (moduleSummary modules).2 = modules.length := by
  refine ⟨List.take_append_drop _ _, ?_⟩
  simp only [moduleSummary, List.length_take]
  omega

/-- `words` in order, greedily grouped into lines: a word joins the current line `line`, whose
`", "`-joined text is taken to be `used` characters long, when the joined text stays within
`width` characters, and otherwise starts a new line. `wrapFrom_flatten` proves that no word is
lost or reordered; the width is layout, not a proved bound. -/
def wrapFrom (width : Nat) (line : List String) (used : Nat) : List String → List (List String)
  | [] => if line.isEmpty then [] else [line]
  | w :: ws =>
    if line.isEmpty then wrapFrom width [w] w.length ws
    else if used + 2 + w.length ≤ width then wrapFrom width (line ++ [w]) (used + 2 + w.length) ws
    else line :: wrapFrom width [w] w.length ws

/-- Wrapping keeps every word, in order: the lines concatenate to the words. -/
theorem wrapFrom_flatten (width : Nat) :
    ∀ (words line : List String) (used : Nat),
      (wrapFrom width line used words).flatten = line ++ words
  | [], line, used => by cases line <;> simp [wrapFrom]
  | w :: ws, line, used => by
    by_cases h : line.isEmpty = true
    · simp [wrapFrom, List.isEmpty_iff.mp h, wrapFrom_flatten width ws [w] w.length]
    · by_cases hw : used + 2 + w.length ≤ width
      · simp [wrapFrom, h, hw, wrapFrom_flatten width ws (line ++ [w]) (used + 2 + w.length)]
      · simp [wrapFrom, h, hw, wrapFrom_flatten width ws [w] w.length]

/-- The indented lines naming `modules`: the names `moduleSummary` prints, grouped by `wrapFrom`
at 96 characters after a four-space indent, then how many more there are. -/
def moduleLines (modules : List String) : String :=
  let (shown, more) := moduleSummary modules
  "\n".intercalate (((wrapFrom 96 [] 0 shown).map fun line => "    " ++ ", ".intercalate line) ++
    if more == 0 then [] else ["    and " ++ toString more ++ " more"])

/-- The first line of an issue's finding, `setup [FILE]: what is wrong`, followed for a library
that leaves out modules by the `moduleLines` naming them. -/
def Issue.message (f : Lakefile) : Issue → String
  | .driverUnset => "setup [" ++ f.name ++ "]: `lintDriver` is not set, so `lake lint` does \
      not run Regula"
  | .driverOther d => "setup [" ++ f.name ++ "]: `lintDriver` is \"" ++ d ++ "\", so `lake lint` \
      runs that driver and not Regula"
  | .optionsMissing es => "setup [" ++ f.name ++ "]: a target builds without " ++
      ", ".intercalate (es.map fun e => "`" ++ toString (optionOf e.1) ++ "`") ++
      ", which the package's `leanOptions` do not set"
  | .targetOptionsMissing exe n es => "setup [" ++ f.name ++ "]: claimed " ++
      (if exe then "lean_exe" else "lean_lib") ++ " `" ++ n ++ "` builds without " ++
      ", ".intercalate (es.map fun e => "`" ++ toString (optionOf e.1) ++ "`") ++
      ", which neither the package's nor its own `leanOptions` set"
  | .argued es => "setup [" ++ f.name ++ "]: a `-D` among the extra `lean` arguments \
      (`weakLeanArgs`, `moreLeanArgs`) of one or more claimed targets sets " ++
      ", ".intercalate (es.map fun e => "`" ++ toString (optionOf e.1) ++ "`") ++
      ", which its `leanOptions` do not; RG2006 requires " ++
      (if es.length == 1 then "it" else "them") ++ " in `leanOptions`, and `init` adds no second \
      setting beside a `-D`"
  | .manifestMissing => "setup [foundation_manifest.json]: the file does not exist, so `lake lint` \
      has no claimed surface"
  | .noLibrary => "setup [" ++ f.name ++ "]: the package has no `lean_lib`, so a foundation \
      manifest has no surface to claim: Regula claims each surface per library, an executable \
      belonging to a library's surface"
  | .guidanceMissing a s => "setup [" ++ a ++ "]: no agent guidance: " ++ a ++ " has no `" ++
      agentsHeading ++ "` section and there is no " ++ s
  | .skillStale p => "setup [" ++ p ++ "]: the skill is not the installed Regula's briefing"
  | .toolchain s v c => "setup [lean-toolchain]: the project's lean-toolchain, " ++ s ++
      ", selects Lean " ++ v ++ " (" ++ c ++ "), but this Regula revision supports" ++
      " only Lean " ++ RegulaPolicy.Compiler.version ++ " (" ++ RegulaPolicy.Compiler.commit ++
      ")"
  | .toolchainUnresolved s r => "setup [lean-toolchain]: " ++
      (if s.isEmpty then "the project's lean-toolchain names no toolchain"
        else "the project's lean-toolchain, " ++ s ++
          ", selects no installed compiler that reports its identity") ++
      ", so its compiler cannot be compared with the Lean " ++ RegulaPolicy.Compiler.version ++
      " (" ++ RegulaPolicy.Compiler.commit ++ ") this Regula revision supports: " ++ r
  | .uncovered l _ ms | .unglobbed l _ ms => "setup [" ++ f.name ++ "]: lean_lib `" ++ l ++
      "` does not include " ++ moduleCount ms ++ " below its roots, but a claimed module \
      imports " ++ pronoun ms ++ ", so `lake lint` finds " ++ pronoun ms ++ " outside every \
      library and fails:\n" ++ moduleLines ms

/-- The fix line of an issue's finding. -/
def Issue.fix (f : Lakefile) : Issue → String
  | .driverUnset => "  fix: set " ++ f.driverSetting ++ ", or run `lake exe regula init`"
  | .driverOther _ => "  fix: Lake runs one lint driver per package: keep it and run Regula as \
      its own step with `lake exe lint`, or set lintDriver to \"" ++ lintDriver ++ "\" and run \
      the other driver as its own command (init never replaces a driver)"
  | .optionsMissing es => "  fix: add " ++
      ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " to " ++ f.optionsPlace ++
      ", or run `lake exe regula init`"
  | .targetOptionsMissing exe n es => "  fix: add " ++
      ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " to the `leanOptions` of " ++
      f.target exe n ++ " (the package's would also reach a target the manifest excludes or \
      one whose `-D` sets them), or run `lake exe regula init`"
  | .argued es => "  fix: set " ++
      ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " in `leanOptions` instead, \
      as RG2006 states for each claimed target, and remove the `-D` (`init` adds no option to a \
      target whose `-D` sets it)"
  | .manifestMissing => "  fix: run `lake exe regula init`, which writes a starter claiming every \
      `lean_lib` as `standard-logical`; then review each claim and rationale"
  | .noLibrary => "  fix: add a " ++ f.library ++ " for the modules your executables import, \
      then run `lake exe regula init`, which writes a starter manifest claiming it with every \
      `lean_exe`"
  | .guidanceMissing a s => "  fix: run `lake exe regula init` (adds the section to " ++ a ++
      ") or `lake exe regula init --skill` (writes " ++ s ++ ")"
  | .skillStale _ => "  fix: run `lake exe regula init`, which replaces it with the installed \
      briefing (for example after `lake update regula`); init owns this file and keeps no local \
      edits"
  | .toolchain _ _ _ => "  fix: move the project, and Mathlib if it uses it, to a toolchain that \
      selects the supported compiler (set lean-toolchain and run `lake update`), or \
      require a Regula revision qualified for your exact compiler (the adoption guide's \
      compatibility table lists each release's toolchain); unsupported versions require a \
      deliberate port; a toolchain override does not change what the project pins"
  | .toolchainUnresolved _ _ => "  fix: install or link the supported compiler, then set \
      lean-toolchain to its exact installed name; `doctor` resolves the pin among the \
      toolchains `elan toolchain list` names and installs nothing"
  | .uncovered l rs ms => "  fix: include " ++ pronoun ms ++ " in the `globs` of " ++
      f.target false l ++ ", for example with " ++ f.globsCode rs ++ ", or remove the " ++
      (if ms.length == 1 then "import" else "imports") ++ " (`init` never changes the `globs` a \
      library sets)"
  | .unglobbed l rs ms => "  fix: " ++ f.globs l rs ++ ", or run `lake exe regula init`, which \
      adds it because the library sets no `globs`, or remove the " ++
      (if ms.length == 1 then "import" else "imports")

/-- The note `doctor` prints, without failing, for one library entry of
`Observation.unimported`: what the library leaves out, then both remedies. -/
def unimportedNote (f : Lakefile) (entry : String × List String × List String) : String :=
  let p := pronoun entry.2.2
  "note [" ++ f.name ++ "]: lean_lib `" ++ entry.1 ++ "` does not include " ++
    moduleCount entry.2.2 ++ " below its roots and no claimed module imports " ++ p ++
    ", so `lake lint` does not audit " ++ p ++ ":\n" ++ moduleLines entry.2.2 ++ "\n" ++
  "  either " ++ f.globs entry.1 entry.2.1 ++ " to audit " ++ p ++ ", or leave " ++ p ++
    " out deliberately"

/-- What an edit writes, as a phrase `init` and `doctor` print after "wrote" or "would write". -/
def Edit.summary (f : Lakefile) : Edit → String
  | .driver => f.driverSetting ++ " in " ++ f.name
  | .options es => ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " in " ++
      f.optionsPlace ++ " of " ++ f.name
  | .targetOptions added => "; ".intercalate ((added.filter (!·.options.isEmpty)).map fun t =>
      ", ".intercalate (t.options.map fun e => "`" ++ f.entry e ++ "`") ++ " in the `leanOptions` \
        of " ++ f.target t.exe t.name) ++ " of " ++ f.name
  | .manifest => "a starter foundation_manifest.json (review each claim and rationale)"
  | .agentsSection a => "the `" ++ agentsHeading ++ "` section in " ++ a
  | .skill p => p ++ ", the installed Regula's skill"
  | .globs l rs => f.globsCode rs ++ " in " ++ f.target false l ++ " of " ++ f.name ++
      ", so the library includes every module below its roots"

end Regula.Setup
