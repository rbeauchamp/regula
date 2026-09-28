import RegulaPolicy.Community

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
- `Settled`, `plan_eq_nil_iff_settled`, `issues_unfixable_iff_settled`, `plan_eq_nil_iff`: the plan
  is empty exactly when no fixable issue remains.
- `issues_run`: applying the plan removes exactly the fixable issues and adds none.
- `Observation.lacks`, `missing`: the options `init` adds, those neither the package nor some
  target gives a value.
- `run_sets`, `resolved_run`: after the plan, a target that built without a required option builds
  with its required value (`RegulaPolicy.Community.sets`, the RG2006 decision), and every root
  target has a value for every required option.
- `run_options_prefix`: the plan never changes or removes an option the package already sets.
- `Issue.message`, `Issue.fix`, `Edit.summary`: the text `doctor` and `init` print.

## Boundaries

The observation is supplied by the operational `regula` command: Lake's loaded root package
(its `lintDriver` and package-level `leanOptions`), whether the workspace contains Mathlib,
whether `foundation_manifest.json` and the agent guidance exist, whether each skill file equals
the installed skill, and the project's and the required Regula's `lean-toolchain`. The command writes each edit into the lakefile, the manifest and the
guidance files, then observes the project again and refuses unless the new plan is empty; that
the file edits realize `apply` is that runtime check, not a theorem. RG2006 itself is decided per
claimed target over Lake's resolved options by `RegulaPolicy.Community.failures`; `init` writes
package-level options only and never changes a value the package or a target already gives. -/

namespace Regula.Setup

open Lean (Name)
open RegulaPolicy.Community (OptionValue BuildOptions required baseline mathlibBaseline valuesOf
  sets optionOf)

/-- The `lintDriver` value that makes `lake lint` run Regula. -/
def lintDriver : String := "regula/lint"

/-- Where `init` writes agent guidance when the project has none. -/
inductive Guidance where
  /-- A short section in `AGENTS.md` that tells the agent to run `lake exe regula agent-guide`;
  it names no version, so it never goes stale. -/
  | agentsMd
  /-- The installed briefing as an Agent Skills `SKILL.md` at `skillPath`, which `init` rewrites
  whenever it differs from the installed Regula's. -/
  | skill
  deriving DecidableEq, Repr

/-- The skill file `init --skill` writes. -/
def skillPath : String := ".agents/skills/regula/SKILL.md"

/-- The skill files `init` and `doctor` recognize, relative to the project root. -/
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

/-- What `init` and `doctor` observe of a project. -/
structure Observation where
  /-- The root package's `lintDriver`; empty when it is not set. -/
  driver : String
  /-- The root package's own `leanOptions`, each key once, as Lake resolves the package
  configuration (without build-type or target options). -/
  options : List (Name × OptionValue)
  /-- The own `leanOptions` of each root `lean_lib` and `lean_exe`. Lake builds a target with the
  package's options followed by the target's own, a later value for a key replacing an earlier
  one; the build type adds only `debugAssertions`. -/
  targets : List (List (Name × OptionValue))
  /-- The workspace contains Mathlib, so a claimed target may import it. -/
  mathlib : Bool
  /-- `foundation_manifest.json` exists at the project root. -/
  manifest : Bool
  /-- `AGENTS.md` contains the `agentsHeading` line. -/
  agentsSection : Bool
  /-- Each recognized skill file that exists, and whether it equals the installed skill. -/
  skills : List (String × Bool)
  /-- The project's `lean-toolchain`, trimmed. -/
  toolchain : String
  /-- The `lean-toolchain` of the required Regula, the only release it supports. -/
  supported : String
  deriving DecidableEq, Repr

/-- The package-level options of an observation, as the RG2006 decision reads options. -/
def Observation.build (o : Observation) : BuildOptions := ⟨o.options, []⟩

/-- The key `init` writes for option `name`: Mathlib's options under `weak.`, which Lean ignores
in a module that does not import Mathlib, and every other option as it is. -/
def key (name : Name) : Name :=
  if (mathlibBaseline.map Prod.fst).contains name then `weak ++ name else name

/-- A required option `init` adds to the package: one the package gives no value under either
spelling while some target gives it none either, so that target builds without it. -/
def Observation.lacks (o : Observation) (r : Name × OptionValue) : Bool :=
  (valuesOf o.build r.1).isEmpty && o.targets.any fun own => (valuesOf ⟨own, []⟩ r.1).isEmpty

/-- The options `init` adds: every required option the observation `lacks`, with its required
value, keyed by `key`. An option given a wrong value is left for its owner to change (`doctor`
reports it through RG2006). -/
def missing (o : Observation) : List (Name × OptionValue) :=
  ((required o.mathlib).filter o.lacks).map fun r => (key r.1, r.2)

/-- One missing or wrong piece of setup. -/
inductive Issue where
  /-- The package sets no `lintDriver`, so `lake lint` does not run Regula. -/
  | driverUnset
  /-- The package's `lintDriver` is another driver; Lake has one per package. -/
  | driverOther (driver : String)
  /-- The package gives no value to these required options (the entries `init` adds). -/
  | optionsMissing (entries : List (Name × OptionValue))
  /-- There is no `foundation_manifest.json`. -/
  | manifestMissing
  /-- There is neither an `AGENTS.md` section nor a skill file. -/
  | guidanceMissing
  /-- The skill file at `path` differs from the installed Regula's skill. -/
  | skillStale (path : String)
  /-- The project uses toolchain `project`, but Regula supports only `supported`. -/
  | toolchain (project supported : String)
  deriving DecidableEq, Repr

/-- Whether `init` writes the fix. It never replaces another lint driver. -/
def Issue.fixable : Issue → Bool
  | .driverUnset => true
  | .driverOther _ => false
  | .optionsMissing _ => true
  | .manifestMissing => true
  | .guidanceMissing => true
  | .skillStale _ => true
  | .toolchain _ _ => false

/-- The skill files that differ from the installed skill. -/
def staleSkills (o : Observation) : List String := (o.skills.filter (!·.2)).map (·.1)

/-- The project has agent guidance: the `AGENTS.md` section or a skill file. -/
def Observation.guided (o : Observation) : Bool := o.agentsSection || !o.skills.isEmpty

/-- The lint-driver issue, if any. -/
def driverIssues (o : Observation) : List Issue :=
  if o.driver = "" then [.driverUnset] else if o.driver = lintDriver then [] else
    [.driverOther o.driver]

/-- Every setup issue of an observation, in a fixed order. -/
def issues (o : Observation) : List Issue :=
  driverIssues o ++
  (if missing o = [] then [] else [.optionsMissing (missing o)]) ++
  (if o.manifest then [] else [.manifestMissing]) ++
  (if o.guided then [] else [.guidanceMissing]) ++
  (staleSkills o).map .skillStale ++
  (if o.toolchain = o.supported then [] else [.toolchain o.toolchain o.supported])

/-- One edit `init` writes. -/
inductive Edit where
  /-- Set the package's `lintDriver` to `lintDriver`. -/
  | driver
  /-- Add these entries to the package's `leanOptions`. -/
  | options (entries : List (Name × OptionValue))
  /-- Write the starter `foundation_manifest.json`. -/
  | manifest
  /-- Append `agentsSection` to `AGENTS.md`, creating the file if needed. -/
  | agentsSection
  /-- Write the installed skill at `path`. -/
  | skill (path : String)
  deriving DecidableEq, Repr

/-- The guidance edit when the project has none: the preference `g`. -/
def guidanceEdits (g : Guidance) (o : Observation) : List Edit :=
  if o.guided then [] else
    match g with
    | .agentsMd => [.agentsSection]
    | .skill => [.skill skillPath]

/-- The edits that fix `o`'s fixable issues, each writing only what is missing. -/
def plan (g : Guidance) (o : Observation) : List Edit :=
  (if o.driver = "" then [.driver] else []) ++
  (if missing o = [] then [] else [.options (missing o)]) ++
  (if o.manifest then [] else [.manifest]) ++
  guidanceEdits g o ++
  (staleSkills o).map .skill

/-- Record that the skill file at `path` equals the installed skill. -/
def markCurrent (path : String) (skills : List (String × Bool)) : List (String × Bool) :=
  if skills.any (·.1 == path) then skills.map fun s => if s.1 == path then (s.1, true) else s
  else skills ++ [(path, true)]

/-- The effect of one edit on the observation. -/
def apply (o : Observation) : Edit → Observation
  | .driver => { o with driver := lintDriver }
  | .options entries => { o with options := o.options ++ entries }
  | .manifest => { o with manifest := true }
  | .agentsSection => { o with agentsSection := true }
  | .skill path => { o with skills := markCurrent path o.skills }

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

theorem run_targets (o : Observation) (es : List Edit) : (run o es).targets = o.targets := by
  induction es generalizing o with
  | nil => rfl
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> rfl

theorem run_toolchain (o : Observation) (es : List Edit) :
    (run o es).toolchain = o.toolchain ∧ (run o es).supported = o.supported := by
  induction es generalizing o with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [(ih _).1, (ih _).2]
    cases e <;> exact ⟨rfl, rfl⟩

theorem run_manifest (o : Observation) (es : List Edit) :
    (run o es).manifest = (o.manifest || decide (Edit.manifest ∈ es)) := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply]

theorem run_agentsSection (o : Observation) (es : List Edit) :
    (run o es).agentsSection = (o.agentsSection || decide (Edit.agentsSection ∈ es)) := by
  induction es generalizing o with
  | nil => simp [run]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply]

theorem run_skills (o : Observation) (es : List Edit) :
    (run o es).skills = markAll o.skills (es.filterMap Edit.skillFile?) := by
  induction es generalizing o with
  | nil => simp [run, markAll]
  | cons e es ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    cases e <;> simp [apply, Edit.skillFile?, markAll, List.filterMap_cons]

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

/-- The values the added entries give a required option: its required value when the
observation `lacks` it, and nothing otherwise. -/
theorem valuesOf_missing (o : Observation) (r : Name × OptionValue)
    (hr : r ∈ required o.mathlib) :
    valuesOf ⟨missing o, []⟩ r.1 = if o.lacks r then [r.2] else [] := by
  have hnd : ((required o.mathlib).filter o.lacks).Nodup :=
    (required_nodup o.mathlib).sublist List.filter_sublist
  rw [missing, valuesOf_keyed o.mathlib r hr _ (fun q hq => (List.mem_filter.mp hq).1) hnd]
  by_cases h : o.lacks r <;> simp [h, List.mem_filter, hr]

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
      if o.guided then [] else match g with | .agentsMd => [] | .skill => [skillPath] := by
  unfold guidanceEdits
  split
  · rfl
  · cases g <;> rfl

/-- The plan has at most one options edit, and it adds `missing o`. -/
theorem plan_entries (g : Guidance) (o : Observation) :
    (plan g o).flatMap Edit.entries = missing o := by
  simp only [plan, List.flatMap_append, guidanceEdits_entries]
  by_cases hd : o.driver = "" <;> by_cases hm : missing o = [] <;> cases hf : o.manifest <;>
    simp [hd, hm, Edit.entries, List.flatMap_map]

theorem plan_driver_mem (g : Guidance) (o : Observation) :
    Edit.driver ∈ plan g o ↔ o.driver = "" := by
  have := driver_not_mem_guidanceEdits g o
  by_cases hd : o.driver = "" <;> by_cases hm : missing o = [] <;> cases hf : o.manifest <;>
    simp [plan, hd, hm, hf, this]

theorem plan_manifest_mem (g : Guidance) (o : Observation) :
    Edit.manifest ∈ plan g o ↔ o.manifest = false := by
  have := manifest_not_mem_guidanceEdits g o
  by_cases hd : o.driver = "" <;> by_cases hm : missing o = [] <;> cases hf : o.manifest <;>
    simp [plan, hd, hm, hf, this]

theorem plan_skillFiles (g : Guidance) (o : Observation) :
    (plan g o).filterMap Edit.skillFile? =
      (if o.guided then [] else match g with | .agentsMd => [] | .skill => [skillPath]) ++
        staleSkills o := by
  simp only [plan, List.filterMap_append, guidanceEdits_skillFiles, List.filterMap_map]
  by_cases hd : o.driver = "" <;> by_cases hm : missing o = [] <;> cases hf : o.manifest <;>
    simp [hd, hm, Edit.skillFile?, Function.comp_def, List.filterMap_cons]

/-! ## Main theorems -/

/-- The package's options after the plan: its own, then the missing ones. -/
theorem run_plan_options (g : Guidance) (o : Observation) :
    (run o (plan g o)).options = o.options ++ missing o := by
  rw [run_options, plan_entries]

/-- A target that built without a required option builds with it after the plan, set to its
required value, as the RG2006 decision reads the options Lake resolves for the target: the
package's, then the target's own. -/
theorem run_sets (g : Guidance) (o : Observation) (own : List (Name × OptionValue))
    (hown : own ∈ o.targets) (r : Name × OptionValue) (hr : r ∈ required o.mathlib)
    (h : valuesOf ⟨o.options ++ own, []⟩ r.1 = []) :
    sets ⟨(run o (plan g o)).options ++ own, []⟩ r.1 r.2 = true := by
  rw [valuesOf_append, List.append_eq_nil_iff] at h
  have hl : o.lacks r = true := by
    simp only [Observation.lacks, Observation.build, h.1, List.isEmpty_nil, Bool.true_and,
      List.any_eq_true]
    exact ⟨own, hown, by simp [h.2]⟩
  have hv : valuesOf ⟨(run o (plan g o)).options ++ own, []⟩ r.1 = [r.2] := by
    rw [run_plan_options, valuesOf_append, valuesOf_append, h.1, h.2, valuesOf_missing o r hr,
      hl]
    rfl
  simp [sets, hv, readsAs_self]

/-- The plan never changes or removes an option the package already gives. -/
theorem run_options_prefix (g : Guidance) (o : Observation) :
    o.options <+: (run o (plan g o)).options := by
  rw [run_plan_options]
  exact List.prefix_append _ _

/-- No required option is missing after the plan. -/
theorem missing_run (g : Guidance) (o : Observation) : missing (run o (plan g o)) = [] := by
  unfold missing
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro r hr
  rw [run_mathlib] at hr
  have hpkg : valuesOf (run o (plan g o)).build r.1 =
      valuesOf o.build r.1 ++ valuesOf ⟨missing o, []⟩ r.1 := by
    simp only [Observation.build, run_plan_options, valuesOf_append]
  have hv := valuesOf_missing o r hr
  cases hl : o.lacks r
  · rw [hl] at hv
    unfold Observation.lacks at hl ⊢
    rw [hpkg, hv, run_targets]
    simp only [Bool.and_eq_false_iff] at hl
    rcases hl with hl | hl <;> simp [hl]
  · rw [hl] at hv
    unfold Observation.lacks
    rw [hpkg, hv]
    simp

/-- After the plan, every root target builds with a value for every required option. -/
theorem resolved_run (g : Guidance) (o : Observation) (own : List (Name × OptionValue))
    (hown : own ∈ o.targets) (r : Name × OptionValue) (hr : r ∈ required o.mathlib) :
    valuesOf ⟨(run o (plan g o)).options ++ own, []⟩ r.1 ≠ [] := by
  intro h
  have hs := run_sets g o own hown r hr
  rw [valuesOf_append, List.append_eq_nil_iff] at h
  by_cases hp : valuesOf ⟨o.options ++ own, []⟩ r.1 = []
  · have := hs hp
    simp [sets, valuesOf_append, h.1, h.2] at this
  · apply hp
    rw [valuesOf_append, List.append_eq_nil_iff]
    have hpre := h.1
    rw [run_plan_options, valuesOf_append, List.append_eq_nil_iff] at hpre
    exact ⟨hpre.1, h.2⟩

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
        ((if o.guided then [] else match g with | .agentsMd => [] | .skill => [skillPath]) ++
          staleSkills o) (.inl hne)
      simp [this]
  · have hg' : o.guided = false := by simpa using hg
    cases g
    · have hmem : Edit.agentsSection ∈ plan .agentsMd o := by
        simp [plan, guidanceEdits, hg']
      simp [hmem]
    · have := markAll_ne_nil (skills := o.skills) (skillPath :: staleSkills o) (.inr (by simp))
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

/-- The manifest exists after the plan. -/
theorem manifest_run (g : Guidance) (o : Observation) : (run o (plan g o)).manifest = true := by
  rw [run_manifest]
  cases hm : o.manifest
  · have h : Edit.manifest ∈ plan g o := (plan_manifest_mem g o).mpr hm
    simp [h]
  · rfl

/-- After `init` applies its plan, the plan of the result is empty: a second run writes
nothing. -/
theorem plan_idempotent (g : Guidance) (o : Observation) : plan g (run o (plan g o)) = [] := by
  have h1 := driver_run g o
  have h2 := missing_run g o
  have h3 := manifest_run g o
  have h4 := guided_run g o
  have h5 := staleSkills_run g o
  generalize run o (plan g o) = r at h1 h2 h3 h4 h5
  simp [plan, guidanceEdits, h1, h2, h3, h4, h5]

theorem guidanceEdits_eq_nil_iff (g : Guidance) (o : Observation) :
    guidanceEdits g o = [] ↔ o.guided = true := by
  unfold guidanceEdits
  cases o.guided <;> cases g <;> simp

/-- The conditions under which nothing is left for `init` to write. -/
def Settled (o : Observation) : Prop :=
  o.driver ≠ "" ∧ missing o = [] ∧ o.manifest = true ∧ o.guided = true ∧ staleSkills o = []

/-- The plan is empty exactly when the observation is settled. -/
theorem plan_eq_nil_iff_settled (g : Guidance) (o : Observation) :
    plan g o = [] ↔ Settled o := by
  unfold plan Settled
  rw [← guidanceEdits_eq_nil_iff g o]
  by_cases hd : o.driver = "" <;> by_cases hm : missing o = [] <;> cases hf : o.manifest <;>
    simp_all

/-- No fixable issue is left exactly when the observation is settled. -/
theorem issues_unfixable_iff_settled (o : Observation) :
    (∀ i ∈ issues o, i.fixable = false) ↔ Settled o := by
  constructor
  · intro h
    refine ⟨fun hd => ?_, ?_, ?_, ?_, ?_⟩
    · have := h .driverUnset (by simp [issues, driverIssues, hd])
      exact Bool.noConfusion this
    · by_cases hm : missing o = []
      · exact hm
      · have := h (.optionsMissing (missing o)) (by simp [issues, hm])
        exact Bool.noConfusion this
    · cases hm : o.manifest
      · have := h .manifestMissing (by simp [issues, hm])
        exact Bool.noConfusion this
      · rfl
    · cases hg : o.guided
      · have := h .guidanceMissing (by simp [issues, hg])
        exact Bool.noConfusion this
      · rfl
    · rw [List.eq_nil_iff_forall_not_mem]
      intro p hp
      have := h (.skillStale p) (by simp [issues, hp])
      exact Bool.noConfusion this
  · rintro ⟨hd, hm, hf, hg, hs⟩ i hi
    simp only [issues, hm, hf, hg, hs, ↓reduceIte, List.map_nil, List.append_nil,
      List.mem_append] at hi
    rcases hi with hi | hi
    · unfold driverIssues at hi
      simp only [hd, ↓reduceIte] at hi
      split at hi
      · simp at hi
      · rw [List.mem_singleton] at hi
        rw [hi]
        rfl
    · split at hi
      · simp at hi
      · rw [List.mem_singleton] at hi
        rw [hi]
        rfl

/-- The plan is empty exactly when every setup issue is one `init` does not write. -/
theorem plan_eq_nil_iff (g : Guidance) (o : Observation) :
    plan g o = [] ↔ ∀ i ∈ issues o, i.fixable = false :=
  (plan_eq_nil_iff_settled g o).trans (issues_unfixable_iff_settled o).symm

/-- Applying the plan removes exactly the issues `init` writes a fix for and adds none. -/
theorem issues_run (g : Guidance) (o : Observation) :
    issues (run o (plan g o)) = (issues o).filter (!·.fixable) := by
  have h1 := run_plan_driver g o
  have h2 := missing_run g o
  have h3 := manifest_run g o
  have h4 := guided_run g o
  have h5 := staleSkills_run g o
  have ⟨h6, h7⟩ := run_toolchain o (plan g o)
  have hs : ((staleSkills o).map Issue.skillStale).filter (!·.fixable) = [] := by
    induction staleSkills o <;> simp_all [Issue.fixable]
  have ht : (if o.toolchain = o.supported then []
      else [Issue.toolchain o.toolchain o.supported]).filter (!·.fixable) =
      if o.toolchain = o.supported then [] else [Issue.toolchain o.toolchain o.supported] := by
    split <;> rfl
  generalize run o (plan g o) = r at h1 h2 h3 h4 h5 h6 h7
  simp only [issues, h2, h3, h4, h5, h6, h7, ↓reduceIte, List.map_nil, List.append_nil,
    List.filter_append, hs, ht]
  have hm : (if missing o = [] then [] else [Issue.optionsMissing (missing o)]).filter
      (!·.fixable) = [] := by split <;> rfl
  have hf : (if o.manifest = true then [] else [Issue.manifestMissing]).filter
      (!·.fixable) = [] := by split <;> rfl
  have hg : (if o.guided = true then [] else [Issue.guidanceMissing]).filter
      (!·.fixable) = [] := by split <;> rfl
  rw [hm, hf, hg]
  unfold driverIssues
  rw [h1]
  by_cases hd : o.driver = ""
  · simp [hd, lintDriver, Issue.fixable]
  · by_cases hl : o.driver = lintDriver
    · simp [hl, lintDriver]
    · simp [hd, hl, Issue.fixable]

/-! ## Finding text

`doctor` prints each issue as the linter prints a finding: what is wrong and where on the first
line, then the fix. -/

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

/-- Where options go in each format. -/
def Lakefile.optionsPlace : Lakefile → String
  | .lean => "the `package` declaration's `leanOptions`"
  | .toml => "the `[leanOptions]` table"

/-- The first line of an issue's finding: `setup [FILE]: what is wrong`. -/
def Issue.message (f : Lakefile) : Issue → String
  | .driverUnset => "setup [" ++ f.name ++ "]: `lintDriver` is not set, so `lake lint` does \
      not run Regula"
  | .driverOther d => "setup [" ++ f.name ++ "]: `lintDriver` is \"" ++ d ++ "\", so `lake lint` \
      runs that driver and not Regula"
  | .optionsMissing es => "setup [" ++ f.name ++ "]: a target builds without " ++
      ", ".intercalate (es.map fun e => "`" ++ toString (optionOf e.1) ++ "`") ++
      ", which the package's `leanOptions` do not set"
  | .manifestMissing => "setup [foundation_manifest.json]: the file does not exist, so `lake lint` \
      has no claimed surface"
  | .guidanceMissing => "setup [AGENTS.md]: no agent guidance: AGENTS.md has no `" ++
      agentsHeading ++ "` section and there is no " ++ skillPath
  | .skillStale p => "setup [" ++ p ++ "]: the skill is not the installed Regula's briefing"
  | .toolchain p s => "setup [lean-toolchain]: the project uses " ++ p ++
      ", but this Regula supports only " ++ s

/-- The fix line of an issue's finding. -/
def Issue.fix (f : Lakefile) : Issue → String
  | .driverUnset => "  fix: set " ++ f.driverSetting ++ ", or run `lake exe regula init`"
  | .driverOther _ => "  fix: Lake runs one lint driver per package: keep it and run Regula as \
      its own step with `lake exe lint`, or set lintDriver to \"" ++ lintDriver ++ "\" and run \
      the other driver as its own command (init never replaces a driver)"
  | .optionsMissing es => "  fix: add " ++
      ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " to " ++ f.optionsPlace ++
      ", or run `lake exe regula init`"
  | .manifestMissing => "  fix: run `lake exe regula init`, which writes a starter claiming every \
      `lean_lib` as `standard-logical`; then review each claim and rationale"
  | .guidanceMissing => "  fix: run `lake exe regula init` (adds the AGENTS.md section) or \
      `lake exe regula init --skill` (writes the skill)"
  | .skillStale _ => "  fix: run `lake exe regula init`, which rewrites it (for example after \
      `lake update regula`)"
  | .toolchain _ s => "  fix: set lean-toolchain to " ++ s ++ " and run `lake update`, or require \
      the Regula release tagged for your toolchain"

/-- What an edit writes, as a phrase `init` and `doctor` print after "wrote" or "would write". -/
def Edit.summary (f : Lakefile) : Edit → String
  | .driver => f.driverSetting ++ " in " ++ f.name
  | .options es => ", ".intercalate (es.map fun e => "`" ++ f.entry e ++ "`") ++ " in " ++
      f.optionsPlace ++ " of " ++ f.name
  | .manifest => "a starter foundation_manifest.json (review each claim and rationale)"
  | .agentsSection => "the `" ++ agentsHeading ++ "` section in AGENTS.md"
  | .skill p => p ++ ", the installed Regula's skill"

end Regula.Setup
