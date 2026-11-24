module

public import Lean.Data.Name
public import LeanIntent.Record
public import LeanIntent.Obligations
public import LeanIntent.Progress
public import Regula.LanguageSet
import all Init.Meta.Defs
import all Regula.LanguageSet

@[expose] public section

namespace RegulaSpecification.Language

open Lean (Name Syntax)
open Regula.Language
open LeanIntent

inductive Occurs : Syntax → Syntax → Prop where
  | self (t : Syntax) : Occurs t t
  | child {s c : Syntax} {i : Lean.SourceInfo} {k : Name} {as : Array Syntax} :
      k ∉ leafKinds → c ∈ as → Occurs s c → Occurs s (.node i k as)

inductive ReservedName : Name → Prop where
  | underscore {p : Name} {s : String} : s.front = '_' → (p, s) ≠ (.anonymous, "_root_") →
      ReservedName (.str p s)
  | autoParam {p : Name} : ReservedName (.str p "autoParam")
  | str {p : Name} {s : String} : ReservedName p → ReservedName (.str p s)
  | num {p : Name} {n : Nat} : ReservedName p → ReservedName (.num p n)

def TargetOf (as : Array Syntax) (n : Name) : Prop :=
  ∃ i r p, Syntax.ident i r n p ∈ as ∨
    ∃ i' xs, Syntax.node i' `null xs ∈ as ∧ Syntax.ident i r n p ∈ xs

def targetComponents (n : Name) : List Name :=
  n.components.dropWhile (· = `_root_)

def CanActivate (N n : Name) : Prop :=
  ∃ i, 0 < i ∧ i ≤ (targetComponents n).length ∧
    (targetComponents n).take i <:+ N.components

def NodeAdmitted (scopedParsers : List Name) (k : Name) (as : Array Syntax) : Prop :=
  (k ∈ kinds ∨ k ∈ leafKinds) ∧
  (k = `Lean.Parser.Attr.simple →
    (∃ i r a p, as[0]? = some (.ident i r a p) ∧ a ∈ simpleAttributes) ∧
      ∃ i', as[1]? = some (.node i' `null #[])) ∧
  (k = `Lean.Parser.Command.set_option →
    ∃ i r o p, as[1]? = some (.ident i r o p) ∧ o ∈ options) ∧
  (k = `Lean.Parser.Tactic.posConfigItem →
    ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ configItems) ∧
  (k = `Lean.Parser.Command.derivingClass →
    ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ derivingClasses) ∧
  ((k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple) →
    ∀ n, TargetOf as n → ∀ N ∈ scopedParsers, ¬ CanActivate N n)

def PositionAdmitted (scopedParsers : List Name) : Syntax → Prop
  | .missing => False
  | .atom _ v => v ∈ atoms
  | .ident _ _ n _ => ¬ ReservedName n
  | .node _ k as => NodeAdmitted scopedParsers k as

def TreeAdmitted (scopedParsers : List Name) (t : Syntax) : Prop :=
  ∀ s, Occurs s t → PositionAdmitted scopedParsers s

def ModuleFile (header : Syntax) : Prop :=
  ∃ i as, Occurs (.node i `Lean.Parser.Module.moduleTk as) header

def ReadToEnd (commands : List Syntax) : Prop :=
  ∃ i as, commands.getLast? = some (.node i `Lean.Parser.Command.eoi as)

def FileAdmitted (f : FileRead) : Prop :=
  f.parsed = true ∧ ModuleFile f.header ∧ ReadToEnd f.commands ∧
    TreeAdmitted f.scopedParsers f.header ∧ ∀ c ∈ f.commands, TreeAdmitted f.scopedParsers c

def ConfigKeyAdmitted (k : Name) : Prop :=
  k ∈ configKeys ∨ ∃ o ∈ options, k = `leanOptions ++ o

def ConfigClosed (r : Reading) : Prop :=
  r.toolchainFile = some leanToolchain ∧ r.leanConfig = false ∧ r.openPaths = [] ∧
    ∀ k ∈ r.configKeys, k.getRoot ≠ `require → ConfigKeyAdmitted k

def ReadInFull (r : Reading) : Prop :=
  r.unread = []

def TreeRelative (base path rel : List String) : Prop :=
  path = base ++ rel ∧ ∀ c ∈ rel, c ≠ "" ∧ c.front ≠ '.'

def RequiresDependency (r : Reading) : Prop :=
  ∃ k ∈ r.configKeys, k.getRoot = `require

def MathlibReached (r : Reading) : Prop :=
  ∃ m ∈ r.reached, m.getRoot = `Mathlib

def ClosedChar (c : Char) : Prop :=
  c.isAlphanum = true ∨ c = '_' ∨ c = '\''

instance : DecidablePred ClosedChar := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def ClosedComponent (s : String) : Prop :=
  s ≠ "" ∧ ∀ c ∈ s.toList, ClosedChar c

instance : DecidablePred ClosedComponent := fun _ => inferInstanceAs (Decidable (_ ∧ _))

inductive ClosedModuleName : Name → Prop where
  | one {s : String} : ClosedComponent s → ClosedModuleName (.str .anonymous s)
  | more {p : Name} {s : String} : ClosedModuleName p → ClosedComponent s →
      ClosedModuleName (.str p s)

def Covered (r : Reading) : Prop :=
  r.roots ≠ [] ∧ (∀ m ∈ r.roots, m ∈ r.reached) ∧ (∀ m ∈ r.reached, ClosedModuleName m) ∧
    ∀ m ∈ r.reached, ∃ f ∈ r.files, f.module = m

def FilesAdmitted (r : Reading) : Prop :=
  ∀ f ∈ r.files, FileAdmitted f

def languageRecord : IntentRecord (Reading → Outcome) where
  shape := .function Reading (fun _ => Outcome)
  dom := []
  props := [
    ⟨"another toolchain, a lakefile.lean, a source directory or a globs entry outside the closed domain, or a Lake key outside the closed set is refused",
      fun d => ∀ r, ¬ ConfigClosed r → d r = .refused⟩,
    ⟨"a failure to read is incomplete",
      fun d => ∀ r, ConfigClosed r → ¬ ReadInFull r → d r = .incomplete⟩,
    ⟨"a project with a dependency has only the proof verdict",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → RequiresDependency r → d r = .proofOnly⟩,
    ⟨"a build with Mathlib in its imports has only the proof verdict",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r → MathlibReached r →
        d r = .proofOnly⟩,
    ⟨"a project with no claim, a module name outside the closed domain or a module left unread is incomplete",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r →
        ¬ MathlibReached r → ¬ Covered r → d r = .incomplete⟩,
    ⟨"a file outside the closed language is refused",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r →
        ¬ MathlibReached r → Covered r → ¬ FilesAdmitted r → d r = .refused⟩,
    ⟨"a project wholly inside the closed language is admitted",
      fun d => ∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r →
        ¬ MathlibReached r → Covered r → FilesAdmitted r → d r = .admitted⟩]
  vocab := [
    ⟨"a closed configuration", Reading, ConfigClosed⟩,
    ⟨"a reading in full", Reading, ReadInFull⟩,
    ⟨"a project with a dependency", Reading, RequiresDependency⟩,
    ⟨"Mathlib in the imports", Reading, MathlibReached⟩,
    ⟨"a covered reading", Reading, Covered⟩,
    ⟨"admitted files", Reading, FilesAdmitted⟩,
    ⟨"an admitted file", FileRead, FileAdmitted⟩,
    ⟨"a closed module name", Name, ClosedModuleName⟩]

theorem language_meets_iff (d : Reading → Outcome) :
    languageRecord.Meets d ↔
      (∀ r, ¬ ConfigClosed r → d r = .refused) ∧
      (∀ r, ConfigClosed r → ¬ ReadInFull r → d r = .incomplete) ∧
      (∀ r, ConfigClosed r → ReadInFull r → RequiresDependency r → d r = .proofOnly) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r → MathlibReached r →
        d r = .proofOnly) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r → ¬ MathlibReached r →
        ¬ Covered r → d r = .incomplete) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r → ¬ MathlibReached r →
        Covered r → ¬ FilesAdmitted r → d r = .refused) ∧
      (∀ r, ConfigClosed r → ReadInFull r → ¬ RequiresDependency r → ¬ MathlibReached r →
        Covered r → FilesAdmitted r → d r = .admitted) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, languageRecord]

def Inside (r : Reading) : Prop :=
  ConfigClosed r ∧ ReadInFull r ∧ ¬ RequiresDependency r ∧ ¬ MathlibReached r ∧ Covered r ∧
    FilesAdmitted r

noncomputable def modelDecision (r : Reading) : Outcome :=
  open Classical in
  if ¬ ConfigClosed r then .refused
  else if ¬ ReadInFull r then .incomplete
  else if RequiresDependency r then .proofOnly
  else if MathlibReached r then .proofOnly
  else if ¬ Covered r then .incomplete
  else if ¬ FilesAdmitted r then .refused
  else .admitted

theorem modelDecision_meets : languageRecord.Meets modelDecision := by
  rw [language_meets_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [modelDecision]

theorem language_o2Run : O2Run languageRecord := o2Run_of_meets modelDecision_meets

private theorem meets_eq_model {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading) :
    d r = modelDecision r := by
  obtain ⟨h1, h2, hc, h3, h4, h5, h6⟩ := (language_meets_iff d).mp h
  unfold modelDecision
  repeat' split
  · exact h1 r ‹_›
  · exact h2 r (Classical.not_not.mp ‹_›) ‹_›
  · exact hc r (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›) ‹_›
  · exact h3 r (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›) ‹_› ‹_›
  · exact h4 r (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›) ‹_› ‹_› ‹_›
  · exact h5 r (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›) ‹_› ‹_› (Classical.not_not.mp ‹_›) ‹_›
  · exact h6 r (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›) ‹_› ‹_› (Classical.not_not.mp ‹_›) (Classical.not_not.mp ‹_›)

theorem admitted_iff {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading) :
    d r = .admitted ↔ Inside r := by
  rw [meets_eq_model h r]; unfold modelDecision Inside
  repeat' split <;> simp_all

theorem language_o5 : O5 languageRecord .eq := by
  rw [o5_correct]; intro u v hu hv
  funext r; rw [meets_eq_model ⟨hu.1, hu.2⟩ r, meets_eq_model ⟨hv.1, hv.2⟩ r]

theorem language_o4 : O4 languageRecord := o4_function _ rfl

def moduleHeader : Syntax :=
  .node .none `Lean.Parser.Module.moduleTk #[.atom .none "module"]

def endOfInput : Syntax :=
  .node .none `Lean.Parser.Command.eoi #[.atom .none ""]

def goodFile : FileRead :=
  { module := `Good, header := moduleHeader, commands := [endOfInput], parsed := true,
    scopedParsers := [] }

def goodReading : Reading :=
  { toolchainFile := some leanToolchain, leanConfig := false,
    configKeys := [`name], openPaths := [], roots := [`Good], reached := [`Good],
    files := [goodFile], unread := [] }

theorem occurs_moduleHeader {s : Syntax} (h : Occurs s moduleHeader) :
    s = moduleHeader ∨ s = .atom .none "module" := by
  cases h with
  | self => exact .inl rfl
  | @child c _ _ _ _ hc hs =>
    have hc' : c = .atom .none "module" := by simpa using hc
    subst hc'; cases hs; exact .inr rfl

theorem admitted_moduleHeader : TreeAdmitted [] moduleHeader := fun s h => by
  rcases occurs_moduleHeader h with rfl | rfl
  · refine ⟨.inl (by decide +kernel), ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;>
      first | exact absurd h' (by decide) | exact absurd h'.elim (by decide)
  · show "module" ∈ atoms; decide +kernel

theorem occurs_endOfInput {s : Syntax} (h : Occurs s endOfInput) : s = endOfInput := by
  cases h with
  | self => rfl
  | child hk _ _ => exact absurd (by decide +kernel) hk

theorem admitted_endOfInput : TreeAdmitted [] endOfInput := fun s h => by
  rw [occurs_endOfInput h]
  refine ⟨.inr (by decide +kernel), ?_, ?_, ?_, ?_, ?_⟩ <;> intro h' <;>
    first | exact absurd h' (by decide) | exact absurd h'.elim (by decide)

theorem goodFile_admitted : FileAdmitted goodFile :=
  ⟨rfl, ⟨.none, _, .self _⟩, ⟨.none, _, rfl⟩, admitted_moduleHeader, fun c hc => by
    have : c = endOfInput := by simpa [goodFile] using hc
    exact this ▸ admitted_endOfInput⟩

theorem good_closed_name : ClosedModuleName `Good := .one (by decide +kernel)

theorem absolute_name_not_closed : ¬ ClosedModuleName (.str .anonymous "/abs/vendor/Evil") := fun h => by
  cases h with | one hc => exact absurd hc (by decide +kernel) | more hp _ => cases hp

theorem parent_name_not_closed : ¬ ClosedModuleName (.str .anonymous "..") := fun h => by
  cases h with | one hc => exact absurd hc (by decide +kernel) | more hp _ => cases hp

theorem closed_of_goodKeys {r : Reading} (ht : r.toolchainFile = some leanToolchain)
    (hl : r.leanConfig = false) (ho : r.openPaths = []) (hk : r.configKeys = [`name]) :
    ConfigClosed r :=
  ⟨ht, hl, ho, fun k h _ => by
    have : k = `name := by simpa [hk] using h
    exact this ▸ .inl (by decide +kernel)⟩

theorem no_dependency_of_goodKeys {r : Reading} (hk : r.configKeys = [`name]) :
    ¬ RequiresDependency r := fun ⟨k, hm, hr⟩ => by
  have : k = `name := by simpa [hk] using hm
  exact absurd (this ▸ hr) (by decide)

theorem goodReading_inside : Inside goodReading :=
  ⟨closed_of_goodKeys rfl rfl rfl rfl, rfl, no_dependency_of_goodKeys rfl,
    fun ⟨m, hm, hr⟩ => absurd ((by simpa [goodReading] using hm : m = `Good) ▸ hr) (by decide),
    ⟨by simp [goodReading], by simp [goodReading],
      fun m hm => (by simpa [goodReading] using hm : m = `Good) ▸ good_closed_name,
      fun m hm => ⟨goodFile, by simp [goodReading], (by simpa [goodReading] using hm : m = `Good).symm⟩⟩,
    fun f hf => (by simpa [goodReading] using hf : f = goodFile) ▸ goodFile_admitted⟩

def leanConfigReading : Reading := { goodReading with leanConfig := true }

def unreadReading : Reading := { goodReading with unread := [(`Good, "unread")] }

def requireReading : Reading := { goodReading with configKeys := [`name, `require.name] }

def noClaimReading : Reading :=
  { goodReading with roots := [], reached := [], files := [] }

def mathlibReading : Reading :=
  { goodReading with reached := [`Good, `Mathlib.Tactic] }

def badFileReading : Reading :=
  { goodReading with files := [{ goodFile with commands := [.missing, endOfInput] }] }

theorem leanConfig_not_closed : ¬ ConfigClosed leanConfigReading := fun h => by
  simpa [leanConfigReading, goodReading] using h.2.1

theorem noClaim_not_covered : ¬ Covered noClaimReading := fun h => by
  simpa [noClaimReading] using h.1

theorem good_closed : ConfigClosed goodReading := closed_of_goodKeys rfl rfl rfl rfl

theorem good_full : ReadInFull goodReading := rfl

theorem good_no_dependency : ¬ RequiresDependency goodReading := goodReading_inside.2.2.1

theorem require_closed : ConfigClosed requireReading := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk hr
  have : k = `name ∨ k = `require.name := by simpa [requireReading] using hk
  rcases this with rfl | rfl
  · exact .inl (by decide +kernel)
  · exact absurd (by decide) hr

theorem require_requires : RequiresDependency requireReading :=
  ⟨`require.name, by simp [requireReading], by decide⟩

theorem mathlib_reached : MathlibReached mathlibReading :=
  ⟨`Mathlib.Tactic, by simp [mathlibReading], by decide⟩

theorem not_mathlib_of_reached {r : Reading} (h : ∀ m ∈ r.reached, m = `Good ∨ m = `Other) :
    ¬ MathlibReached r := by
  rintro ⟨m, hm, hr⟩
  rcases h m hm with rfl | rfl <;> exact absurd hr (by decide)

theorem badFile_covered : Covered badFileReading :=
  ⟨by simp [badFileReading, goodReading], by simp [badFileReading, goodReading],
    fun m hm => (by simpa [badFileReading, goodReading] using hm : m = `Good) ▸ good_closed_name,
    fun m hm => ⟨{ goodFile with commands := [.missing, endOfInput] }, by simp [badFileReading],
      (by simpa [badFileReading, goodReading] using hm : m = `Good).symm⟩⟩

theorem badFile_refused : ¬ FilesAdmitted badFileReading := fun h =>
  (h { goodFile with commands := [.missing, endOfInput] } (by simp [badFileReading])).2.2.2.2
    .missing (by simp) .missing (.self _)

theorem language_o2 : O2 languageRecord := by
  rw [o2_correct]
  refine ⟨⟨modelDecision, by simp [languageRecord]⟩, ?_⟩
  intro p hp
  simp only [languageRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨goodReading, good_closed⟩
  · exact ⟨goodReading, good_full⟩
  · exact ⟨requireReading, require_requires⟩
  · exact ⟨mathlibReading, mathlib_reached⟩
  · exact ⟨goodReading, goodReading_inside.2.2.2.2.1⟩
  · exact ⟨goodReading, goodReading_inside.2.2.2.2.2⟩
  · exact ⟨goodFile, goodFile_admitted⟩
  · exact ⟨`Good, good_closed_name⟩

theorem language_o3 : O3 languageRecord := by
  rw [o3_correct]
  intro p hp
  simp only [languageRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  have c {r : Reading} (ht : r.toolchainFile = some leanToolchain) (hl : r.leanConfig = false)
      (ho : r.openPaths = []) (hk : r.configKeys = [`name]) := closed_of_goodKeys ht hl ho hk
  have n {r : Reading} (hk : r.configKeys = [`name]) := no_dependency_of_goodKeys (r := r) hk
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun _ => .admitted, fun h => absurd (h leanConfigReading leanConfig_not_closed) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h unreadReading (c rfl rfl rfl rfl) fun hf => by simp [unreadReading, ReadInFull] at hf) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h requireReading require_closed rfl require_requires) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h mathlibReading (c rfl rfl rfl rfl) rfl (n rfl) mathlib_reached) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h noClaimReading (c rfl rfl rfl rfl) rfl (n rfl)
        (not_mathlib_of_reached (by simp [noClaimReading])) noClaim_not_covered) (by decide)⟩
  · exact ⟨fun _ => .admitted, fun h => absurd
      (h badFileReading (c rfl rfl rfl rfl) rfl (n rfl)
        (not_mathlib_of_reached (by simp [badFileReading, goodReading])) badFile_covered
        badFile_refused) (by decide)⟩
  · exact ⟨fun _ => .refused, fun h => absurd
      (h goodReading good_closed good_full good_no_dependency goodReading_inside.2.2.2.1
        goodReading_inside.2.2.2.2.1 goodReading_inside.2.2.2.2.2) (by decide)⟩

theorem constant_fails (o : Outcome) : ¬ languageRecord.Meets (fun _ => o) := fun h => by
  have ha := (admitted_iff h goodReading).mpr goodReading_inside
  have hb := ((language_meets_iff _).mp h).1 leanConfigReading leanConfig_not_closed
  rw [ha] at hb; cases hb

def refusedKinds : List Name :=
  [`Lean.runCmd, `Lean.Parser.Command.eval, `Lean.Parser.Command.evalBang,
    `Lean.Parser.Command.guardCmd, `Lean.guardMsgsCmd, `Lean.runElab, `Lean.runMeta,
    `Lean.Parser.Tactic.nativeDecide, `Lean.Parser.Tactic.runTac, `Lean.byElab,
    `Lean.Parser.Command.macro, `Lean.Parser.Command.macro_rules, `Lean.Parser.Command.syntax,
    `Lean.Parser.Command.syntaxAbbrev, `Lean.Parser.Command.syntaxCat,
    `Lean.Parser.Command.notation, `Lean.Parser.Command.mixfix, `Lean.Parser.Command.elab,
    `Lean.Parser.Command.elab_rules, `Lean.Parser.Command.initialize, `Lean.Parser.Attr.macro,
    `Lean.Parser.Attr.extern, `Lean.Parser.Attr.export, `Lean.Parser.Command.partial,
    `Lean.Parser.Command.unsafe, `Lean.Parser.Term.unsafe, `Lean.Parser.Command.meta,
    `Lean.Parser.Command.deriving, `Lean.Parser.Term.quot, `Lean.Parser.Tactic.quot,
    `Lean.Parser.Term.dynamicQuot, `Lean.Parser.Command.quot, `Lean.includeStr,
    `Lean.Parser.Term.binderTactic, `Lean.Parser.Command.openHiding,
    `Lean.Parser.Command.openRenaming, `Lean.Parser.Command.exit, `Lean.Parser.Command.import,
    `Lean.Parser.Module.prelude, `Lean.Parser.Tactic.tryTrace, `Lean.Parser.Tactic.exact?,
    `Lean.Parser.Tactic.apply?, `Lean.Parser.Command.check_failure]

theorem refusedKinds_outside : ∀ k ∈ refusedKinds, k ∉ kinds ∧ k ∉ leafKinds := by decide +kernel

theorem refused_attributes :
    ∀ a ∈ [`implemented_by, `extern, `csimp, `macro_inline, `init, `builtin_init, `export,
      `command_elab, `term_elab, `tactic, `macro, `simproc, `cbv_simproc],
    a ∉ simpleAttributes := by decide +kernel

theorem refused_options :
    ∀ o ∈ [`debug.skipKernelTC, `match.ignoreUnusedAlts, `internal.parseQuotWithCurrentStage,
      `compiler.extract_closed, `doc.verso],
    o ∉ options := by decide +kernel

theorem refused_config_keys :
    ∀ k ∈ [`plugins, `dynlibs, `moreLeanArgs, `weakLeanArgs, `moreServerOptions, `needs,
      `extraDepTargets, `precompileModules, `moreLinkObjs, `moreLinkLibs, `moreLinkArgs, `buildDir,
      `leanLibDir, `lean_lib.plugins, `lean_lib.dynlibs, `lean_lib.moreLeanArgs,
      `lean_lib.needs, `lean_lib.extraDepTargets, `lean_lib.precompileModules, `lean_exe.plugins,
      `lean_exe.needs, `lean_exe.moreLeanArgs, `testDriver, `packagesDir],
    k ∉ configKeys ∧ ∀ o ∈ options, k ≠ `leanOptions ++ o := by decide +kernel

theorem refused_target_srcDir :
    `lean_lib.srcDir ∉ configKeys ∧ `lean_exe.srcDir ∉ configKeys ∧
      ∀ o ∈ options, `lean_lib.srcDir ≠ `leanOptions ++ o ∧ `lean_exe.srcDir ≠ `leanOptions ++ o := by decide +kernel

theorem configKeys_no_require : ∀ k ∈ configKeys, k.getRoot ≠ `require := by decide +kernel

theorem open_path_refused {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : r.openPaths ≠ []) : d r = .refused := by
  obtain ⟨h1, -⟩ := (language_meets_iff d).mp h
  exact h1 r fun hc => hr hc.2.2.1

theorem require_not_admitted {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : RequiresDependency r) : d r ≠ .admitted :=
  fun ha => ((admitted_iff h r).mp ha).2.2.1 hr

theorem unclosed_name_not_admitted {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (m : Name) (hm : m ∈ r.reached) (hn : ¬ ClosedModuleName m) : d r ≠ .admitted :=
  fun ha => hn (((admitted_iff h r).mp ha).2.2.2.2.1.2.2.1 m hm)

theorem lean_config_refused {d : Reading → Outcome} (h : languageRecord.Meets d) (r : Reading)
    (hr : r.leanConfig = true) : d r = .refused := by
  obtain ⟨h1, -⟩ := (language_meets_iff d).mp h
  exact h1 r fun hc => by
    have := hc.2.1
    simp [hr] at this

abbrev GateRun : Type := Outcome → Bool → Regula.Closed.Verdict → Report × List Step

def fullGateRecord : IntentRecord GateRun where
  shape := .function Outcome (fun _ => Bool → Regula.Closed.Verdict → Report × List Step)
  dom := []
  props := [
    ⟨"a refused project is compiled by nothing",
      fun g => ∀ b v, g .refused b v = (.refused, [.read])⟩,
    ⟨"a project that could not be read is compiled by nothing",
      fun g => ∀ b v, g .incomplete b v = (.incomplete, [.read])⟩,
    ⟨"a project with only the proof verdict is compiled by nothing, and is told so",
      fun g => ∀ b v, g .proofOnly b v = (.proofOnly, [.read])⟩,
    ⟨"an admitted project gets the full verdict, from the rules on a build that ended with 0",
      fun g => ∀ v, g .admitted true v = (.full v, [.read, .build, .rules])⟩,
    ⟨"an admitted project whose build failed gets a full verdict of failure",
      fun g => ∀ v, g .admitted false v = (.full .fail, [.read, .build])⟩]
  vocab := []

theorem fullGate_meets_iff (g : GateRun) :
    fullGateRecord.Meets g ↔
      (∀ b v, g .refused b v = (.refused, [.read])) ∧
      (∀ b v, g .incomplete b v = (.incomplete, [.read])) ∧
      (∀ b v, g .proofOnly b v = (.proofOnly, [.read])) ∧
      (∀ v, g .admitted true v = (.full v, [.read, .build, .rules])) ∧
      (∀ v, g .admitted false v = (.full .fail, [.read, .build])) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, fullGateRecord]

theorem fullGate_o5 : O5 fullGateRecord .eq := by
  rw [o5_correct]
  intro u v hu hv
  obtain ⟨u1, u2, u3, u4, u5⟩ := (fullGate_meets_iff u).mp ⟨hu.1, hu.2⟩
  obtain ⟨v1, v2, v3, v4, v5⟩ := (fullGate_meets_iff v).mp ⟨hv.1, hv.2⟩
  funext o b w
  cases o <;> cases b <;> simp_all

theorem fullGate_o4 : O4 fullGateRecord := o4_function _ rfl

theorem fullGate_o2 : O2 fullGateRecord := by
  rw [o2_correct]
  exact ⟨⟨fun _ _ _ => (.incomplete, []), by simp [fullGateRecord]⟩, by simp [fullGateRecord]⟩

theorem fullGate_o3 : O3 fullGateRecord := by
  rw [o3_correct]
  intro p hp
  simp only [fullGateRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨fun _ _ _ => (.incomplete, []), fun h => ?_⟩
  · simpa using h true .pass
  · simpa using h true .pass
  · simpa using h true .pass
  · simpa using h .pass
  · simpa using h .pass

theorem build_only_after_check {g : GateRun} (h : fullGateRecord.Meets g) (o b v) :
    Step.build ∈ (g o b v).2 → o = .admitted ∧ (g o b v).2.head? = some .read := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := (fullGate_meets_iff g).mp h
  cases o <;> cases b <;> simp_all

theorem full_needs_no_mathlib {d : Reading → Outcome} {g : GateRun} (hd : languageRecord.Meets d)
    (hg : fullGateRecord.Meets g) (r : Reading) (b v w)
    (hf : (g (d r) b v).1 = .full w) : ¬ MathlibReached r := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := (fullGate_meets_iff g).mp hg
  have ha : d r = .admitted := by
    cases ho : d r <;> rw [ho] at hf <;> cases b <;> simp_all
  exact ((admitted_iff hd r).mp ha).2.2.2.1

structure LeanBehaviour where
  Elaborates : FileRead → List Syntax → Prop
  NoProjectCode : List Syntax → Prop
  h1 : ∀ r, Inside r → ∀ f ∈ r.files, Elaborates f f.commands
  h2 : ∀ scopedParsers (ts : List Syntax), (∀ t ∈ ts, TreeAdmitted scopedParsers t) → NoProjectCode ts

theorem admitted_runs_no_project_code (L : LeanBehaviour) {d : Reading → Outcome}
    (hd : languageRecord.Meets d) (r : Reading) (ha : d r = .admitted) :
    ∀ f ∈ r.files, ∃ ts, L.Elaborates f ts ∧ L.NoProjectCode ts := by
  have hi := (admitted_iff hd r).mp ha
  intro f hf
  have hadm : FileAdmitted f := hi.2.2.2.2.2 f hf
  exact ⟨f.commands, L.h1 r hi f hf, L.h2 f.scopedParsers f.commands hadm.2.2.2.2⟩

end RegulaSpecification.Language
