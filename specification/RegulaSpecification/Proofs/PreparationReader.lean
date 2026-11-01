/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.PreparationTrace

/-!
# Preparation by the actual reader

These proofs compose the exact events of the reader's parts. The prefix parameters contain only events
already received; they supply the source reads and module names used by later copy steps.
-/

namespace RegulaSpecification.Effects
open Lean (Name)
open System (FilePath)
open Regula.Effect Regula.Reader Regula.Language RegulaSpecification.Language
variable {L E : Type}

theorem ReadingLoaded.prepend {prior before t : List (Event L E)} {project tree : FilePath} {root : Root L}
    (hq : Quiet before) (h : ReadingLoaded (prior ++ before) project tree root t) :
    ReadingLoaded prior project tree root (before ++ t) := by
  rcases h with h | ⟨pre, rest, modules, rfl, hp, hm, hc⟩
  · exact .inl (hq.append h)
  · exact .inr ⟨before ++ pre, rest, modules, by simp [List.append_assoc], hq.append hp,
      by simpa [List.append_assoc] using hm, by simpa [List.append_assoc] using hc⟩

theorem ReadingLoad.prepend {prior before t : List (Event L E)} {sysroot : String} {project tree : FilePath}
    (hq : Quiet before) (h : ReadingLoad (prior ++ before) sysroot project tree t) :
    ReadingLoad prior sysroot project tree (before ++ t) := by
  rcases h with h | ⟨pre, response, rest, rfl, hp, hc⟩
  · exact .inl (hq.append h)
  · exact .inr ⟨before ++ pre, response, rest, by simp [List.append_assoc], hq.append hp,
      by simpa [List.append_assoc] using hc⟩

theorem ReadingLoaded.appendQuiet {prior t after : List (Event L E)} {project tree : FilePath} {root : Root L}
    (h : ReadingLoaded prior project tree root t) (hq : Quiet after) :
    ReadingLoaded prior project tree root (t ++ after) := by
  rcases h with h | ⟨pre, rest, modules, rfl, hp, hm, hc⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, rest ++ after, modules, by simp, hp, hm, ?_⟩
    exact hc.append (.observations _ fun e he => .inl (hq e he))

theorem ReadingLoad.appendQuiet {prior t after : List (Event L E)} {sysroot : String} {project tree : FilePath}
    (h : ReadingLoad prior sysroot project tree t) (hq : Quiet after) :
    ReadingLoad prior sysroot project tree (t ++ after) := by
  rcases h with h | ⟨pre, response, rest, rfl, hp, hc⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, response, rest ++ after, by simp, hp, ?_⟩
    cases response with
    | error error => exact hc.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hc.append hq
      | some root => exact hc.appendQuiet hq

theorem ConfigCopies.appendQuiet {prior t after : List (Event L E)} {sysroot : String}
    {project tree : FilePath} {copies} (h : ConfigCopies sysroot project tree copies prior t) (hq : Quiet after) :
    ConfigCopies sysroot project tree copies prior (t ++ after) := by
  induction h with
  | done h => exact .done (h.appendQuiet hq)
  | stopped h => exact .stopped (h.append hq)
  | failed hp hc hr => simpa [List.append_assoc] using ConfigCopies.failed hp hc (hr.append hq)
  | next hp hc hr ih => simpa [List.append_assoc] using ConfigCopies.next hp hc ih

theorem ReadingPreparation.appendQuiet {t after : List (Event L E)} {dir treeDir : FilePath}
    (h : ReadingPreparation t dir treeDir) (hq : Quiet after) : ReadingPreparation (t ++ after) dir treeDir := by
  rcases h with h | ⟨project, tree, sysroot, text, before, rest, rfl, hp, h1, h2, h3, h4, hc⟩
  · exact .inl (h.append hq)
  · exact .inr ⟨project, tree, sysroot, text, before, rest ++ after, by simp [List.append_assoc],
      hp, h1, h2, h3, h4, hc.appendQuiet hq⟩

/-- `readFiles` meets `ReadingLoaded`: only observations, or its root's toolchain path set once, before every lookup, parser
import and module copy, with no other set after it. Each copy is of a needed name's file, by a text the prefix read. -/
theorem readFiles_preparation {config : List (FilePath × String)} {prior t : List (Event L E)} {project tree : FilePath}
    {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {b : Except String (Reading × List (Name × Source))}
    (hm : DefaultModules prior root root.defaultTargets modules)
    (h : Runs (readFiles config project tree root modules start : Attempt L E _).run t b) :
    ReadingLoaded prior project tree root t := by
  rw [readFiles] at h
  obtain ⟨a, rest, response, rfl, ha, hr⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨u, hu, rfl⟩ := runs_lift_iff.mp ha
  obtain rfl := runs_call_iff.mp hu
  cases u
  refine .inr ⟨[], rest, modules, rfl, quiet_nil, by simpa using hm, ?_⟩
  obtain ⟨first, last, response, rfl, hfirst, hlast⟩ := runs_attempt_bind_iff.mp hr
  have hq : Quiet first := quiet_realPaths _ _ _ hfirst
  apply ModuleCopies.append (.observations _ fun e he => .inl (hq e he))
  cases response with
  | error error => obtain ⟨rfl, -⟩ := hlast; exact .nil
  | ok dirs =>
    obtain ⟨walkTrace, parseTrace, response, rfl, hw, hp⟩ := runs_attempt_bind_iff.mp hlast
    obtain ⟨w, hw', rfl⟩ := runs_lift_iff.mp hw
    obtain ⟨hobs, hsrc⟩ := walk_preparation (prior := prior ++ [] ++ [⟨.setSearchPath root.toolchain, ()⟩] ++ first)
      project tree root modules dirs _ _ _ (fun m h => .root h) hw' (by simp)
    apply ModuleCopies.append (.observations _ hobs)
    dsimp only at hp
    split at hp
    · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hp; exact .nil
    · obtain ⟨first', last', response', rfl, hfirst', hlast'⟩ := runs_attempt_bind_iff.mp hp
      apply ModuleCopies.append (.observations _ (observing_parseFiles _ _ _ _ _ _ hfirst'))
      cases response' with
      | error error => obtain ⟨rfl, -⟩ := hlast'; exact .nil
      | ok files =>
        dsimp only at hlast'
        split at hlast'
        · obtain ⟨c1, c2, cr, rfl, hc, htail⟩ := runs_attempt_bind_iff.mp hlast'
          have hcopies := writeSources_preparation (project := project) (root := root) (modules := modules)
            (prior := prior ++ [] ++ [⟨.setSearchPath root.toolchain, ()⟩] ++ (first ++ (walkTrace ++ first'))) (fun x hx => by
              have := hsrc x (List.mem_reverse.mp hx)
              exact ⟨Named.mono (by simp [List.append_assoc]) this.1, this.2.1,
                SourceText.mono (by simp [List.append_assoc]) this.2.2⟩) hc
          have hquiet : Quiet c2 := by
            cases cr with
            | error error => obtain ⟨rfl, -⟩ := htail; exact quiet_nil
            | ok u =>
              obtain ⟨d1, d2, dr, rfl, hd, hrest⟩ := runs_attempt_bind_iff.mp htail
              have hdq : Quiet d1 := quiet_readBack _ _ _ hd
              have hd2 : Quiet d2 := by
                cases dr with
                | error error => obtain ⟨rfl, -⟩ := hrest; exact quiet_nil
                | ok v => exact (onlyA_seq (quiet_noOtherConfig tree) fun _ => onlyA_pure _) _ _ hrest
              exact hdq.append hd2
          refine ModuleCopies.append (by simpa [List.append_assoc] using hcopies) (.observations _ fun e he => .inl (hquiet e he))
        · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hlast'
          exact .nil

/-- `readRoot` asks at most one load of the root, with only observations before it. -/
theorem readRoot_preparation {config : List (FilePath × String)} {prior t : List (Event L E)} {sysroot : String}
    {project tree : FilePath}
    {start : Reading} {b : Except String (Reading × List (Name × Source))}
    (h : Runs (readRoot config sysroot project tree start : Attempt L E _).run t b) :
    ReadingLoad prior sysroot project tree t := by
  rw [readRoot] at h
  obtain ⟨first, rest, result, rfl, hfirst, hrest⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨a, b', response, rfl, ha, hb⟩ := runs_bind_iff.mp hfirst
  obtain rfl := runs_call_iff.mp ha
  obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp hb
  refine .inr ⟨[], response, rest, by simp, quiet_nil, ?_⟩
  cases response with
  | error error => obtain ⟨rfl, -⟩ := hrest; exact quiet_nil
  | ok pair =>
    obtain ⟨root, log⟩ := pair
    cases root with
    | none => obtain ⟨rfl, -⟩ := hrest; exact quiet_nil
    | some root =>
      dsimp only [loaded] at hrest
      split at hrest
      · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hrest; exact .inl quiet_nil
      · obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp hrest
        have hq : Quiet first := quiet_defaultModules _ _ _ _ hf
        apply ReadingLoaded.prepend hq
        cases response with
        | error error => obtain ⟨rfl, -⟩ := hl; exact .inl quiet_nil
        | ok modules =>
          dsimp only at hl
          split at hl
          · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl; exact .inl quiet_nil
          · apply readFiles_preparation (h := hl)
            exact (defaultModules_spec root root.defaultTargets
              (fun e he => List.mem_append_right _ he) hf).1 modules rfl

/-- The two configuration attempts short-circuit in order; only two completed copies admit a load. -/
theorem readKeys_preparation {prior t : List (Event L E)} {sysroot text : String} {project tree : FilePath}
    {tf : Option String} {b : Except String (Reading × List (Name × Source))}
    (h : Runs (readKeys sysroot project tree tf text : Attempt L E _).run t b) :
    ConfigCopies sysroot project tree [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)]
      prior t := by
  rw [readKeys] at h
  obtain ⟨first, rest, response, rfl, hf, hr⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨response, hc, rfl⟩ := runs_lift_iff.mp hf
  obtain rfl := runs_call_iff.mp hc
  have hq : Quiet ([⟨.parseToml (Lean.Parser.mkInputContext text "lakefile.toml"), response⟩] : List (Event L E)) :=
    by intro e he; obtain rfl := List.mem_singleton.mp he; trivial
  cases response with
  | error error =>
    obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hr
    exact .stopped (by simpa using hq)
  | ok table =>
    dsimp only at hr
    split at hr
    · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hr
      exact .stopped (by simpa using hq)
    · obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp hr
      have hs := writeInTree_preparation hf
      cases response with
      | error error =>
        obtain ⟨rfl, -⟩ := hl
        simpa using ConfigCopies.failed hq hs quiet_nil
      | ok u =>
        apply ConfigCopies.next hq hs
        obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp hl
        have hs := writeInTree_preparation hf
        cases response with
        | error error =>
          obtain ⟨rfl, -⟩ := hl
          simpa using ConfigCopies.failed quiet_nil hs quiet_nil
        | ok u =>
          exact ConfigCopies.next quiet_nil hs (.done (readRoot_preparation hl))

theorem quiet_requireEnv (name why : String) : OnlyAIn QuietOp (requireEnv name why : Attempt L E _) := by
  rw [requireEnv]
  refine only_seq (only_call trivial) fun r => ?_
  cases r <;> exact only_pure _

theorem quiet_startedOutside (lakeLib project : FilePath) :
    OnlyAIn QuietOp (startedOutside lakeLib project : Attempt L E _) := by
  rw [startedOutside]
  refine onlyA_seq (onlyA_attempt (only_call trivial)) fun app => ?_
  refine onlyA_seq (quiet_realPath _) fun real => ?_
  exact onlyA_seq (quiet_requireEnv _ _) fun _ => onlyA_pure _

theorem quiet_toolchainOf (project : FilePath) : OnlyIn QuietOp (toolchainOf project : Prog L E _) := by
  rw [toolchainOf]
  refine only_seq (quiet_readExact _ _) fun r => ?_
  cases r <;> exact only_pure _

theorem quiet_existsByName (path : FilePath) : OnlyAIn QuietOp (existsByName path : Attempt L E _) := by
  rw [existsByName]
  refine only_seq (only_call trivial) fun r => ?_
  split <;> exact only_pure _

/-- At the configuration entry, every read used to authorize the copy belongs to the earlier prefix. -/
theorem readConfig_preparation {prior t : List (Event L E)} {dir treeDir project tree : FilePath}
    {sysroot : String} {tf : Option String} {b : Except String (Reading × List (Name × Source))}
    (hq : Quiet prior) (hp : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ prior)
    (ht : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ prior) (hs : SysrootIs prior sysroot)
    (h : Runs (readConfig sysroot project tree tf : Attempt L E _).run t b) :
    ReadingPreparation (prior ++ t) dir treeDir := by
  rw [readConfig] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  have hfirst : Quiet first := quiet_existsByName _ _ _ hf
  cases response with
  | error error =>
    obtain ⟨rfl, -⟩ := hl
    exact .inl (by simpa using hq.append hfirst)
  | ok present =>
    cases present with
    | true =>
      obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl
      exact .inl (by simpa using hq.append hfirst)
    | false =>
      obtain ⟨second, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp hl
      obtain ⟨r, hr, rfl⟩ := runs_lift_iff.mp hf
      have hsecond : Quiet second := quiet_readExact _ _ _ _ hr
      cases r with
      | error error =>
        obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl
        exact .inl (by simpa [List.append_assoc] using (hq.append hfirst).append hsecond)
      | ok text =>
        refine .inr ⟨project, tree, sysroot, text, prior ++ first ++ second, last,
          by simp [List.append_assoc], (hq.append hfirst).append hsecond,
          by simp [hp], by simp [ht], by simpa [SysrootIs] using
            (List.mem_append_left second (List.mem_append_left first hs)), ?_, readKeys_preparation hl⟩
        obtain ⟨real, he, -⟩ := (readExact_spec hr).1 text rfl
        simp [he]

/-- The complete reader's preparation, including stops before its configuration copies. -/
theorem readProject_preparation {prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List (Name × Source))} (hq : Quiet prior) (hs : SysrootIs prior sysroot)
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t b) :
    ReadingPreparation (prior ++ t) dir treeDir := by
  rw [readProject] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hf
  obtain rfl := runs_call_iff.mp hc
  have hfirst (r) : Quiet ([⟨.realPath dir, r⟩] : List (Event L E)) := by
    intro e he; obtain rfl := List.mem_singleton.mp he; trivial
  cases r with
  | error error =>
    obtain ⟨rfl, -⟩ := hl
    exact .inl (by simpa using hq.append (hfirst _))
  | ok project =>
    obtain ⟨second, last₂, response₂, rfl, hf₂, hl₂⟩ := runs_attempt_bind_iff.mp hl
    obtain ⟨r₂, hc₂, rfl⟩ := runs_attempt_iff.mp hf₂
    obtain rfl := runs_call_iff.mp hc₂
    have hsecond (r) : Quiet ([⟨.realPath treeDir, r⟩] : List (Event L E)) := by
      intro e he; obtain rfl := List.mem_singleton.mp he; trivial
    cases r₂ with
    | error error =>
      obtain ⟨rfl, -⟩ := hl₂
      exact .inl (by simpa [List.append_assoc] using
        (hq.append (hfirst (.ok project))).append (hsecond (.error error)))
    | ok tree =>
      obtain ⟨third, last₃, response₃, rfl, hf₃, hl₃⟩ := runs_attempt_bind_iff.mp hl₂
      obtain ⟨⟨program, lakeLib⟩, hc₃, rfl⟩ := runs_lift_iff.mp hf₃
      obtain rfl := runs_call_iff.mp hc₃
      have hthird : Quiet ([⟨.lakeInstall sysroot, (program, lakeLib)⟩] : List (Event L E)) := by
        intro e he; obtain rfl := List.mem_singleton.mp he; trivial
      obtain ⟨fourth, last₄, response₄, rfl, hf₄, hl₄⟩ := runs_attempt_bind_iff.mp hl₃
      have hfourth : Quiet fourth := quiet_startedOutside _ _ _ _ hf₄
      let before := prior ++ [⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩,
        ⟨.lakeInstall sysroot, (program, lakeLib)⟩] ++ fourth
      have hbefore : Quiet before := by
        simpa [before, List.append_assoc] using
          (((hq.append (hfirst (.ok project))).append (hsecond (.ok tree))).append hthird).append hfourth
      cases response₄ with
      | error error =>
        obtain ⟨rfl, -⟩ := hl₄
        exact .inl (by simpa [before, List.append_assoc] using hbefore)
      | ok outside =>
        obtain ⟨fifth, last₅, response₅, rfl, hf₅, hl₅⟩ := runs_attempt_bind_iff.mp hl₄
        obtain ⟨tf, htf, rfl⟩ := runs_lift_iff.mp hf₅
        have hfifth : Quiet fifth := quiet_toolchainOf _ _ _ htf
        have hprefix := hbefore.append hfifth
        dsimp only at hl₅
        split at hl₅
        · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl₅
          exact .inl (by simpa [before, List.append_assoc] using hprefix)
        · split at hl₅
          · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl₅
            exact .inl (by simpa [before, List.append_assoc] using hprefix)
          · have hp : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ before ++ fifth := by simp [before]
            have ht : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ before ++ fifth := by simp [before]
            have hs' : SysrootIs (before ++ fifth) sysroot := by
              simp only [SysrootIs] at hs ⊢
              simp [before, hs]
            simpa [before, List.append_assoc] using readConfig_preparation hprefix hp ht hs' hl₅

theorem read_preparation {prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List String)} (hq : Quiet prior) (hs : SysrootIs prior sysroot)
    (h : Runs (read sysroot dir treeDir : Attempt L E _).run t b) :
    ReadingPreparation (prior ++ t) dir treeDir := by
  rw [Regula.Reader.read] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  have hp := readProject_preparation hq hs hf
  cases response with
  | error error => obtain ⟨rfl, -⟩ := hl; simpa using hp
  | ok pair => obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp hl; simpa using hp

end RegulaSpecification.Effects
