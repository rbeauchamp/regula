/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.PreparationReader
import RegulaSpecification.Proofs.ShellParts

/-!
# Preparation by the actual loaders

Every search-path consumer follows the setter supplied by its own load, including when the consumer
fails. These are exact traces of `inputOf`, `loadTree` and `loadPlain`, with arbitrary responses.
-/

namespace RegulaSpecification.Effects
open Lean (Name)
open System (FilePath)
open Regula.Effect Regula.Reader Regula.Shell Regula.Language
variable {L E : Type}

theorem quiet_of_saying {t : List (Event L E)} (h : ∀ e ∈ t, e.isOnlySaying = true) : Quiet t := by
  intro e he
  have hs := h e he
  obtain ⟨op, response⟩ := e
  cases op <;> first | trivial | cases hs

theorem InputPreparation.prepend {before t : List (Event L E)} {root : Root L}
    (hq : Quiet before) (h : InputPreparation root t) : InputPreparation root (before ++ t) := by
  rcases h with h | ⟨pre, rest, rfl, hp, hr⟩
  · exact .inl (hq.append h)
  · exact .inr ⟨before ++ pre, rest, by simp [List.append_assoc], hq.append hp, hr⟩

theorem InputPreparation.appendQuiet {t after : List (Event L E)} {root : Root L}
    (h : InputPreparation root t) (hq : Quiet after) : InputPreparation root (t ++ after) := by
  rcases h with h | ⟨pre, rest, rfl, hp, hr⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, rest ++ after, by simp, hp, fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hr e he
    · exact .inl (hq e he)

theorem RulesPreparation.appendQuiet {t after : List (Event L E)} {sysroot : String} {tree : FilePath}
    (h : RulesPreparation sysroot tree t) (hq : Quiet after) : RulesPreparation sysroot tree (t ++ after) := by
  rcases h with h | ⟨pre, real, response, rest, rfl, hp, hm, hr⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, real, response, rest ++ after, by simp, hp, hm, ?_⟩
    cases response with
    | error error => exact hr.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hr.append hq
      | some root => exact hr.appendQuiet hq

theorem PlainPreparation.appendQuiet {t after : List (Event L E)}
    (h : PlainPreparation t) (hq : Quiet after) : PlainPreparation (t ++ after) := by
  rcases h with h | ⟨pre, sysroot, dir, response, rest, rfl, hp, hs, hd, hr⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, sysroot, dir, response, rest ++ after, by simp, hp, hs, hd, ?_⟩
    cases response with
    | error error => exact hr.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hr.append hq
      | some root => exact hr.appendQuiet hq

theorem observing_readModules (a b : FilePath) (names : List Name) :
    OnlyAIn (fun o => QuietOp o ∨ RulesSearchOp o) (readModules a b names : Attempt L E _) := by
  induction names with
  | nil => exact onlyA_pure _
  | cons name names ih =>
    exact onlyA_seq (onlyA_attempt (only_call (.inr trivial))) fun _ => onlyA_seq ih fun _ => onlyA_pure _

theorem observing_factsOf (env : Lean.Environment) (a b : FilePath) :
    OnlyAIn (fun o => QuietOp o ∨ RulesSearchOp o) (factsOf env a b : Attempt L E _) :=
  onlyA_seq (observing_readModules _ _ _) fun _ => onlyA_pure _

/-- The exact input phase cannot use a lookup or import before setting this root's search path. -/
theorem inputOf_preparation {root : Root L} {p : Regula.Closed.Profile} {t : List (Event L E)}
    {b : Except String Regula.Closed.Input} (h : Runs (inputOf root p : Attempt L E _).run t b) :
    InputPreparation root t := by
  rw [inputOf] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  have hq : Quiet first := quiet_defaultModules _ _ _ _ hf
  cases response with
  | error error => obtain ⟨rfl, -⟩ := hl; exact .inl (by simpa using hq)
  | ok modules =>
    obtain ⟨setting, rest, response, rfl, hset, hr⟩ := runs_attempt_bind_iff.mp hl
    obtain ⟨u, hc, rfl⟩ := runs_lift_iff.mp hset
    obtain rfl := runs_call_iff.mp hc
    cases u
    refine .inr ⟨first, rest, rfl, hq, ?_⟩
    exact (onlyA_seq (onlyA_attempt (only_call
      (o := .importForRules (modules.map (·.1)).toArray) (.inr trivial))) fun env =>
        onlyA_seq (observing_factsOf env root.leanLib root.rootLib) fun _ => only_pure _) _ _ hr

/-- The actual reload makes exactly the load request directed by the tree's real-path response. -/
theorem loadTree_preparation {sysroot : String} {tree : FilePath} {p : Regula.Closed.Profile}
    {t : List (Event L E)} {b : Except String Regula.Closed.Input}
    (h : Runs (loadTree sysroot tree p : Attempt L E _).run t b) : RulesPreparation sysroot tree t := by
  rw [loadTree] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hf
  obtain rfl := runs_call_iff.mp hc
  have hq (r) : Quiet ([⟨.realPath tree, r⟩] : List (Event L E)) := by
    intro e he; obtain rfl := List.mem_singleton.mp he; trivial
  cases r with
  | error error => obtain ⟨rfl, -⟩ := hl; exact .inl (by simpa using hq (.error error))
  | ok real =>
    obtain ⟨loading, rest, response, rfl, hload, hr⟩ := runs_attempt_bind_iff.mp hl
    obtain ⟨a, b', r, rfl, ha, hb⟩ := runs_bind_iff.mp hload
    obtain rfl := runs_call_iff.mp ha
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp hb
    refine .inr ⟨[⟨.realPath tree, .ok real⟩], real, r, rest, by simp, hq _, by simp, ?_⟩
    cases r with
    | error error => obtain ⟨rfl, -⟩ := hr; exact quiet_nil
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => obtain ⟨rfl, -⟩ := hr; exact quiet_nil
      | some root => exact inputOf_preparation hr

/-- The plain loader's prefix provides its requested workspace and toolchain. -/
theorem loadPlain_preparation {prior t : List (Event L E)} {p : Regula.Closed.Profile}
    {b : Except String Regula.Closed.Input} (hq : Quiet prior)
    (h : Runs (loadPlain p : Attempt L E _).run t b) : PlainPreparation (prior ++ t) := by
  rw [loadPlain] at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r, rfl, hok, -⟩ := requireEnv_spec hf
  have henv (r) : Quiet ([⟨.getEnv "LEAN_SYSROOT", r⟩] : List (Event L E)) := by
    intro e he; obtain rfl := List.mem_singleton.mp he; trivial
  cases response with
  | error error => obtain ⟨rfl, -⟩ := hl; exact .inl (by simpa using hq.append (henv r))
  | ok sysroot =>
    obtain rfl := hok sysroot rfl
    obtain ⟨second, last₂, response₂, rfl, hf₂, hl₂⟩ := runs_attempt_bind_iff.mp hl
    obtain ⟨r₂, hc₂, rfl⟩ := runs_attempt_iff.mp hf₂
    obtain rfl := runs_call_iff.mp hc₂
    have hdir (r) : Quiet ([⟨.realPath ".", r⟩] : List (Event L E)) := by
      intro e he; obtain rfl := List.mem_singleton.mp he; trivial
    cases r₂ with
    | error error =>
      obtain ⟨rfl, -⟩ := hl₂
      exact .inl (by simpa [List.append_assoc] using (hq.append (henv (some sysroot))).append (hdir (.error error)))
    | ok dir =>
      obtain ⟨loading, rest, response₃, rfl, hload, hr⟩ := runs_attempt_bind_iff.mp hl₂
      obtain ⟨a, b', r₃, rfl, ha, hb⟩ := runs_bind_iff.mp hload
      obtain rfl := runs_call_iff.mp ha
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp hb
      refine .inr ⟨prior ++ [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩, ⟨.realPath ".", .ok dir⟩],
        sysroot, dir, r₃, rest, by simp, ?_, by simp [SysrootIs], by simp, ?_⟩
      · simpa using (hq.append (henv (some sysroot))).append (hdir (.ok dir))
      · cases r₃ with
        | error error => obtain ⟨rfl, -⟩ := hr; exact quiet_nil
        | ok pair =>
          obtain ⟨root, log⟩ := pair
          cases root with
          | none => obtain ⟨rfl, -⟩ := hr; exact quiet_nil
          | some root =>
            obtain ⟨installation, tail, response₄, rfl, hi, ht⟩ := runs_attempt_bind_iff.mp hr
            obtain ⟨⟨program, lakeLib⟩, hc, rfl⟩ := runs_lift_iff.mp hi
            obtain rfl := runs_call_iff.mp hc
            apply InputPreparation.prepend
              (show Quiet ([⟨.lakeInstall sysroot, (program, lakeLib)⟩] : List (Event L E)) from by
                intro e he; obtain rfl := List.mem_singleton.mp he; trivial)
            obtain ⟨environment, final, response₅, rfl, he, hfinal⟩ := runs_attempt_bind_iff.mp ht
            have hqe : Quiet environment := quiet_requireEnv _ _ _ _ he
            apply InputPreparation.prepend hqe
            cases response₅ with
            | error error => obtain ⟨rfl, -⟩ := hfinal; exact .inl quiet_nil
            | ok received =>
              dsimp only at hfinal
              split at hfinal
              · exact inputOf_preparation hfinal
              · obtain ⟨rfl, -⟩ := runs_attempt_throw_iff.mp hfinal; exact .inl quiet_nil

end RegulaSpecification.Effects
