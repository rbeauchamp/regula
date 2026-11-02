/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderOnly
import RegulaSpecification.Proofs.ShellLoad

/-!
# The parts of a run: what it prints, and the loads of a finished build

For every response, about the definitions in `Regula.Shell`.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open System (FilePath)
open Regula.Effect
open Regula.Reader
open Regula.Shell
open Regula.Language
open Regula.Closed (detailText)

variable {L E : Type}

/-- Events that only say something, and each line a detail. -/
def Details (t : List (Event L E)) : Prop :=
  (∀ e ∈ t, e.isOnlySaying = true) ∧ ∀ l ∈ printed t, IsDetail l

theorem printed_append (a b : List (Event L E)) : printed (a ++ b) = printed a ++ printed b := by
  simp [printed]

/-- Splitting the actual requested character stream gives exactly `printed`, followed by the empty tail
after the final LF. This includes embedded separators, empty messages and consecutive print calls. -/
theorem serialized_split (t : List (Event L E)) :
    (serialized t).splitOn '\n' = (printed t).map String.toList ++ [[]] := by
  unfold serialized printed
  generalize t.filterMap Event.line? = texts
  induction texts with
  | nil => simp
  | cons text rest ih =>
    simp only [List.flatMap_cons, String.toList_push, List.append_assoc, List.singleton_append] at ih ⊢
    rw [List.splitOn_append_cons_self]
    simpa [List.map_flatMap, Function.comp_def, List.map_map, List.append_assoc] using
      congrArg ((text.toList.splitOn '\n') ++ ·) ih

/-- No LF or CR survives diagnostic serialization, for every input string. -/
theorem detailText_no_break (s : String) :
    '\n' ∉ (detailText s).toList ∧ '\r' ∉ (detailText s).toList := by
  simp only [detailText, String.toList_ofList, List.mem_flatMap]
  constructor <;> rintro ⟨c, _, hc⟩ <;>
    split at hc <;> (try split at hc) <;> simp_all <;> subst c <;> contradiction

/-- A diagnostic's requested physical lines consist of its one prefixed line. -/
theorem detailText_lines (s : String) :
    (("  " ++ detailText s).toList.splitOn '\n').map String.ofList = ["  " ++ detailText s] := by
  rw [List.splitOn_eq_singleton (by simpa using (detailText_no_break s).1)]
  simp only [List.map_singleton, String.ofList_toList]

theorem details_nil : Details (L := L) (E := E) [] := by
  simp [Details, printed]

theorem details_append {a b : List (Event L E)} (ha : Details a) (hb : Details b) : Details (a ++ b) := by
  refine ⟨fun e he => ?_, fun l hl => ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact ha.1 e he
    · exact hb.1 e he
  · rw [printed_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact ha.2 l hl
    · exact hb.2 l hl

theorem acted_of_saying {e : Event L E} (h : e.isOnlySaying = true) : e.acted? = none := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | rfl | cases h

theorem say_spec {s : String} {t : List (Event L E)} {u : Unit} (h : Runs (say s : Prog L E Unit) t u) :
    Details t := by
  unfold say at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨rfl, -⟩ := runs_pure_iff.mp h₂
  refine ⟨fun e he => ?_, fun l hl => ?_⟩
  · simp only [List.append_nil, List.mem_singleton] at he
    subst he
    rfl
  · have hl' : l ∈ (("  " ++ detailText s).toList.splitOn '\n').map String.ofList := by
      simpa only [printed, Event.line?, List.append_nil, List.filterMap_cons, List.filterMap_nil,
        List.flatMap_cons, List.flatMap_nil, List.nil_append] using hl
    rw [detailText_lines] at hl'
    exact ⟨detailText s, List.mem_singleton.mp hl'⟩

theorem sayAll_spec {ls : List String} {t : List (Event L E)} {u : Unit}
    (h : Runs (sayAll ls : Prog L E Unit) t u) : Details t := by
  induction ls generalizing t with
  | nil =>
    rw [sayAll] at h
    obtain ⟨rfl, -⟩ := runs_pure_iff.mp h
    exact details_nil
  | cons l ls ih =>
    rw [sayAll] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
    exact details_append (say_spec h₁) (ih h₂)

/-- The end of a run: its last line, and nothing after it. -/
theorem finish_spec {text : String} {code c : UInt32} {t : List (Event L E)}
    (h : Runs (finish text code : Prog L E UInt32) t c) :
    c = code ∧ ∃ r, t = [⟨.println text, r⟩] := by
  unfold finish at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
  exact ⟨rfl, r, rfl⟩

/-- A list with a last line after `pre` ends with that line, when `pre` holds only details and `line` holds no LF. -/
theorem endsWith_of {pre : List (Event L E)} {line : String} {r : Resp (Op.println line : Op L E)}
    (hn : '\n' ∉ line.toList) (h : ∀ l ∈ printed pre, IsDetail l) :
    EndsWith (pre ++ [⟨.println line, r⟩]) line :=
  ⟨pre, r, rfl, hn, h⟩

/-- Every proof-verdict label is one physical line. -/
theorem proofLine_no_break (v : Regula.Closed.Verdict) : '\n' ∉ v.proofLine.toList := by
  cases v <;> decide

set_option maxRecDepth 4096 in
/-- Every full-gate label is one physical line. -/
theorem reportLabel_no_break (r : Report) : '\n' ∉ r.label.toList := by
  cases r with
  | full v => cases v <;> decide
  | refused | incomplete | proofOnly => decide

/-- A pass names its subject at the end of the line, and a subject with no LF leaves it one physical line. -/
theorem proofLineOn_no_break (s : String) (v : Regula.Closed.Verdict) :
    '\n' ∉ (v.proofLineOn s).toList := by
  cases v with
  | pass =>
    have hs := (detailText_no_break s).1
    have hp := proofLine_no_break .pass
    simp only [Regula.Closed.Verdict.proofLineOn, String.toList_append, List.mem_append, not_or]
    exact ⟨⟨hp, by decide⟩, hs⟩
  | fail | incomplete => exact proofLine_no_break _

/-- The same of the full gate's last line. -/
theorem reportLabelOn_no_break (s : String) (r : Report) : '\n' ∉ (r.labelOn s).toList := by
  rcases r with (_ | _ | _) | _ | _ | _
  · have hs := (detailText_no_break s).1
    have hp := reportLabel_no_break (.full .pass)
    simp only [Report.labelOn, String.toList_append, List.mem_append, not_or]
    exact ⟨⟨hp, by decide⟩, hs⟩
  all_goals exact reportLabel_no_break _

/-- The serialized output ends in the one verdict line; every preceding physical line is a detail.
The final empty chunk is the position after `println`'s terminating LF, not another output line. -/
theorem endsWith_serialized {t : List (Event L E)} {line : String} (h : EndsWith t line) :
    ∃ pre : List String, (serialized t).splitOn '\n' = pre.map String.toList ++ [line.toList, []] ∧
      ∀ l ∈ pre, IsDetail l := by
  obtain ⟨pre, r, rfl, hn, hd⟩ := h
  refine ⟨printed pre, ?_, hd⟩
  rw [serialized_split, printed_append]
  simp [printed, Event.line?, List.splitOn_eq_singleton hn, List.append_assoc]

theorem finishProof_spec {report : Regula.Closed.Report} {c : UInt32} {t : List (Event L E)}
    (h : Runs (finishProof report : Prog L E UInt32) t c) :
    c = report.verdict.exitCode ∧ EndsWith t report.verdict.proofLine ∧ ∀ e ∈ t, e.isOnlySaying = true := by
  unfold finishProof at h
  obtain ⟨t₁, t₂, u, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  have hd := sayAll_spec h₁
  obtain ⟨hc, r, rfl⟩ := finish_spec h₂
  refine ⟨hc, endsWith_of (proofLine_no_break _) hd.2, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hd.1 e he
  · have : e = _ := List.mem_singleton.mp he
    subst this
    rfl

/-- The end of a run of the proof verdict on a subject. -/
theorem finishPlain_spec {subject : FilePath} {report : Regula.Closed.Report} {c : UInt32} {t : List (Event L E)}
    (h : Runs (finishPlain subject report : Prog L E UInt32) t c) :
    c = report.verdict.exitCode ∧ EndsWith t (report.verdict.proofLineOn subject.toString) ∧
      ∀ e ∈ t, e.isOnlySaying = true := by
  unfold finishPlain at h
  obtain ⟨t₁, t₂, u, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  have hd := sayAll_spec h₁
  obtain ⟨hc, r, rfl⟩ := finish_spec h₂
  refine ⟨hc, endsWith_of (proofLineOn_no_break _ _) hd.2, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hd.1 e he
  · have : e = _ := List.mem_singleton.mp he
    subst this
    rfl

/-- An event that only says something is no failure. -/
theorem not_failed_of_saying {e : Event L E} (h : e.isOnlySaying = true) : ¬ e.failed := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | exact id | cases h

/-! ## The loads of a finished build -/

theorem requireEnv_spec {name why : String} {t : List (Event L E)} {b : Except String String}
    (h : Runs (requireEnv name why : Attempt L E String).run t b) :
    ∃ r, t = [⟨.getEnv name, r⟩] ∧ (∀ v, b = .ok v → r = some v) ∧ ((∃ e, b = .error e) → r = none) := by
  rw [requireEnv] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  refine ⟨r, ?_⟩
  cases r with
  | some value =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    exact ⟨rfl, fun v he => (by cases he; rfl), fun ⟨e, he⟩ => (by cases he)⟩
  | none =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    exact ⟨rfl, fun v he => (by cases he), fun _ => rfl⟩

/-- `loaded` gives a root only from Lake's load of it, and otherwise says that the load failed. -/
theorem loaded_spec {what : String} {r : Except String (Option (Root L) × List String)} :
    (∀ root, loaded what r = .ok root → ∃ log, r = .ok (some root, log)) ∧
      ∀ why, loaded what r = .error why →
        (∃ e, r = .error e) ∨ ∃ log, r = .ok (none, log) := by
  cases r with
  | error e => exact ⟨fun _ he => (by cases he), fun _ _ => .inl ⟨e, rfl⟩⟩
  | ok v =>
    obtain ⟨o, log⟩ := v
    cases o with
    | none => exact ⟨fun _ he => (by cases he), fun _ _ => .inr ⟨log, rfl⟩⟩
    | some root =>
      refine ⟨fun root' he => ?_, fun _ he => (by cases he)⟩
      cases he
      exact ⟨log, rfl⟩

/-- `loadPlain`: the load of the workspace that Lake dispatched. A load that gives an input received no failed answer, and its lookups and imports
name the search path of what Lake's load gave. -/
theorem loadPlain_spec {T prior t : List (Event L E)} {p : Regula.Closed.Profile}
    {b : Except String (FilePath × Regula.Closed.Input)} (hT : t.Sublist T) (hq : Quiet prior)
    (h : Runs (loadPlain p : Attempt L E _).run t b) :
    Loaded PlainRoot PlainReason T p (b.map (·.2)) ∧
      (∀ d i, b = .ok (d, i) → ((⟨.realPath ".", .ok d⟩ : Event L E) ∈ T ∧
        ∃ sysroot root log, (⟨.loadWorkspace sysroot d, .ok (some root, log)⟩ : Event L E) ∈ T ∧ PlainRoot T root) ∧ Clean t) ∧
      PlainPreparation (prior ++ t) := by
  unfold loadPlain at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨e₁, rfl, v1, v2⟩ := requireEnv_spec h₁
  have hT' : (([⟨.getEnv "LEAN_SYSROOT", e₁⟩] : List (Event L E)) ++ t₂).Sublist T := hT
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT'
  have hmem₁ : (⟨.getEnv "LEAN_SYSROOT", e₁⟩ : Event L E) ∈ T := hT'.subset (by simp)
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    have he : e₁ = none := v2 ⟨why, rfl⟩
    subst he
    exact ⟨.inr ⟨.noSysroot hmem₁, why, rfl⟩, (fun _ _ he => by cases he),
      .inl (by simpa using hq.append (quiet_one (o := .getEnv "LEAN_SYSROOT") (r := none) trivial))⟩
  | ok sysroot =>
    have he : e₁ = some sysroot := v1 sysroot rfl
    subst he
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₅, h₅, rfl⟩ := runs_attempt_iff.mp h₃
    obtain rfl := runs_call_iff.mp h₅
    have hT₄ : t₄.Sublist T := (List.sublist_append_right _ _).trans hT₂
    cases r₅ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₄
      exact ⟨.inr ⟨.noDirectory (e := e) (hT₂.subset (by simp)), _, rfl⟩, (fun _ _ he => by cases he),
        .inl (by simpa using hq.append (by quiet_events : Quiet ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩, ⟨.realPath ".", .error e⟩] : List (Event L E))))⟩
    | ok dir =>
      obtain ⟨t₅, t₆, r₆, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₄
      obtain ⟨t₇, t₈, r₈, rfl, h₈, h₉⟩ := runs_bind_iff.mp h₆
      obtain rfl := runs_call_iff.mp h₈
      obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₉
      have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
      have hmemLoad : (⟨.loadWorkspace sysroot dir, r₈⟩ : Event L E) ∈ T := hT₄.subset (by simp)
      have hpre : Quiet (prior ++ [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩, ⟨.realPath ".", .ok dir⟩]) :=
        hq.append (by quiet_events)
      obtain ⟨l1, l2⟩ := loaded_spec (what := "the workspace") (r := r₈)
      cases hl : loaded "the workspace" r₈ with
      | error why =>
        rw [hl] at h₇
        obtain ⟨rfl, rfl⟩ := h₇
        refine ⟨.inr ⟨.load hmem₁ (hT₂.subset (by simp)) hmemLoad (l2 why hl), why, rfl⟩, (fun _ _ he => by cases he), ?_⟩
        rcases l2 why hl with ⟨e, rfl⟩ | ⟨log, rfl⟩
        · exact .inr ⟨_, sysroot, dir, .error e, [], by simp [List.append_assoc], hpre, by simp [SysrootIs], by simp, quiet_nil⟩
        · exact .inr ⟨_, sysroot, dir, .ok (none, log), [], by simp [List.append_assoc], hpre, by simp [SysrootIs], by simp, quiet_nil⟩
      | ok root =>
        rw [hl] at h₇
        obtain ⟨log, rfl⟩ := l1 root hl
        have hprep {u : List (Event L E)} (hu : InputPreparation root u) : PlainPreparation (prior ++ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++
            ([⟨.realPath ".", .ok dir⟩] ++ ([⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩] ++ u)))) :=
          .inr ⟨_, sysroot, dir, .ok (some root, log), u, by simp [List.append_assoc], hpre, by simp [SysrootIs], by simp, hu⟩
        obtain ⟨t₁₁, t₁₂, r₁₂, rfl, h₁₃, h₁₄⟩ := runs_attempt_bind_iff.mp h₇
        obtain ⟨e₂, rfl, w1, w2⟩ := requireEnv_spec h₁₃
        have hmemEnv : (⟨.getEnv "LEAN_PATH", e₂⟩ : Event L E) ∈ T := hT₆.subset (by simp)
        have hT₁₂ : t₁₂.Sublist T := (List.sublist_append_right _ _).trans hT₆
        have hqe : Quiet ([⟨.getEnv "LEAN_PATH", e₂⟩] : List (Event L E)) := quiet_one trivial
        cases r₁₂ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₁₄
          have he : e₂ = none := w2 ⟨why, rfl⟩
          subst he
          exact ⟨.inr ⟨.noSearchPath hmemEnv, why, rfl⟩, (fun _ _ he => by cases he),
            by simpa using hprep (u := [⟨.getEnv "LEAN_PATH", none⟩]) (InputPreparation.prepend (t := []) hqe (fun e he => by cases he))⟩
        | ok received =>
          have he : e₂ = some received := w1 received rfl
          subst he
          dsimp only at h₁₄
          split at h₁₄
          · rename_i hdis
            obtain ⟨tI, tP, rI, rfl, hI, hP⟩ := runs_attempt_bind_iff.mp h₁₄
            obtain ⟨o1, o2⟩ := inputOf_spec ((List.sublist_append_left _ _).trans hT₁₂) hI
            have hroot : PlainRoot T root := ⟨sysroot, dir, log, received, hmem₁, hmemLoad,
              hT₂.subset (by simp), hmemEnv, (dispatchedFrom_eq_true_iff _ _).mp (by simpa using hdis)⟩
            have hend : tP = [] ∧ b.map (·.2) = rI ∧ ∀ d i, b = .ok (d, i) → d = dir ∧ rI = .ok i := by
              cases rI with
              | error why => obtain ⟨rfl, rfl⟩ := hP; exact ⟨rfl, rfl, fun _ _ he => by cases he⟩
              | ok input =>
                obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp hP
                exact ⟨rfl, rfl, fun d i he => by cases he; exact ⟨rfl, rfl⟩⟩
            obtain ⟨rfl, hmap, hsub⟩ := hend
            refine ⟨?_, fun d i he => ?_, by simpa [List.append_assoc] using hprep (u := [⟨.getEnv "LEAN_PATH", some received⟩] ++ tI) (o2.prepend hqe)⟩
            · rw [hmap]
              rcases o1 with ⟨f, roots, hb, he, -⟩ | ⟨hf, hw⟩
              · exact .inl ⟨root, f, roots, hroot, hb, he⟩
              · exact .inr ⟨.build hroot hf, hw⟩
            · obtain ⟨rfl, hi⟩ := hsub d i he
              refine ⟨⟨hT₂.subset (by simp), sysroot, root, log, hmemLoad, hroot⟩, ?_⟩
              rcases o1 with ⟨f, roots, -, -, hcl⟩ | ⟨-, why, hw⟩
              · have hc₁ : Clean ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩, ⟨.realPath ".", .ok d⟩,
                    ⟨.loadWorkspace sysroot d, .ok (some root, log)⟩, ⟨.getEnv "LEAN_PATH", some received⟩] : List (Event L E)) := by
                  intro x hx
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                  rcases hx with rfl | rfl | rfl | rfl
                  · exact fun hn => by cases hn
                  · rintro ⟨y, hy⟩; cases hy
                  · rintro (⟨y, hy⟩ | ⟨y, hy⟩) <;> cases hy
                  · exact fun hn => by cases hn
                simpa [List.append_assoc] using hc₁.append hcl
              · rw [hw] at hi; cases hi
          · rename_i hd
            obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₁₄
            exact ⟨.inr ⟨.elsewhere hmem₁ (hT₂.subset (by simp)) hmemLoad hmemEnv ((dispatchedFrom_eq_false_iff _ _).mp (by simpa using hd)), _, rfl⟩,
              (fun _ _ he => by cases he),
              by simpa using hprep (u := [⟨.getEnv "LEAN_PATH", some received⟩]) (InputPreparation.prepend (t := []) hqe (fun e he => by cases he))⟩

/-- `loadTree`: the load of the build in the checker's tree. -/
theorem loadTree_spec {T t : List (Event L E)} {sysroot : String} {tree : FilePath}
    {p : Regula.Closed.Profile} {b : Except String Regula.Closed.Input} (hT : t.Sublist T)
    (h : Runs (loadTree sysroot tree p : Attempt L E _).run t b) :
    Loaded (TreeRoot sysroot tree) (TreeReason sysroot tree) T p b ∧ (∀ i, b = .ok i → Clean t) ∧ RulesPreparation sysroot tree t := by
  unfold loadTree at h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₅, h₅, rfl⟩ := runs_attempt_iff.mp h₃
  obtain rfl := runs_call_iff.mp h₅
  have hT₄ : t₄.Sublist T := (List.sublist_append_right _ _).trans hT
  cases r₅ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₄
    exact ⟨.inr ⟨.noTree (e := e) (hT.subset (by simp)), _, rfl⟩, fun _ he => (by cases he),
      .inl (by simpa using quiet_one (o := .realPath tree) (r := .error e) trivial)⟩
  | ok dir =>
    obtain ⟨t₅, t₆, r₆, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₄
    obtain ⟨t₇, t₈, r₈, rfl, h₈, h₉⟩ := runs_bind_iff.mp h₆
    obtain rfl := runs_call_iff.mp h₈
    obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₉
    have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
    have hmemLoad : (⟨.loadRoot sysroot dir, r₈⟩ : Event L E) ∈ T := hT₄.subset (by simp)
    have hpre : Quiet ([⟨.realPath tree, .ok dir⟩] : List (Event L E)) := quiet_one trivial
    obtain ⟨l1, l2⟩ := loaded_spec (what := "the configuration") (r := r₈)
    cases hl : loaded "the configuration" r₈ with
    | error why =>
      rw [hl] at h₇
      obtain ⟨rfl, rfl⟩ := h₇
      refine ⟨.inr ⟨.load (hT.subset (by simp)) hmemLoad (l2 why hl), why, rfl⟩, fun _ he => (by cases he), ?_⟩
      rcases l2 why hl with ⟨e, rfl⟩ | ⟨log, rfl⟩
      · exact .inr ⟨_, dir, .error e, [], by simp, hpre, by simp, quiet_nil⟩
      · exact .inr ⟨_, dir, .ok (none, log), [], by simp, hpre, by simp, quiet_nil⟩
    | ok root =>
      rw [hl] at h₇
      obtain ⟨log, rfl⟩ := l1 root hl
      obtain ⟨o1, o2⟩ := inputOf_spec hT₆ h₇
      refine ⟨?_, fun i he => ?_, .inr ⟨_, dir, .ok (some root, log), t₆, by simp, hpre, by simp, o2⟩⟩
      · have hroot : TreeRoot sysroot tree T root := ⟨dir, log, hT.subset (by simp), hmemLoad⟩
        rcases o1 with ⟨f, roots, hb, he, -⟩ | ⟨hf, hw⟩
        · exact .inl ⟨root, f, roots, hroot, hb, he⟩
        · exact .inr ⟨.build hroot hf, hw⟩
      · subst he
        rcases o1 with ⟨f, roots, -, -, hcl⟩ | ⟨-, why, hw⟩
        · have hc₁ : Clean ([⟨.realPath tree, .ok dir⟩, ⟨.loadRoot sysroot dir, .ok (some root, log)⟩] : List (Event L E)) := by
            intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · rintro ⟨y, hy⟩; cases hy
            · rintro (⟨y, hy⟩ | ⟨y, hy⟩) <;> cases hy
          simpa [List.append_assoc] using hc₁.append hcl
        · cases hw

end RegulaSpecification.Effects
