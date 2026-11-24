module

public import RegulaSpecification.Proofs.ReaderWalk
import all Regula.Reader

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

theorem parsed_events {input : InputContext} {env : E} {fuel : Nat} {state : ModuleParserState} {messages : MessageLog}
    {commands : List Syntax} {final : MessageLog} {t : List (Event L E)}
    (h : Parsed input env fuel state messages commands final t) : Quiet t ∧ Clean t := by
  induction h with
  | stop => exact ⟨quiet_nil, clean_nil⟩
  | last _ => exact ⟨by quiet_events, clean_one id⟩
  | next _ _ ih =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> rcases List.mem_cons.mp hx with rfl | hx
    · exact trivial
    · exact ih.1 x hx
    · exact id
    · exact ih.2 x hx

def FileFrom (T : List (Event L E)) (root : Root L) (sources : List (Name × Source)) (toolchain : List Name) (m : Name)
    (s : Source) (f : FileRead) : Prop :=
  f.module = m ∧ f.header = s.header ∧
    ∃ (env : E) (final : MessageLog) (commands : List (Event L E)),
      (⟨.importForParser root.toolchain
          (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
            (s.imports.toList.map (·.module)) []
            ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups,
        .ok (env, f.scopedParsers)⟩ : Event L E) ∈ T ∧
      Parsed s.input env (s.input.inputString.utf8ByteSize + 1) s.state s.messages f.commands final commands ∧
        commands.Sublist T ∧
      f.parsed = !final.hasErrors

theorem mem_visible_held {headers : Name → Option (Array Import)} {isToolchain : Name → Bool} {todo seen : List Name}
    {fuel : Nat} {n : Name} (h : n ∈ visibleToolchain headers isToolchain todo seen fuel) : isToolchain n = true := by
  induction fuel generalizing todo seen with
  | zero => simp [visibleToolchain] at h
  | succ fuel ih =>
    cases todo with
    | nil => simp [visibleToolchain] at h
    | cons m rest =>
      simp only [visibleToolchain] at h
      split at h
      · rename_i ht
        rcases List.mem_cons.mp h with rfl | h
        · exact ht
        · exact ih h
      · split at h <;> exact ih h

theorem environmentFor_spec {T t : List (Event L E)} {root : Root L} {cache : ParserCache E} {mods : List Name}
    {b : Except String ((E × List Name) × ParserCache E)} (hT : t.Sublist T)
    (hc : ∀ x ∈ cache, (⟨.importForParser root.toolchain x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (environmentFor root.toolchain cache mods : Attempt L E _).run t b) :
    (∀ pair c', b = .ok (pair, c') → (⟨.importForParser root.toolchain mods.eraseDups, .ok pair⟩ : Event L E) ∈ T ∧
      (∀ x ∈ c', (⟨.importForParser root.toolchain x.1, .ok x.2⟩ : Event L E) ∈ T) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ x, (⟨.importForParser root.toolchain mods.eraseDups, .error x⟩ : Event L E) ∈ t) ∧
    Observes root t := by
  rw [environmentFor] at h
  split at h
  · rename_i pair' hl
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ _ he => by cases he; exact ⟨hc _ (mem_of_lookup hl), hc, clean_nil⟩, by simp, quiet_nil.observes _⟩
  · obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r₆, h₇, rfl⟩ := runs_attempt_iff.mp h₅; obtain rfl := runs_call_iff.mp h₇
    have hobs {r} : Observes root ([⟨.importForParser root.toolchain mods.eraseDups, r⟩] : List (Event L E)) := fun x hx => by
      rw [List.mem_singleton.mp hx]; exact .inr rfl
    cases r₆ with
    | error e' =>
      obtain ⟨rfl, rfl⟩ := h₆
      exact ⟨by simp, fun _ => ⟨e', by simp⟩, by simpa using hobs⟩
    | ok p =>
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
      refine ⟨fun _ _ he => ?_, by simp, by simpa using hobs⟩
      cases he
      have hev : (⟨.importForParser root.toolchain mods.eraseDups, .ok p⟩ : Event L E) ∈ T := hT.subset (by simp)
      exact ⟨hev, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hev
        · exact hc x hx, by clean_events⟩

theorem parseFile_spec {T t : List (Event L E)} {root : Root L} {sources : List (Name × Source)} {toolchain : List Name}
    {cache : ParserCache E} {m : Name} {s : Source} {b : Except String (FileRead × ParserCache E)}
    (hT : t.Sublist T) (hc : ∀ x ∈ cache, (⟨.importForParser root.toolchain x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (parseFile root.toolchain cache sources toolchain m s : Attempt L E _).run t b) :
    (∀ f c', b = .ok (f, c') → FileFrom T root sources toolchain m s f ∧
      (∀ x ∈ c', (⟨.importForParser root.toolchain x.1, .ok x.2⟩ : Event L E) ∈ T) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ mods x, (⟨.importForParser root.toolchain mods, .error x⟩ : Event L E) ∈ t ∧ ∀ n ∈ mods, n ∈ toolchain) ∧
    Observes root t := by
  rw [parseFile] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨e1, e2, e3⟩ := environmentFor_spec ((List.sublist_append_left _ _).trans hT) hc h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂; obtain ⟨x, hx⟩ := e2 ⟨why, rfl⟩
    exact ⟨by simp, fun _ => ⟨_, x, by simpa using hx, fun n hn => by simpa using mem_visible_held (List.mem_eraseDups.mp hn)⟩,
      by simpa using e3⟩
  | ok envResult =>
    obtain ⟨⟨env, scopedParsers⟩, cache'⟩ := envResult
    obtain ⟨hev, hc', hclean⟩ := e1 _ _ rfl
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨⟨commands, final⟩, h₅, rfl⟩ := runs_lift_iff.mp h₃
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
    have hparsed := parseAll_parsed _ _ _ _ _ h₅
    obtain ⟨hq, hcl⟩ := parsed_events hparsed
    refine ⟨fun _ _ he => by cases he; exact ⟨⟨rfl, rfl, env, final, t₃, hev, hparsed,
      by simpa using (List.sublist_append_right _ _).trans hT, rfl⟩, hc', by simpa using hclean.append hcl⟩,
      by simp, by simpa using e3.append (hq.observes _)⟩

theorem parseFiles_spec (root : Root L) (sources : List (Name × Source)) (toolchain : List Name) {T : List (Event L E)}
    (todo : List (Name × Source)) (cache : ParserCache E) {t : List (Event L E)}
    {b : Except String (List FileRead)}
    (hT : t.Sublist T) (hc : ∀ x ∈ cache, (⟨.importForParser root.toolchain x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (parseFiles root.toolchain sources toolchain cache todo : Attempt L E _).run t b) :
    (∀ files, b = .ok files → (∀ f ∈ files, ∃ x ∈ todo, FileFrom T root sources toolchain x.1 x.2 f) ∧
      (∀ x ∈ todo, ∃ f ∈ files, FileFrom T root sources toolchain x.1 x.2 f) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ mods x, (⟨.importForParser root.toolchain mods, .error x⟩ : Event L E) ∈ t ∧ ∀ n ∈ mods, n ∈ toolchain) ∧
    Observes root t := by
  induction todo generalizing cache t b with
  | nil =>
    rw [parseFiles] at h; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ he => by cases he; simpa using clean_nil, by simp, quiet_nil.observes _⟩
  | cons x todo ih =>
    obtain ⟨m, s⟩ := x; rw [parseFiles] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hT₂ := (List.sublist_append_right _ _).trans hT
    obtain ⟨p1, p2, p3⟩ := parseFile_spec ((List.sublist_append_left _ _).trans hT) hc h₁
    cases r with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₂; obtain ⟨mods, x, hx, hn⟩ := p2 ⟨why, rfl⟩
      exact ⟨by simp, fun _ => ⟨mods, x, by simp [hx], hn⟩, by simpa using p3⟩
    | ok fileResult =>
      obtain ⟨file, cache'⟩ := fileResult; obtain ⟨hfile, hc', hcl₁⟩ := p1 _ _ rfl
      obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2, i3⟩ := ih cache' ((List.sublist_append_left _ _).trans hT₂) hc' h₃
      cases r₃ with
      | error w =>
        obtain ⟨rfl, rfl⟩ := h₄; obtain ⟨mods, x, hx, hn⟩ := i2 ⟨w, rfl⟩
        exact ⟨by simp, fun _ => ⟨mods, x, by simp [hx], hn⟩, by simpa using p3.append i3⟩
      | ok fs =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        obtain ⟨j1, j2, j3⟩ := i1 fs rfl
        refine ⟨fun _ he => ?_, by simp, by simpa using p3.append i3⟩
        cases he
        refine ⟨?_, ?_, by simpa using hcl₁.append j3⟩
        · intro f hf; rcases List.mem_cons.mp hf with rfl | hf
          · exact ⟨(m, s), by simp, hfile⟩
          · obtain ⟨y, hy, hfy⟩ := j1 f hf; exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩
        · intro y hy; rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨file, by simp, hfile⟩
          · obtain ⟨f, hf, hfy⟩ := j2 y hy; exact ⟨f, List.mem_cons_of_mem _ hf, hfy⟩

end RegulaSpecification.Effects
