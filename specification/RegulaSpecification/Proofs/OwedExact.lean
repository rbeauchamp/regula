/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Owed

/-!
# Exit 0 exactly when a pass is owed

`plain_owed` and `full_owed` state that what `PlainOwed` and `FullOwed` hold of the responses gives exit 0, for every program
that meets the record. This module states the other direction: a run that exits with 0 received what they hold. So a run with
exit 0 that gets one answer for each operation and, for the full reading, one parser context for each input meets those premises.

That direction has a hypothesis, which only it needs. The record's reasons read what a trace holds, and one operation can
stand in a trace twice with two answers: a path read as a module's file and as the toolchain's file, on answers that no Lake
gives, or a file that another process changed between two reads. Then a run can pass on what it judged, while the other
answer is a reason. `OneAnswer` is what excludes that, and `OneContext` the same of the parser's context. No theorem discharges `OneContext`; read
from the code, `importParsers_eq` reads the scoped parsers from the environment it gives, and a file gets its context from its
header, the run's sources and its toolchain modules (`Regula.Reader.parseFile`).
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language
open RegulaSpecification.Loader

variable {L E : Type}

/-- Each operation of the trace that reads or acts, asked twice, got one answer. A print is left out: its answer decides
nothing. -/
def OneAnswer (t : List (Event L E)) : Prop :=
  ∀ e ∈ t, ∀ e' ∈ t, e.isOnlySaying = false → e.op = e'.op → e = e'

/-- Lean's parser read one input in one environment, and what an import gave of the scoped parsers is a function of the
environment it gave. -/
structure OneContext (t : List (Event L E)) : Prop where
  /-- One environment for one input. -/
  env : ∀ {input env env' s s' m m'} {r : Syntax × ModuleParserState × MessageLog}
    {r' : Syntax × ModuleParserState × MessageLog},
    (⟨.parseCommand input env s m, r⟩ : Event L E) ∈ t → (⟨.parseCommand input env' s' m', r'⟩ : Event L E) ∈ t →
    env = env'
  /-- One list of scoped parsers for one environment. -/
  parsers : ∀ {mods mods' : List Name} {env : E} {a b : List Name},
    (⟨.importForParser mods, .ok (env, a)⟩ : Event L E) ∈ t → (⟨.importForParser mods', .ok (env, b)⟩ : Event L E) ∈ t →
    a = b

theorem OneAnswer.resp {t : List (Event L E)} (h : OneAnswer t) {o : Op L E} {r r' : Resp o}
    (h1 : (⟨o, r⟩ : Event L E) ∈ t) (h2 : (⟨o, r'⟩ : Event L E) ∈ t)
    (hs : (⟨o, r⟩ : Event L E).isOnlySaying = false) : r = r' := by
  have he := h _ h1 _ h2 hs rfl
  simpa using he

/-- The modules of the default targets are one list, on one answer for each library. -/
theorem defaultModules_unique {T : List (Event L E)} (h : OneAnswer T) {root : Root L} {targets a b}
    (ha : DefaultModules T root targets a) (hb : DefaultModules T root targets b) : a = b := by
  induction ha generalizing b with
  | nil => cases hb; rfl
  | lib hl he _ ih =>
    cases hb with
    | lib hl' he' hrest' =>
      have hsame := hl.symm.trans hl'
      cases hsame
      have hms := Except.ok.inj (h.resp he he' rfl)
      subst hms
      rw [ih hrest']
    | exe hl' => rw [hl] at hl'; cases hl'
    | other hl' => rw [hl] at hl'; cases hl'
  | exe hl hx _ ih =>
    cases hb with
    | lib hl' => rw [hl] at hl'; cases hl'
    | exe _ hx' hrest' =>
      have hsame := hx.symm.trans hx'
      cases hsame
      rw [ih hrest']
    | other _ hx' => rw [hx] at hx'; cases hx'
  | other hl hx _ ih =>
    cases hb with
    | lib hl' => rw [hl] at hl'; cases hl'
    | exe _ hx' => rw [hx] at hx'; cases hx'
    | other _ _ hrest' => exact ih hrest'

/-- Two lists of loaded modules with one list of names and one module for each name are one list. -/
theorem modules_eq {a b : List Regula.Load.LoadedModule} (hn : a.map (·.name) = b.map (·.name))
    (h : ∀ m ∈ a, ∀ m' ∈ b, m.name = m'.name → m = m') : a = b := by
  induction a generalizing b with
  | nil => simpa using hn.symm
  | cons x xs ih =>
    cases b with
    | nil => cases hn
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at hn
      rw [h x (by simp) y (by simp) hn.1,
        ih hn.2 fun m hm m' hm' => h m (List.mem_cons_of_mem _ hm) m' (List.mem_cons_of_mem _ hm')]

/-- What a load read of a finished build is one reading, on one answer for each operation. -/
theorem buildRead_unique {T : List (Event L E)} (h : OneAnswer T) {root : Root L} {f f' roots roots'}
    (h1 : BuildRead T root f roots) (h2 : BuildRead T root f' roots') : f = f' ∧ roots = roots' := by
  obtain ⟨q, hq, rfl, hs, ht, hr, hm⟩ := h1
  obtain ⟨q', hq', rfl, hs', ht', hr', hm'⟩ := h2
  obtain rfl := defaultModules_unique h hq hq'
  have henv := Except.ok.inj (h.resp (hs.subset (by simp) : (⟨.importForRules (q.map (·.1)).toArray, .ok f.env⟩ : Event L E) ∈ T)
    (hs'.subset (by simp) : (⟨.importForRules (q.map (·.1)).toArray, .ok f'.env⟩ : Event L E) ∈ T) rfl)
  refine ⟨?_, rfl⟩
  have hdirs := ht.trans ht'.symm
  have hroot := hr.trans hr'.symm
  have hnames : f.modules.toList.map (·.name) = f'.modules.toList.map (·.name) := by
    rw [f.names, f'.names, henv]
  have hmods : f.modules.toList = f'.modules.toList := by
    refine modules_eq hnames fun m hm₁ m' hm₂ hn => ?_
    have hm₁' : m ∈ f.modules := Array.mem_toList_iff.mp hm₁
    have hm₂' : m' ∈ f'.modules := Array.mem_toList_iff.mp hm₂
    have ho : m.olean = m'.olean := Except.ok.inj (h.resp (hm m hm₁') (hn ▸ hm' m' hm₂') rfl)
    rw [f.placed m hm₁', f'.placed m' hm₂', hn, ho, hdirs, hroot]
  have hmods' : f.modules = f'.modules := Array.toList_inj.mp hmods
  obtain ⟨env, td, rd, ms, n, pl⟩ := f
  obtain ⟨env', td', rd', ms', n', pl'⟩ := f'
  simp only at henv hdirs hroot hmods'
  subst henv hdirs hroot hmods'
  rfl

/-- A run of the proof verdict that exits with 0 received what `PlainOwed` states, on one answer for each operation. -/
theorem plain_exit_zero_owed {t : List (Event L E)} {p : Regula.Closed.Profile} (h : PlainRun t p 0)
    (hone : OneAnswer t) : PlainOwed t p := by
  obtain ⟨result, hl, hc, -, -, hok, -⟩ := h
  have healthy := hok rfl
  have hv : (Regula.Closed.decision result).verdict = .pass :=
    (Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp hc.symm
  rcases hl with ⟨root, f, roots, hg, hb, rfl⟩ | ⟨-, m, rfl⟩
  · obtain ⟨sysroot, dir, log, leanPath, lakeLib, program, hs, hload, hdir, hinst, henv, hdis⟩ := id hg
    refine ⟨fun hw => ?_, fun root' f' roots' hg' hb' => ?_⟩
    · cases hw with
      | noSysroot h => exact healthy _ h rfl
      | noDirectory h => exact healthy _ h ⟨_, rfl⟩
      | load _ _ h hf => exact healthy _ h hf
      | noSearchPath h => exact healthy _ h rfl
      | @elsewhere sysroot' dir' root' log' leanPath' program' lakeLib' hs' hd' hl' hi' he' hn =>
        have h1 := Option.some.inj (hone.resp hs' hs rfl)
        subst h1
        have h2 := Except.ok.inj (hone.resp hd' hdir rfl)
        subst h2
        have h3 : (some root', log') = (some root, log) := Except.ok.inj (hone.resp hl' hload rfl)
        simp only [Prod.mk.injEq, Option.some.injEq] at h3
        obtain ⟨rfl, -⟩ := h3
        have h4 : (program', lakeLib') = (program, lakeLib) := hone.resp hi' hinst rfl
        simp only [Prod.mk.injEq] at h4
        obtain ⟨-, rfl⟩ := h4
        have h5 := Option.some.inj (hone.resp he' henv rfl)
        subst h5
        rw [hdis] at hn
        cases hn
      | build _ hf =>
        cases hf with
        | library _ _ h => exact healthy _ h ⟨_, rfl⟩
        | «import» _ h => exact healthy _ h ⟨_, rfl⟩
        | search _ _ _ h => exact healthy _ h ⟨_, rfl⟩
    · obtain ⟨s', d', l', _, _, _, hs', hload', hdir', -⟩ := hg'
      have h1 := Option.some.inj (hone.resp hs' hs rfl)
      subst h1
      have h2 := Except.ok.inj (hone.resp hdir' hdir rfl)
      subst h2
      have h3 : (some root', l') = (some root, log) := Except.ok.inj (hone.resp hload' hload rfl)
      simp only [Prod.mk.injEq, Option.some.injEq] at h3
      obtain ⟨rfl, -⟩ := h3
      obtain ⟨rfl, rfl⟩ := buildRead_unique hone hb' hb
      exact pass_iff_floor.mp hv
  · cases hv

/-- What a parse of one input gave is one list of commands, on one answer for each call of the parser. -/
theorem parsed_unique {T : List (Event L E)} (h : OneAnswer T) {input : InputContext} {env : E} {fuel state messages}
    {a b final final' evs evs'} (ha : Parsed input env fuel state messages a final evs)
    (hb : Parsed input env fuel state messages b final' evs') (hs : ∀ e ∈ evs, e ∈ T) (hs' : ∀ e ∈ evs', e ∈ T) :
    a = b ∧ final = final' := by
  induction ha generalizing b final' evs' with
  | stop => cases hb; exact ⟨rfl, rfl⟩
  | @last fuel state messages stx state' final ht =>
    cases hb with
    | @last _ _ _ stx₂ state₂ _ _ =>
      have hr : (stx, state', final) = (stx₂, state₂, final') :=
        h.resp (hs _ (List.mem_singleton.mpr rfl)) (hs' _ (List.mem_singleton.mpr rfl)) rfl
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -, rfl⟩ := hr
      exact ⟨rfl, rfl⟩
    | @next _ _ _ stx₂ state₂ messages₂ _ _ _ ht₂ _ =>
      have hr : (stx, state', final) = (stx₂, state₂, messages₂) :=
        h.resp (hs _ (List.mem_singleton.mpr rfl)) (hs' _ (List.mem_cons_self ..)) rfl
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -, -⟩ := hr
      rw [ht] at ht₂
      cases ht₂
  | @next fuel state messages stx state' messages' rest final events ht _ ih =>
    cases hb with
    | @last _ _ _ stx₂ state₂ _ ht₂ =>
      have hr : (stx, state', messages') = (stx₂, state₂, final') :=
        h.resp (hs _ (List.mem_cons_self ..)) (hs' _ (List.mem_singleton.mpr rfl)) rfl
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, -, -⟩ := hr
      rw [ht] at ht₂
      cases ht₂
    | @next _ _ _ stx₂ state₂ messages₂ _ _ _ _ hrest =>
      have hr : (stx, state', messages') = (stx₂, state₂, messages₂) :=
        h.resp (hs _ (List.mem_cons_self ..)) (hs' _ (List.mem_cons_self ..)) rfl
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨rfl, rfl⟩ := ih hrest (fun e he => hs e (List.mem_cons_of_mem _ he))
        (fun e he => hs' e (List.mem_cons_of_mem _ he))
      exact ⟨rfl, rfl⟩

/-- A parse with fuel left asks the parser at least once, from where it started. -/
theorem parsed_first {input : InputContext} {env : E} {fuel state messages cmds final} {evs : List (Event L E)}
    (h : Parsed input env (fuel + 1) state messages cmds final evs) :
    ∃ r, (⟨.parseCommand input env state messages, r⟩ : Event L E) ∈ evs := by
  cases h with
  | last => exact ⟨_, List.mem_singleton.mpr rfl⟩
  | next => exact ⟨_, List.mem_cons_self ..⟩

/-- A reading of one file by its path is one reading, on one answer for each operation and one context for each input. -/
theorem readAs_same {T : List (Event L E)} (h : OneAnswer T) (hc : OneContext T) {project tree path : FilePath}
    {f f₀ : FileRead} {i i₀ m m₀} (ha : ReadAs T project tree f path i m) (hb : ReadAs T project tree f₀ path i₀ m₀) :
    f.header = f₀.header ∧ f.commands = f₀.commands ∧ f.parsed = f₀.parsed ∧ f.scopedParsers = f₀.scopedParsers ∧
      i = i₀ := by
  obtain ⟨text, rel, real, state, messages, final, env, commands, h1, -, -, h4, h5, h6, h7, h8⟩ := ha
  obtain ⟨text', rel', real', state', messages', final', env', commands', h1', -, -, h4', h5', h6', h7', h8'⟩ := hb
  have hrel : rel = rel' := List.append_cancel_left (h1.1.symm.trans h1'.1)
  subst hrel
  have htext := Except.ok.inj (h.resp (h4.subset (by simp) : (⟨.readFile (under project rel), .ok text⟩ : Event L E) ∈ T)
    (h4'.subset (by simp) : (⟨.readFile (under project rel), .ok text'⟩ : Event L E) ∈ T) rfl)
  subst htext
  have hhead : (f.header, state, messages, i) = (f₀.header, state', messages', i₀) := Except.ok.inj (h.resp
    (h4.subset (by simp) : (⟨.parseHeader (mkInputContext text path.toString), .ok (f.header, state, messages, i)⟩ :
      Event L E) ∈ T)
    (h4'.subset (by simp) : (⟨.parseHeader (mkInputContext text path.toString),
      .ok (f₀.header, state', messages', i₀)⟩ : Event L E) ∈ T) rfl)
  simp only [Prod.mk.injEq] at hhead
  obtain ⟨hh, rfl, rfl, rfl⟩ := hhead
  obtain ⟨r, hr⟩ := parsed_first h6
  obtain ⟨r', hr'⟩ := parsed_first h6'
  have henv : env = env' := hc.env (h7.subset hr) (h7'.subset hr')
  subst henv
  have hsc : f.scopedParsers = f₀.scopedParsers := hc.parsers h5 h5'
  obtain ⟨hcm, hfin⟩ := parsed_unique h h6 h6' (fun e he => h7.subset he) (fun e he => h7'.subset he)
  exact ⟨hh, hcm, by rw [h8, h8', hfin], hsc, rfl⟩

/-- A list of distinct members of another list sums to no more. -/
theorem sum_le_of_subset {α : Type} {g : α → Nat} {a b : List α} (ha : a.Nodup) (h : ∀ x ∈ a, x ∈ b) :
    (a.map g).sum ≤ (b.map g).sum := by
  classical
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hnd := List.nodup_cons.mp ha
    have hsub : ∀ y ∈ xs, y ∈ b.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun e => hnd.1 (by rw [← e]; exact hy))).mpr (h y (List.mem_cons_of_mem _ hy))
    have hle := ih hnd.2 hsub
    have he : (b.map g).sum = g x + ((b.erase x).map g).sum := by
      have := ((List.perm_cons_erase hx).map g).sum_nat
      simpa using this
    simp only [List.map_cons, List.sum_cons]
    omega

/-- What a key maps to in a list is a member of the list. -/
theorem mem_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β} (h : l.lookup a = some b) :
    (a, b) ∈ l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have hne : (a == k) = false := by simpa using hk
      simp only [List.lookup_cons, hne] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A key of a member has a value. -/
theorem lookup_of_mem_isSome {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β} (h : (a, b) ∈ l) :
    (l.lookup a).isSome = true := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk
      simp
    · have hne : (a == k) = false := by simpa using hk
      simp only [List.lookup_cons, hne]
      rcases List.mem_cons.mp h with he | he
      · cases he
        exact absurd rfl hk
      · exact ih he

/-- No reason in the closed set holds of a run whose reading rests on `Evidence`, is inside the closed language and received
no failed answer, on one answer for each operation and one context for each input. -/
theorem no_reason_of_evidence {T : List (Event L E)} {dir treeDir : FilePath} {stands : List String → Option String}
    {r : Reading} {o : Outcome}
    (hev : Evidence T dir treeDir stands r) (hi : Inside r) (hfail : ∀ e ∈ T, ¬ e.failed) (hone : OneAnswer T)
    (hctx : OneContext T) : ¬ Reason T dir treeDir o := by
  obtain ⟨project, tree, hp, ht, hap, ⟨s1, prog1, lib1, hs1, hl1, hst⟩, ⟨ttext, treal, htt, htr, hte1, hte2, hpin⟩,
    ⟨eabs, habs, nm, cd, dt, rfl⟩, ⟨text, real, table, hr1, hr2, hr3, hr4, hr5, hr6, hdeep, hkeys⟩, hpin0, hc1, hc2, sysroot, root,
    log, modules, hsys, hload, hdef, hroots, hdirs, hglobs, htargets, hres, htwo, headers, held, hcount, hnodup, hcomp,
    hheld, hfiles, honly⟩ := hev.places
  obtain ⟨hclosed, -, hnodep, hnomath, ⟨hne, hrr, hcl, hcovf⟩, hfa⟩ := hi
  have hP {p' : FilePath} (h : (⟨.realPath dir, .ok p'⟩ : Event L E) ∈ T) : project = p' :=
    Except.ok.inj (hone.resp hp h rfl)
  have hT {t' : FilePath} (h : (⟨.realPath treeDir, .ok t'⟩ : Event L E) ∈ T) : tree = t' :=
    Except.ok.inj (hone.resp ht h rfl)
  have hTL {t' : FilePath} {root' : Root L} (h : TreeLoaded T dir treeDir t' root') : tree = t' ∧ root = root' := by
    obtain ⟨h1, s', l', h2, h3, -⟩ := h
    obtain rfl := hT h1
    have h4 := Option.some.inj (hone.resp h2 hsys rfl)
    subst h4
    have h5 : (some root', l') = (some root, log) := Except.ok.inj (hone.resp h3 hload rfl)
    simp only [Prod.mk.injEq, Option.some.injEq] at h5
    exact ⟨rfl, h5.1.symm⟩
  have hSc {p' t' : FilePath} {root' : Root L} {q : List (Name × FilePath)}
      (h : Scene T dir treeDir p' t' root' q) : project = p' ∧ tree = t' ∧ root = root' ∧ modules = q := by
    obtain ⟨h1, h2⟩ := hTL h.loaded
    subst h1 h2
    exact ⟨hP h.project_real, rfl, rfl, defaultModules_unique hone hdef h.default⟩
  have hHead {m path text' header state messages} {imports : Array Import}
      (hc : Compiled headers root modules m path) (hst' : SourceText T project tree path text')
      (he : (⟨.parseHeader (mkInputContext text' path.toString), .ok (header, state, messages, imports)⟩ : Event L E) ∈ T) :
      headers.lookup m = some imports := by
    obtain ⟨-, f, -, -, i0, m0, text0, hl0, hra, -⟩ := hcomp m path hc
    obtain ⟨rel, hrel, hread⟩ := hst'
    obtain ⟨rel', real', st0, ms0, fin0, env0, cmds0, h1, -, -, h4, -⟩ := hra
    have hrel' : rel = rel' := List.append_cancel_left (hrel.1.symm.trans h1.1)
    subst hrel'
    have htx : text' = text0 := Except.ok.inj (hone.resp hread
      (h4.subset (by simp) : (⟨.readFile (under project rel), .ok text0⟩ : Event L E) ∈ T) rfl)
    subst htx
    have hh : (header, state, messages, imports) = (f.header, st0, ms0, i0) := Except.ok.inj (hone.resp he
      (h4.subset (by simp) : (⟨.parseHeader (mkInputContext text' path.toString), .ok (f.header, st0, ms0, i0)⟩ :
        Event L E) ∈ T) rfl)
    simp only [Prod.mk.injEq] at hh
    rw [hl0, hh.2.2.2]
  have hNC : ∀ {m}, Named T project tree root modules m → ∀ path, FileOfModule root modules m path →
      Compiled headers root modules m path := by
    intro m hn
    induction hn with
    | root hm =>
      rename_i m'
      intro path hf
      obtain ⟨⟨k, p0⟩, hx, hk⟩ := List.mem_map.mp hm
      obtain rfl : k = m' := hk
      rcases hf with hf | hf
      · exact .root hf
      · rw [hres _ _ _ hx hf]
        exact .root hx
    | @imported m₀ imports i hn₀ hh hi ih =>
      intro path hf
      rcases hf with hf | hf
      · exact .root hf
      · obtain ⟨p₀, text₀, a, b, c, hf₀, hst₀, he₀⟩ := hh
        have hc₀ := ih p₀ hf₀
        exact .imported hc₀ (hHead hc₀ hst₀ he₀) ⟨i, hi, rfl⟩ hf
  have hNI {m} {imports : Array Import} {i : Import} (hn : Named T project tree root modules m)
      (hh : HeaderOf T project tree root modules m imports) (hi : i ∈ imports) :
      (i.module ∈ r.reached ∨ (root.resolve i.module = none ∧ modules.lookup i.module = none ∧
        HeldByToolchain T root i.module)) ∧ ClosedModuleName i.module ∧ i.module.getRoot ≠ `Mathlib ∧
        ((modules.lookup i.module).isSome = true → (root.resolve i.module).isSome = true) := by
    obtain ⟨p₀, text₀, a, b, c, hf₀, hst₀, he₀⟩ := hh
    have hc₀ := hNC hn p₀ hf₀
    have hl := hHead hc₀ hst₀ he₀
    obtain ⟨-, f, hf, hmod, -, -, -, -, -, -⟩ := hcomp m p₀ hc₀
    obtain ⟨-, i1, -, -, -, -, -, hl1, -, hall⟩ := hfiles f hf
    rw [hmod, hl] at hl1
    cases hl1
    exact hall i hi
  intro hreason
  cases hreason with
  | failed he _ hf => exact hfail _ he hf
  | load hp hf => exact hfail _ hp.event hf
  | toolchain h1 h2 h3 =>
    obtain rfl := hP h1
    exact h3 (by rw [← Except.ok.inj (hone.resp h2 htt rfl)] at hpin; exact hpin)
  | toolchainFailed h1 h2 =>
    obtain rfl := hP h1
    cases hone.resp h2 htt rfl
  | toolchainNotExact h1 h2 h3 =>
    obtain rfl := hP h1
    rw [Except.ok.inj (hone.resp h2 htr rfl), (exactBelow_iff _ _ _).mpr ⟨hte1, hte2⟩] at h3
    cases h3
  | toolchainNoReal h1 h2 =>
    obtain rfl := hP h1
    cases hone.resp h2 htr rfl
  | @started p' s' pr' ll' app' real' lp' h1 h2 h3 h4 h5 h6 h7 =>
    obtain rfl := hP h1
    obtain rfl := Option.some.inj (hone.resp h2 hs1 rfl)
    have hi1 : (pr', ll') = (prog1, lib1) := hone.resp h3 hl1 rfl
    simp only [Prod.mk.injEq] at hi1
    obtain ⟨-, rfl⟩ := hi1
    obtain ⟨a0, r0, own, lp0, g1, g2, g3, g4, g5, g6⟩ := hst
    obtain rfl := Except.ok.inj (hone.resp h4 g1 rfl)
    obtain rfl := Except.ok.inj (hone.resp h5 g2 rfl)
    obtain rfl := Option.some.inj (hone.resp h6 g3 rfl)
    rcases h7 with h7 | h7
    · rw [g5] at h7
      cases h7
    · rw [h7 own g4] at g6
      cases g6
  | tomlNotExact h1 h2 h3 =>
    obtain rfl := hP h1
    rw [Except.ok.inj (hone.resp h2 hr1 rfl), (exactBelow_iff _ _ _).mpr ⟨hr2, hr3⟩] at h3
    cases h3
  | notApart h1 h2 h3 =>
    obtain rfl := hP h1
    obtain rfl := hT h2
    exact h3 hap
  | configNotInTree h1 h2 h3 =>
    obtain rfl := hT h1
    rcases h2 with rfl | rfl
    · exact hc1 h3
    · exact hc2 h3
  | moduleNotInTree hsc hn hf ho =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    exact (hcomp _ _ (hNC hn _ hf)).1 ho
  | moduleNotExact hsc hn hf hrel hreal hb =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    obtain ⟨-, f, -, -, i0, m0, text0, -, hra, -⟩ := hcomp _ _ (hNC hn _ hf)
    obtain ⟨rel', real', st0, ms0, fin0, env0, cmds0, h1, h2, h3, h4, -⟩ := hra
    have hrel' := List.append_cancel_left (hrel.1.symm.trans h1.1)
    subst hrel'
    rw [Except.ok.inj (hone.resp hreal (h4.subset (List.mem_cons_self ..)) rfl), (exactBelow_iff _ _ _).mpr ⟨h2, h3⟩] at hb
    cases hb
  | leanConfig h1 h2 =>
    obtain rfl := hP h1
    cases hone.resp h2 habs rfl
  | key hk hp' hroot hna =>
    obtain ⟨p', t', h1, h2, h3⟩ := hk
    obtain rfl := hP h1
    obtain rfl := Except.ok.inj (hone.resp h2 hr4 rfl)
    obtain rfl := Except.ok.inj (hone.resp h3 hr5 rfl)
    exact hna (hclosed.2.2.2 _ (hkeys _ hp') hroot)
  | deep hk hd =>
    obtain ⟨p', t', h1, h2, h3⟩ := hk
    obtain rfl := hP h1
    obtain rfl := Except.ok.inj (hone.resp h2 hr4 rfl)
    obtain rfl := Except.ok.inj (hone.resp h3 hr5 rfl)
    exact hdeep hd
  | deepDependency hk hd =>
    obtain ⟨p', t', h1, h2, h3⟩ := hk
    obtain rfl := hP h1
    obtain rfl := Except.ok.inj (hone.resp h2 hr4 rfl)
    obtain rfl := Except.ok.inj (hone.resp h3 hr5 rfl)
    exact hdeep hd
  | dependency hk hp' hroot =>
    obtain ⟨p', t', h1, h2, h3⟩ := hk
    obtain rfl := hP h1
    obtain rfl := Except.ok.inj (hone.resp h2 hr4 rfl)
    obtain rfl := Except.ok.inj (hone.resp h3 hr5 rfl)
    exact hnodep ⟨_, hkeys _ hp', hroot⟩
  | openDir hl hd hn =>
    obtain ⟨rfl, rfl⟩ := hTL hl
    obtain ⟨rel, hrel⟩ := hdirs _ hd
    exact hn rel hrel
  | openGlob hl hd hg hn =>
    obtain ⟨rfl, rfl⟩ := hTL hl
    obtain ⟨n, rfl⟩ := hglobs _ hd _ hg
    exact hn n rfl
  | noClaim hsc =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    exact hne (by simpa using hroots)
  | targetName hl hn hc =>
    obtain ⟨rfl, rfl⟩ := hTL hl
    exact hc (htargets _ hn)
  | twoFiles hsc h1 h2 h3 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    exact h3 (hres _ _ _ h1 h2)
  | twoRoots hsc h1 h2 h3 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    exact h3 (htwo _ _ _ h1 h2)
  | moduleName hsc hn hc =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    cases hn with
    | root hm => exact hc (hcl _ (hrr _ (hroots ▸ hm)))
    | imported hn₀ hh hi => exact hc (hNI hn₀ hh hi).2.1
  | twoTexts hsc hp1 hp2 hparts hne =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    have hstands {path text'} (hpl : Planned T project tree root modules path text') :
        stands (parts path) = some text' := by
      cases hpl with
      | toml h => rw [Except.ok.inj (hone.resp h hr4 rfl)]; exact hr6
      | toolchain => exact hpin0
      | source hn hf hst =>
        obtain ⟨-, f, -, -, i0, m0, t0, -, hra, hs0⟩ := hcomp _ _ (hNC hn _ hf)
        obtain ⟨rel, hrel, hread⟩ := hst
        obtain ⟨rel', real', st0, ms0, fin0, env0, cmds0, h1, -, -, h4, -⟩ := hra
        have hrel' : rel = rel' := List.append_cancel_left (hrel.1.symm.trans h1.1)
        subst hrel'
        have htx : text' = t0 := Except.ok.inj (hone.resp hread
          (h4.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)) :
            (⟨.readFile (under project rel), .ok t0⟩ : Event L E) ∈ T) rfl)
        rw [htx]
        exact hs0
    have h1 := hstands hp1
    rw [hparts, hstands hp2] at h1
    exact hne (Option.some.inj h1).symm
  | importedRoot hsc hn hh hi h1 h2 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    have := (hNI hn hh hi).2.2.2 h1
    rw [h2] at this
    cases this
  | @notToolchain p' t' r' q m olean' real' reals hsc hn hl hr h1 h2 h3 h4 =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    have hnoFile : ∀ path, ¬ FileOfModule root modules m path := by
      rintro path (hf | hf)
      · have := lookup_of_mem_isSome hf
        rw [hl] at this
        cases this
      · rw [hr] at hf
        cases hf
    cases hn with
    | root hm =>
      obtain ⟨⟨k, p0⟩, hx, rfl⟩ := List.mem_map.mp hm
      exact hnoFile p0 (.inl hx)
    | imported hn₀ hh hi =>
      rcases (hNI hn₀ hh hi).1 with hreach | ⟨-, -, hheldBy⟩
      · obtain ⟨f, hf, hmod⟩ := hcovf _ hreach
        obtain ⟨p1, -, -, -, hfm, -⟩ := hfiles f hf
        rw [hmod] at hfm
        exact hnoFile p1 hfm
      · obtain ⟨olean, real', d, dr, hsub, hd, hdr, hb⟩ := hheldBy
        obtain rfl := Except.ok.inj (hone.resp h1 (hsub.subset (List.mem_cons_self ..)) rfl)
        obtain rfl := Except.ok.inj (hone.resp h2 (hsub.subset (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))) rfl)
        rw [← h3] at hd
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        obtain ⟨h5, h6⟩ := h4 x hx
        obtain rfl := Except.ok.inj (hone.resp h5 hdr rfl)
        rw [hb] at h6
        cases h6
  | @tooMany p' t' root' q ms hsc hnd hall hgt =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    have hsub : ∀ x ∈ ms, x ∈ headers := by
      intro x hx
      obtain ⟨hn, p₀, text₀, a, b, c, hf₀, hst₀, he₀⟩ := hall x hx
      exact mem_lookup (hHead (hNC hn p₀ hf₀) hst₀ he₀)
    have hms : ms.Nodup := by
      exact (List.pairwise_map.mp hnd).imp fun h he => h (by rw [he])
    have := sum_le_of_subset (g := fun x : Name × Array Import => x.2.size) hms hsub
    omega
  | mathlib hsc hn hroot =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    cases hn with
    | root hm => exact hnomath ⟨_, hrr _ (hroots ▸ hm), hroot⟩
    | imported hn₀ hh hi => exact (hNI hn₀ hh hi).2.2.1 hroot
  | file hsc hn hf hra _ _ _ _ _ hna =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hSc hsc
    obtain ⟨-, f₀, hf₀, -, _, _, t0, -, hra₀, -⟩ := hcomp _ _ (hNC hn _ hf)
    obtain ⟨hh, hcm, hpa, hsp, -⟩ := readAs_same hone hctx hra ⟨t0, hra₀⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := hfa f₀ hf₀
    refine hna ⟨hpa.trans a1, hh ▸ a2, hcm ▸ a3, ?_, fun c hc => ?_⟩
    · rw [hh, hsp]
      exact a4
    · rw [hsp]
      exact a5 c (hcm ▸ hc)

/-- What is read before the build is what the run holds. -/
theorem readPhase_subset {t : List (Event L E)} {e : Event L E} (h : e ∈ readPhase t) : e ∈ t :=
  (List.drop_sublist _ _).subset ((List.takeWhile_sublist _).subset h)

/-- What follows the last Lake command is what the run holds. -/
theorem rulesPhase_subset {t : List (Event L E)} {e : Event L E} (h : e ∈ rulesPhase t) : e ∈ t := by
  simp only [rulesPhase, List.mem_reverse] at h
  exact List.mem_reverse.mp ((List.takeWhile_sublist _).subset h)

/-- A run of the full gate that exits with 0 received what `FullOwed` states, on one answer for each operation of its reading
and of its load of the result, and one context for each input. -/
theorem full_exit_zero_owed {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} (h : FullRun t dir p 0)
    (h1 : OneAnswer (readPhase t)) (h2 : OneContext (readPhase t)) (h3 : OneAnswer (rulesPhase t)) :
    FullOwed t dir p := by
  rcases h with ⟨e, rest, -, hc, -⟩ | ⟨tree, tRead, tGate, r, last, ht, hq, hlast, o, report, hdec, -, hn, ha, hc, -, -, hok, -⟩
  · exact absurd hc (by decide)
  have healthy := hok rfl
  have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp hc.symm
  subst hrep
  have htree : t = ⟨.createTempDir, .ok tree⟩ :: (tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last) := by
    rw [ht]; simp
  have hread : tRead.Sublist (readPhase t) := by
    have := readPhase_sublist (x := ⟨.createTempDir, .ok tree⟩)
      (rest := tGate ++ ⟨.removeDirAll tree, r⟩ :: last) hq
    simpa [ht] using this
  cases o with
  | refused => cases (hn (by simp)).2
  | proofOnly => cases (hn (by simp)).2
  | incomplete => cases (hn (by simp)).2
  | admitted =>
    obtain ⟨r', hi, hev⟩ := hdec.1 rfl
    obtain ⟨sysroot, tBuild, tRules, hs, rfl, hb⟩ := ha rfl
    have htree' : ∀ {tree' rest}, t = ⟨.createTempDir, .ok tree'⟩ :: rest → tree = tree' := by
      intro tree' rest he
      rw [htree] at he
      injection he with he' _
      injection he' with _ hr
      exact Except.ok.inj hr
    refine ⟨fun e he => healthy _ he ⟨e, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro tree' rest o' he
      obtain rfl := htree' he
      exact no_reason_of_evidence (Evidence.mono hread hev) hi (fun e he => healthy e (readPhase_subset he)) h1 h2
    · intro tree' rest s' he _ hrej
      cases hrej with
      | build _ h4 h5 => exact healthy _ h4 h5
      | replay _ _ h4 h5 => exact healthy _ h4 h5
    · intro tree' rest s' he _ hw
      have hb' {root} (hf : BuildFailed (rulesPhase t) root) : False := by
        cases hf with
        | library _ _ h => exact healthy _ (rulesPhase_subset h) ⟨_, rfl⟩
        | «import» _ h => exact healthy _ (rulesPhase_subset h) ⟨_, rfl⟩
        | search _ _ _ h => exact healthy _ (rulesPhase_subset h) ⟨_, rfl⟩
      cases hw with
      | noTree h => exact healthy _ (rulesPhase_subset h) ⟨_, rfl⟩
      | load _ h hf => exact healthy _ (rulesPhase_subset h) hf
      | build _ hf => exact hb' hf
    · intro tree' rest s' root' f' roots' he hs' hg' hb'
      obtain rfl := htree' he
      obtain rfl := Option.some.inj (h1.resp hs' (hread.subset hs) rfl)
      rcases hb.2.2.1 with ⟨program, lakeLib, result, hnb, -, hl, hrep⟩ | ⟨hrep, -⟩
      · have hrules : tRules.Sublist (rulesPhase t) := by
          have hpost : ∀ e ∈ (⟨.removeDirAll tree, r⟩ :: last : List (Event L E)), e.isBuild = false := by
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · rfl
            · have := hlast e he
              obtain ⟨o', r'⟩ := e
              cases o' <;> first | rfl | cases this
          have := rulesPhase_sublist (pre := ⟨.createTempDir, .ok tree⟩ :: tRead ++ tBuild) hnb hpost
          simpa [ht, List.append_assoc] using this
        have hv : (Regula.Closed.decision result).verdict = .pass := (Report.full.inj hrep).symm
        rcases hl with ⟨root, f, roots, hg, hbr, rfl⟩ | ⟨-, m, rfl⟩
        · obtain ⟨real₁, log₁, g1, g2⟩ := TreeRoot.mono hrules hg
          obtain ⟨real₂, log₂, g3, g4⟩ := hg'
          obtain rfl := Except.ok.inj (h3.resp g3 g1 rfl)
          have h5 : (some root', log₂) = (some root, log₁) := Except.ok.inj (h3.resp g4 g2 rfl)
          simp only [Prod.mk.injEq, Option.some.injEq] at h5
          obtain ⟨rfl, -⟩ := h5
          obtain ⟨rfl, rfl⟩ := buildRead_unique h3 hb' (BuildRead.mono hrules hbr)
          exact pass_iff_floor.mp hv
        · cases hv
      · cases hrep

end RegulaSpecification.Effects
