/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Preparation
import RegulaSpecification.Proofs.Owed
import RegulaSpecification.Proofs.Written

/-!
# What a full verdict's admission is about

These theorems read the record alone, so they hold of every program that meets it. `FullRun.gate_stands` states that a full run
that reaches a Lake command or a load for the rules has an admitted reading and a gate, and that at each point of the gate what
stands is what the reading left, on `Evidence` of that state. `FullRun.at_consumer` and `FullRun.judged_at_consumer` state it at the
consumer, and `Evidence.judged` that each text standing was judged. `uncheckedCopy_fails` and `uncheckedCopy_build_fails` make the
trace of an audit of an earlier revision fail the record, for every text other than the pinned one that neither Lake's nor Lean's
parser was given, and `judgedCopy_stands` is its neighbour: the same copy of a text that stands keeps the evidence.
`rewritten_stands` gives what stands after two writes. `FullRun.answered_at_consumer` states that each text standing by a write of the
reading is what the file system answered for that write's path after the reading's last act, and `act_after_readBack_fails` that a
reading that ends with an act, once a written text stands, fails the clause, for each act of `Op`.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open Lean.Parser (mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-- Whether a request is a Lake command or a load for the rules. -/
def Event.consumesTree (e : Event L E) : Bool :=
  e.isBuild || e.isImportForRules

/-- An event that only reports or that the rules phase may ask does not write or remove. -/
theorem keeps_of_no_mutation {e : Event L E} (h : match e.op with
    | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ => False
    | _ => True) : e.keepsFiles := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | trivial | exact h.elim

/-- An event that is not in a prefix of a list comes after all of that prefix. -/
theorem prefix_of_not_mem {A B pre post : List (Event L E)} {e : Event L E} (h : A ++ B = pre ++ e :: post) (he : e ∉ A) :
    ∃ mid, pre = A ++ mid ∧ B = mid ++ e :: post := by
  induction A generalizing pre with
  | nil => exact ⟨pre, rfl, h⟩
  | cons a A ih =>
    cases pre with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) he
    | cons x pre' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨mid, rfl, hb⟩ := ih h' (fun hx => he (List.mem_cons_of_mem _ hx))
      exact ⟨mid, rfl, hb⟩

/-- An event that is not in a suffix of a list lies in the rest, after what comes before it. -/
theorem split_before {G R mid post : List (Event L E)} {e : Event L E} (h : G ++ R = mid ++ e :: post) (he : e ∉ R) :
    ∃ rest, G = mid ++ e :: rest := by
  induction G generalizing mid with
  | nil =>
    simp only [List.nil_append] at h
    exact absurd (by rw [h]; simp) he
  | cons g G ih =>
    cases mid with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact ⟨G, by simp [h.1]⟩
    | cons m mid' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rest, hr⟩ := ih h.2
      exact ⟨rest, by simp [hr, h.1]⟩

/-- A full run that reaches a Lake command or a load for the rules has made its tree, read, and gone on to a gate that ends with the
removal. Its reading is inside the closed language with no failed answer, on `Evidence` of what the reading left. No event of the
gate writes or removes a file, so at each point of the gate, the reload included, what stands is what the reading left. This is
about the run's own requests: what a trusted call does inside itself and what another process does are not events of the trace. -/
theorem FullRun.gate_stands {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post)
    (he : e.consumesTree = true) :
    ∃ (tree : FilePath) (tRead tGate : List (Event L E)) (resp : Except IO.Error Unit) (last : List (Event L E)) (r : Reading),
      t = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ (tGate ++ ⟨.removeDirAll tree, resp⟩ :: last) ∧
      (∃ mid rest, tGate = mid ++ e :: rest ∧ pre = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ mid) ∧
      Inside r ∧ Evidence tRead dir tree (written tRead) r ∧ (∃ real, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ tRead ∧ ReadBack tRead real) ∧
      (∀ x ∈ tRead, ¬ x.failed) ∧
      (∀ x ∈ tGate, x.keepsFiles) ∧
      ∀ u v, tGate = u ++ v → ∀ q, written ((⟨.createTempDir, .ok tree⟩ :: tRead) ++ u) q = written tRead q := by
  have hsay {x : Event L E} (hs : x.isOnlySaying = true) : x.consumesTree = false := by
    obtain ⟨o, r⟩ := x
    cases o <;> first | rfl | cases hs
  rcases h with ⟨err, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, resp, last, rfl, hrd, hlast, o, report, hdec, hnf, hstop, hadm, -, -, -, -, -, -⟩
  · -- No tree: nothing consumes one.
    exfalso
    have hmem : e ∈ (⟨.createTempDir, .error err⟩ :: rest : List (Event L E)) := by rw [ht]; simp
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases he
    · rw [hsay (hs e hmem)] at he
      cases he
  · have hnotRead : e ∉ (⟨.createTempDir, .ok tree⟩ :: tRead : List (Event L E)) := fun hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · cases he
      · have := hrd e hx
        simp [Event.consumesTree, this.1, this.2] at he
    have hnotLast : e ∉ (⟨.removeDirAll tree, resp⟩ :: last : List (Event L E)) := fun hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · cases he
      · rw [hsay (hlast e hx)] at he
        cases he
    have ht' : (⟨.createTempDir, .ok tree⟩ :: tRead) ++ (tGate ++ ⟨.removeDirAll tree, resp⟩ :: last) = pre ++ e :: post := by
      simpa [List.append_assoc] using ht
    obtain ⟨mid, hpre, hrest⟩ := prefix_of_not_mem ht' hnotRead
    obtain ⟨tail, htail⟩ := split_before hrest hnotLast
    by_cases ho : o = .admitted
    · subst ho
      obtain ⟨r, real, hi, hev, hreal, hback⟩ := hdec.1 rfl
      obtain ⟨sysroot, tBuild, tRules, -, hgate, hb⟩ := hadm rfl
      subst hgate
      have hkeep : ∀ x ∈ tBuild ++ tRules, x.keepsFiles := fun x hx => keeps_of_no_mutation (hb.no_mutation x hx)
      refine ⟨tree, tRead, tBuild ++ tRules, resp, last, r, by simp [List.append_assoc], ⟨mid, tail, htail, hpre⟩, hi, hev, ⟨real, hreal, hback⟩, hnf rfl,
        hkeep, fun u v hu q => ?_⟩
      have hku : ∀ x ∈ u, x.keepsFiles := fun x hx => hkeep x (by rw [hu]; exact List.mem_append_left _ hx)
      rw [written_append, leavesAs_nil_of_keeps hku]
      rfl
    · rw [(hstop ho).1] at htail
      simp at htail

/-- At each Lake command and each load for the rules of a full run, the events before it are the tree's allocation, a reading and
events that neither write nor remove, and the reading is inside the closed language with no failed answer, on `Evidence` of what
stands right then. So what the admission judged is what stands by the run's requests at that request. -/
theorem FullRun.at_consumer {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post)
    (he : e.consumesTree = true) :
    ∃ (tree : FilePath) (tRead mid : List (Event L E)) (r : Reading),
      pre = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ mid ∧ (∀ x ∈ mid, x.keepsFiles) ∧ Inside r ∧
      Evidence tRead dir tree (written pre) r ∧ (∀ x ∈ tRead, ¬ x.failed) := by
  obtain ⟨tree, tRead, tGate, -, -, r, -, ⟨mid, rest, hgate, hpre⟩, hi, hev, -, hnf, hkeep, hstands⟩ := h.gate_stands ht he
  have hsame : (written pre : List String → Option String) = written tRead := by
    funext q
    rw [hpre]
    exact hstands mid (e :: rest) hgate q
  refine ⟨tree, tRead, mid, r, hpre, fun x hx => hkeep x (by rw [hgate]; exact List.mem_append_left _ hx), hi, ?_, hnf⟩
  rw [hsame]
  exact hev

/-- Each text that the state of `Evidence` holds is one the run judged: the text of `lakefile.toml` that Lake's parser read, the
pinned text, or a text that a file of the reading was parsed from. -/
theorem Evidence.judged {T : List (Event L E)} {dir treeDir : FilePath} {held : List String → Option String} {r : Reading}
    (h : Evidence T dir treeDir held r) {q : List String} {text : String} (hq : held q = some text) :
    (∃ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ T) ∨ text = leanToolchain ∨
      ∃ f ∈ r.files, ∃ project tree path imports mods, parts path = q ∧ ReadText T project tree f path imports mods text := by
  obtain ⟨project, tree, -, -, -, -, -, -, ⟨t0, -, table, -, -, -, -, h5, h6, -, -⟩, hpin, -, -, -, root, -, modules, -, -, -, -, -, -,
    -, -, -, headers, -, -, -, -, -, -, honly⟩ := h.places
  rcases honly q text hq with rfl | rfl | ⟨f, hf, path, i, md, -, h1, h2⟩
  · have : t0 = text := Option.some.inj (h6.symm.trans hq)
    subst this
    exact .inl ⟨table, h5⟩
  · exact .inr (.inl (Option.some.inj (hq.symm.trans hpin)))
  · exact .inr (.inr ⟨f, hf, project, tree, path, i, md, h1, h2⟩)

/-- Two names with one file: each name's file of the reading was parsed from one text. -/
theorem Evidence.two_names {T : List (Event L E)} {dir treeDir : FilePath} {held : List String → Option String} {r : Reading}
    (h : Evidence T dir treeDir held r) :
    ∃ (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) (headers : List (Name × Array Lean.Import)),
      ∀ m path m' path', Compiled headers root modules m path → Compiled headers root modules m' path' → parts path = parts path' →
        ∃ text, (∃ f ∈ r.files, f.module = m ∧ ∃ imports mods, ReadText T project tree f path imports mods text) ∧
          ∃ f ∈ r.files, f.module = m' ∧ ∃ imports mods, ReadText T project tree f path' imports mods text := by
  obtain ⟨project, tree, -, -, -, -, -, -, -, -, -, -, -, root, -, modules, -, -, -, -, -, -, -, -, -, headers, -, -, -, hc, -, -, -⟩ :=
    h.places
  refine ⟨project, tree, root, modules, headers, fun m path m' path' h1 h2 hp => ?_⟩
  obtain ⟨-, f, hf, hm, i, md, t1, -, g1, s1⟩ := hc m path h1
  obtain ⟨-, f', hf', hm', i', md', t2, -, g2, s2⟩ := hc m' path' h2
  have : t1 = t2 := Option.some.inj (s1.symm.trans (hp ▸ s2))
  subst this
  exact ⟨t1, ⟨f, hf, hm, i, md, g1⟩, f', hf', hm', i', md', g2⟩

/-- The trace of an audit of an earlier revision: after the reading, read a file of the project again, and copy what that read gave
over the file in the tree. -/
def uncheckedCopy (source path parent : FilePath) (text : String) : List (Event L E) :=
  [⟨.readFile source, .ok text⟩, ⟨.createDirAll parent, .ok ()⟩, ⟨.writeFile path text, .ok ()⟩]

/-- That trace has no `Evidence` of the state it leaves, for every path, every reading and every text other than the pinned one that
neither Lake's TOML parser nor Lean's header parser was given: the state holds that text, and `Evidence` says that every text
standing was judged. So an earlier good reading gives no authority for what a later write replaced. -/
theorem uncheckedCopy_fails {T : List (Event L E)} {dir treeDir source path parent : FilePath} {text : String} {r : Reading}
    (hpin : text ≠ leanToolchain)
    (hnotToml : ∀ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text)
    (hnotFile : ∀ name x, (⟨.parseHeader (mkInputContext text name), .ok x⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text) :
    ¬ Evidence (T ++ uncheckedCopy source path parent text) dir treeDir
      (written (T ++ uncheckedCopy source path parent text)) r := by
  intro hev
  have hq : written (T ++ uncheckedCopy (L := L) (E := E) source path parent text) (parts path) = some text := by
    have := written_last_write (T ++ [⟨.readFile source, .ok text⟩, ⟨.createDirAll parent, .ok ()⟩]) ([] : List (Event L E)) path text (.ok ())
      (fun _ _ => rfl)
    simpa [uncheckedCopy, List.append_assoc] using this
  rcases Evidence.judged hev hq with ⟨table, hm⟩ | h | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4, _⟩
  · exact hnotToml table hm
  · exact hpin h
  · exact hnotFile _ _ (h4.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- At each Lake command and each load for the rules of a full run, each text standing is one the run judged before it. -/
theorem FullRun.judged_at_consumer {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post)
    (he : e.consumesTree = true) {q : List String} {text : String} (hq : written pre q = some text) :
    (∃ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ pre) ∨ text = leanToolchain ∨
      ∃ name x, (⟨.parseHeader (mkInputContext text name), .ok x⟩ : Event L E) ∈ pre := by
  obtain ⟨tree, tRead, mid, r, hpre, -, -, hev, -⟩ := h.at_consumer ht he
  have hsub : ∀ x ∈ tRead, x ∈ pre := fun x hx => by
    rw [hpre]
    simp [hx]
  rcases Evidence.judged hev hq with ⟨table, hm⟩ | hpin | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4, _⟩
  · exact .inl ⟨table, hsub _ hm⟩
  · exact .inr (.inl hpin)
  · exact .inr (.inr ⟨_, _, hsub _ (h4.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))⟩)

/-- No full run reaches a Lake command after that trace, for every path, every run and every text other than the pinned one that
neither parser was given before that command. -/
theorem uncheckedCopy_build_fails {T post : List (Event L E)} {dir source path parent tree program cwd : FilePath} {text : String}
    {args : List String} {r : Except IO.Error UInt32} {p : Regula.Closed.Profile} {c : UInt32}
    (hpin : text ≠ leanToolchain)
    (hnotToml : ∀ table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text)
    (hnotFile : ∀ name x, (⟨.parseHeader (mkInputContext text name), .ok x⟩ : Event L E) ∉ T ++ uncheckedCopy source path parent text) :
    ¬ FullRun ((⟨.createTempDir, .ok tree⟩ :: (T ++ uncheckedCopy source path parent text)) ++
      ⟨.runLake program cwd args, r⟩ :: post) dir p c := by
  intro h
  have hq : written (⟨.createTempDir, .ok tree⟩ :: (T ++ uncheckedCopy (L := L) (E := E) source path parent text)) (parts path) = some text := by
    have := written_last_write (⟨.createTempDir, .ok tree⟩ :: (T ++ [⟨.readFile source, .ok text⟩, ⟨.createDirAll parent, .ok ()⟩]))
      ([] : List (Event L E)) path text (.ok ()) (fun _ _ => rfl)
    simpa [uncheckedCopy, List.append_assoc] using this
  rcases FullRun.judged_at_consumer h rfl rfl hq with ⟨table, hm⟩ | hp | ⟨name, x, hm⟩
  · rcases List.mem_cons.mp hm with he | hm
    · cases congrArg Event.op he
    · exact hnotToml table hm
  · exact hpin hp
  · rcases List.mem_cons.mp hm with he | hm
    · cases congrArg Event.op he
    · exact hnotFile name x hm

/-- At each Lake command and each load for the rules of a full run, each text that stands by a write of the reading is the answer that
the file system gave for that write's path after the reading's last act, and that same segment holds its answer that nothing has the name
`lakefile.lean` in the tree, which Lake prefers to the configuration judged. Between that answer and this request the run asks no
write and no removal, and the events of the reading after it hold no act at all. So no theorem here needs that different components
name different files, or that a write that answered success stored its text. -/
theorem FullRun.answered_at_consumer {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) {pre post : List (Event L E)} {e : Event L E} (ht : t = pre ++ e :: post)
    (he : e.consumesTree = true) :
    ∃ (tree : FilePath) (before suffix mid : List (Event L E)),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧ (∀ x ∈ mid, x.keepsFiles) ∧
      (∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ before ++ suffix → written pre (parts path) = some text →
        (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix) ∧
      ∃ real err, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
        (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ suffix ∧
        ∃ name code details, err = .noFileOrDirectory name code details := by
  obtain ⟨tree, tRead, tGate, -, -, r, -, ⟨mid, rest, hgate, hpre⟩, -, -, ⟨real, hreal, hback⟩, -, hkeep, hstands⟩ := h.gate_stands ht he
  obtain ⟨before, suffix, rfl, hq, hread, err, herr, hno⟩ := hback
  refine ⟨tree, before, suffix, mid, hpre, hq, fun x hx => hkeep x (by rw [hgate]; exact List.mem_append_left _ hx), ?_, real, err, hreal, herr, hno⟩
  intro path text r' hw hs
  refine hread path text r' hw ?_
  rw [← hs, hpre]
  exact (hstands mid (e :: rest) hgate _).symm

/-- An act at the end of a reading fails the clause, for each act of the closed type `Op`, once any text stands: the segment that
holds the read-back has no room for it, so no read after the act is there. -/
theorem act_after_readBack_fails {T : List (Event L E)} {e : Event L E} (hact : ¬ QuietOp e.op) {path : FilePath} {text : String}
    {r : Except IO.Error Unit} (hw : (⟨.writeFile path text, r⟩ : Event L E) ∈ T ++ [e])
    (hs : written (T ++ [e]) (parts path) = some text) {tree : FilePath} : ¬ ReadBack (T ++ [e]) tree := by
  rintro ⟨pre, suffix, hsplit, hq, hread, -⟩
  have hnil : suffix = [] := by
    rcases List.eq_nil_or_concat suffix with h | ⟨xs, x, rfl⟩
    · exact h
    · exfalso
      rw [List.concat_eq_append, ← List.append_assoc] at hsplit
      have hlast := (List.append_inj' hsplit (by simp)).2
      have : e = x := by simpa using hlast
      subst this
      exact hact (hq e (by simp))
  subst hnil
  cases hread path text r hw hs

/-- The neighbour of `act_after_readBack_fails`: reads and reports after the read-back keep the clause. -/
theorem ReadBack.append_quiet {t after : List (Event L E)} {tree : FilePath} (h : ReadBack t tree) (hq : Quiet after)
    (hk : ∀ x ∈ after, x.keepsFiles) : ReadBack (t ++ after) tree := by
  obtain ⟨pre, suffix, rfl, hs, hread, err, herr, hno⟩ := h
  refine ⟨pre, suffix ++ after, by simp, ?_, ?_, err, List.mem_append_left _ herr, hno⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hs e he
    · exact hq e he
  · intro path text r hw hst
    have hin : (⟨.writeFile path text, r⟩ : Event L E) ∈ pre ++ suffix := by
      simp only [List.append_assoc, List.mem_append] at hw ⊢
      rcases hw with hw | hw | hw
      · exact .inl hw
      · exact .inr hw
      · exact absurd (hk _ hw) (fun h => h.elim)
    have hsame : written (pre ++ suffix ++ after) (parts path) = written (pre ++ suffix) (parts path) := by
      rw [written_append, leavesAs_nil_of_keeps hk]
      rfl
    exact List.mem_append_left _ (hread path text r hin (by rw [← hsame]; simpa [List.append_assoc] using hst))

/-- Events before a reading that hold no act keep the clause. -/
theorem ReadBack.prepend_no_acts {a t : List (Event L E)} {tree : FilePath} (ha : ∀ e ∈ a, e.acted? = none) (h : ReadBack t tree) :
    ReadBack (a ++ t) tree := by
  obtain ⟨pre, suffix, rfl, hs, hread, err, herr, hno⟩ := h
  refine ⟨a ++ pre, suffix, by simp, hs, ?_, err, herr, hno⟩
  intro path text r hw hst
  have hin : (⟨.writeFile path text, r⟩ : Event L E) ∈ pre ++ suffix := by
    rcases List.mem_append.mp hw with hw | hw
    · cases ha _ hw
    · exact hw
  have hsame := written_after_no_acts (b := pre ++ suffix) ha (parts path)
  exact hread path text r hin (by rw [← hsame]; exact hst)

/-- The neighbour of `uncheckedCopy_fails`: a read and a copy of the text that already stands there change nothing the evidence is
about. So what `uncheckedCopy_fails` refuses is the unjudged text, and not the shape of the trace. -/
theorem judgedCopy_stands {T : List (Event L E)} {dir treeDir source path parent : FilePath} {text : String} {r : Reading}
    (hev : Evidence T dir treeDir (written T) r) (hq : written T (parts path) = some text) :
    Evidence (T ++ uncheckedCopy source path parent text) dir treeDir
      (written (T ++ uncheckedCopy source path parent text)) r := by
  have hsame : (written (T ++ uncheckedCopy (L := L) (E := E) source path parent text) : List String → Option String) = written T := by
    funext q
    rw [written_append]
    simp only [uncheckedCopy, leavesFrom, List.foldl_cons, List.foldl_nil, Event.leaves]
    by_cases hp : parts path = q
    · subst hp
      simp [hq]
    · simp [hp]
  rw [hsame]
  exact Evidence.mono (List.sublist_append_left _ _) hev

/-- After a write and a later write of another text at one path, with nothing after that writes or removes, what stands is the
last. -/
theorem rewritten_stands (a b c : List (Event L E)) (path : FilePath) (x y : String) (r₁ r₂ : Except IO.Error Unit)
    (hc : LeavesAs c []) :
    written (a ++ ⟨.writeFile path x, r₁⟩ :: b ++ ⟨.writeFile path y, r₂⟩ :: c) (parts path) = some y := by
  have := written_last_write (a ++ ⟨.writeFile path x, r₁⟩ :: b) c path y r₂ hc
  simpa [List.append_assoc] using this

end RegulaSpecification.Effects
