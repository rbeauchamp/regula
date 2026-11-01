/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Language

/-!
# What the owner confirmed, stated apart from the code's own values

The owner's restatement (`confirmation.md`) names what the language check refuses and admits, and that a run's output says which
verdict it gave. Each statement here holds its expected value as a literal, and none reads a table or a function under proof for it:
each is about `decision`, or about the text of `Report.label` and `Verdict.proofLine`, the definitions that run. So a table or a
sentence replaced by a constant fails this module's build. A theorem whose expected value came from the table could show only that the
table agrees with itself.

An example is stated over the parser's node kinds or the decision's input. The kinds and the shapes of the trees below are what Lean's
own `parseCommand` and `parseHeader` gave for the owner's examples at v4.35.0 (`README.md`, "What was measured"). That those trees are what
the parser gives for a project's real text is H1, which these theorems do not reach. Admitting Regula's own core cannot be stated this way:
it is the gate's run of the full gate on this checkout, an observation, and `core_configuration_admitted` states only the configuration's part.
-/

namespace RegulaSpecification.Owner

open Lean (Name Syntax)
open Regula.Language
open RegulaSpecification.Language

/-! ## What the check refuses -/

/-- `s` is at a position that the check reads of some file of the reading. -/
def Holds (r : Reading) (s : Syntax) : Prop :=
  ∃ f ∈ r.files, ∃ t, (t = f.header ∨ t ∈ f.commands) ∧ Occurs s t

/-- The check reads everything but open text, so no kind that holds a construct can be hidden from `Occurs` by entering the table
of kinds it does not enter. -/
theorem unread_kinds_are_open_text :
    ∀ k ∈ leafKinds, k ∈ [`str, `num, `char, `name, `scientific, `fieldIdx, `interpolatedStrLitKind, `hygieneInfo,
      `Lean.Parser.Command.docComment, `Lean.Parser.Command.moduleDoc, `Lean.Parser.Command.eoi] := by
  decide +kernel

/-- Everything that the decision reads before it reads the files is in order, so what it says is about the files. -/
def Reached (r : Reading) : Prop :=
  ConfigClosed r ∧ ReadInFull r ∧ ¬ RequiresDependency r ∧ ¬ MathlibReached r ∧ Covered r

/-- What refusing a construct is: the reading is never admitted, and once everything before the files is in order the outcome is
`.refused`. Earlier in the decision it can be another refusal to admit, such as `.proofOnly` for a project with a dependency. -/
def Refuses (r : Reading) : Prop :=
  decision r ≠ .admitted ∧ (Reached r → decision r = .refused)

theorem refuses_of_position {r : Reading} {f : FileRead} {s t : Syntax} (hf : f ∈ r.files)
    (ht : t = f.header ∨ t ∈ f.commands) (ho : Occurs s t) (hs : ¬ PositionAdmitted f.scopedParsers s) : Refuses r := by
  have hne : decision r ≠ .admitted :=
    offender_not_admitted r f hf s t ht ((mem_offenders_iff _ _ _).mpr ⟨ho, hs⟩)
  refine ⟨hne, fun ⟨c, g, k, m, v⟩ => ?_⟩
  obtain ⟨-, -, -, -, -, h5, h6⟩ := (language_meets_iff decision).mp decision_meets
  by_cases o : FilesAdmitted r
  · exact absurd (h6 r c g k m v o) hne
  · exact h5 r c g k m v o

/-- The kinds that Lean's parser gives for `run_cmd`, `#eval`, `#guard`, `run_tac`, `by_elab`, `native_decide`, `macro`, `syntax`,
`notation`, `elab`, `initialize` and the `macro` of `@[local macro k]`, in that order. -/
def namedKinds : List Name :=
  [`Lean.runCmd, `Lean.Parser.Command.eval, `Lean.Parser.Command.guardCmd, `Lean.Parser.Tactic.runTac,
    `Lean.byElab, `Lean.Parser.Tactic.nativeDecide, `Lean.Parser.Command.macro, `Lean.Parser.Command.syntax,
    `Lean.Parser.Command.notation, `Lean.Parser.Command.elab, `Lean.Parser.Command.initialize, `Lean.Parser.Attr.macro]

theorem namedKinds_outside : ∀ k ∈ namedKinds, k ∉ kinds ∧ k ∉ leafKinds := by
  decide +kernel

/-- Each of those kinds is refused, wherever a file holds it. -/
theorem refuses_named_kinds {r : Reading} {i : Lean.SourceInfo} {k : Name} {as : Array Syntax}
    (hk : k ∈ namedKinds) (h : Holds r (.node i k as)) : Refuses r := by
  obtain ⟨f, hf, t, ht, ho⟩ := h
  have hout := namedKinds_outside k hk
  exact refuses_of_position hf ht ho fun hp => hp.1.elim hout.1 hout.2

/-- `decide +native`: the configuration item that Lean's parser gives for `+native`, wherever a file holds it. -/
theorem refuses_decide_native {r : Reading} {i i' : Lean.SourceInfo} {raw : Substring.Raw} {pre : List Syntax.Preresolved}
    {as : Array Syntax} (ha : as[1]? = some (.ident i' raw `native pre))
    (h : Holds r (.node i `Lean.Parser.Tactic.posConfigItem as)) : Refuses r := by
  obtain ⟨f, hf, t, ht, ho⟩ := h
  refine refuses_of_position hf ht ho fun hp => ?_
  obtain ⟨_, c, _, _, hc, hm⟩ := hp.2.2.2.1 rfl
  rw [ha] at hc
  cases Option.some.inj hc
  exact absurd hm (by decide +kernel)

theorem not_closed_refused (r : Reading) (h : ¬ ConfigClosed r) : decision r = .refused :=
  ((language_meets_iff decision).mp decision_meets).1 r h

/-- A `lakefile.lean` is refused. -/
theorem refuses_lakefile_lean (r : Reading) (h : r.leanConfig = true) : decision r = .refused :=
  not_closed_refused r fun hc => by simp [hc.2.1] at h

/-- The keys of Lake's TOML that hold a plugin, at each table that can hold one. -/
def pluginKeys : List Name := [`plugins, `lean_lib.plugins, `lean_exe.plugins]

theorem pluginKeys_outside :
    ∀ k ∈ pluginKeys, k.getRoot ≠ `require ∧ k ∉ configKeys ∧ ∀ o ∈ options, k ≠ `leanOptions ++ o := by
  decide +kernel

/-- A plugin in Lake's TOML is refused. -/
theorem refuses_plugin_key (r : Reading) {k : Name} (hk : k ∈ pluginKeys) (h : k ∈ r.configKeys) :
    decision r = .refused := by
  obtain ⟨hr, hn, ho⟩ := pluginKeys_outside k hk
  refine not_closed_refused r fun hc => ?_
  rcases hc.2.2.2 k h hr with hm | ⟨o, hm, he⟩
  · exact hn hm
  · exact ho o hm he

/-! ## What the check admits -/

/-- A node with no source position. -/
private abbrev n (k : Name) (xs : List Syntax) : Syntax := .node .none k ⟨xs⟩

/-- A token. -/
private abbrev a (v : String) : Syntax := .atom .none v

/-- An identifier. -/
private abbrev i (m : Name) : Syntax := .ident .none default m []

/-- An empty optional argument. -/
private abbrev e : Syntax := n `null []

/-- The modifiers of a declaration that has none but `attrs`. -/
private abbrev mods (attrs : Syntax) : Syntax :=
  n `Lean.Parser.Command.declModifiers [e, attrs, e, e, e, e, e]

/-- `example : True := by tac`, as Lean's parser gives it. -/
private abbrev byExample (tac : Syntax) : Syntax :=
  n `Lean.Parser.Command.declaration [mods e,
    n `Lean.Parser.Command.example [a "example",
      n `Lean.Parser.Command.optDeclSig [e, n `null [n `Lean.Parser.Term.typeSpec [a ":", i `True]]],
      n `Lean.Parser.Command.declValSimple [a ":=",
        n `Lean.Parser.Term.byTactic [a "by",
          n `Lean.Parser.Tactic.tacticSeq [n `Lean.Parser.Tactic.tacticSeq1Indented [n `null [tac]]]],
        n `Lean.Parser.Termination.suffix [e, e], e]]]

/-- `+item` in a tactic, as Lean's parser gives it. -/
private abbrev plusItem (item : Name) : Syntax :=
  n `Lean.Parser.Tactic.optConfig [n `null [n `Lean.Parser.Tactic.configItem [n `Lean.Parser.Tactic.posConfigItem [a "+", i item]]]]

/-- The library code that the owner's words name, and the one attribute of the form `@[name]` that Regula's core uses: `by simp`, `by omega`,
`by decide +kernel`, `variable (n : Nat)`, `inductive T where | a deriving DecidableEq` and `@[expose] def f : Nat := 1`. -/
def libraryCode : List Syntax :=
  [byExample (n `Lean.Parser.Tactic.simp [a "simp", n `Lean.Parser.Tactic.optConfig [e], e, e, e, e]),
    byExample (n `Lean.Parser.Tactic.omega [a "omega", n `Lean.Parser.Tactic.optConfig [e]]),
    byExample (n `Lean.Parser.Tactic.decide [a "decide", plusItem `kernel]),
    n `Lean.Parser.Command.variable [a "variable",
      n `null [n `Lean.Parser.Term.explicitBinder [a "(", n `null [i `n], n `null [a ":", i `Nat], e, a ")"]]],
    n `Lean.Parser.Command.declaration [mods e,
      n `Lean.Parser.Command.inductive [a "inductive", n `Lean.Parser.Command.declId [i `T, e],
        n `Lean.Parser.Command.optDeclSig [e, e], n `null [a "where"],
        n `null [n `Lean.Parser.Command.ctor [e, a "|", mods e, i `a, n `Lean.Parser.Command.optDeclSig [e, e]]], e,
        n `Lean.Parser.Command.optDeriving [n `null [a "deriving", n `null [n `Lean.Parser.Command.derivingClass [e, i `DecidableEq]]]], e]],
    n `Lean.Parser.Command.declaration [
      mods (n `null [n `Lean.Parser.Term.attributes [a "@[",
        n `null [n `Lean.Parser.Term.attrInstance [n `Lean.Parser.Term.attrKind [e], n `Lean.Parser.Attr.simple [i `expose, e]]], a "]"]]),
      n `Lean.Parser.Command.definition [a "def", n `Lean.Parser.Command.declId [i `f, e],
        n `Lean.Parser.Command.optDeclSig [e, n `null [n `Lean.Parser.Term.typeSpec [a ":", i `Nat]]],
        n `Lean.Parser.Command.declValSimple [a ":=", n `num [a "1"], n `Lean.Parser.Termination.suffix [e, e], e], e]]]

/-- The key paths of Regula's own `lakefile.toml`, by what its text states. -/
def coreKeys : List Name :=
  [`name, `version, `description, `keywords, `license, `licenseFiles, `srcDir, `defaultTargets, `lintDriver, `lintDriverArgs,
    `leanOptions.warningAsError, `leanOptions.autoImplicit, `leanOptions.relaxedAutoImplicit, `leanOptions.linter.missingDocs,
    `lean_lib.name, `lean_lib.globs, `lean_exe.name, `lean_exe.root, `lean_exe.supportInterpreter]

/-- A project of one `module` file that holds `commands`, with the pinned toolchain and the key paths `keys`. -/
def readingOf (keys : List Name) (commands : List Syntax) : Reading where
  toolchainFile := some "leanprover/lean4:v4.35.0"
  leanConfig := false
  configKeys := keys
  openPaths := []
  roots := [`Example]
  reached := [`Example]
  files := [{ module := `Example,
              header := n `Lean.Parser.Module.header [n `null [n `Lean.Parser.Module.moduleTk [a "module"]], e, e],
              commands := commands ++ [n `Lean.Parser.Command.eoi [a ""]],
              parsed := true,
              scopedParsers := [] }]
  unread := []

/-- It admits library code that uses `simp`, `omega`, `decide +kernel`, `variable` and `deriving DecidableEq`. -/
theorem admits_library_code : decision (readingOf [`name] libraryCode) = .admitted := by
  decide +kernel

/-- Regula's own Lake configuration is admitted, on the pinned toolchain's text. The rest of admitting Regula's own core is observed, by the gate. -/
theorem core_configuration_admitted : decision (readingOf coreKeys []) = .admitted := by
  decide +kernel

/-- `run_cmd pure ()`, in the tree Lean's parser gives, is refused in that same project. -/
theorem refuses_run_cmd_in_that_project :
    decision (readingOf [`name] [n `Lean.runCmd [a "run_cmd", n `Lean.Parser.Term.doSeqIndent [n `null []]]]) = .refused := by
  decide +kernel

/-- `decide +native`, in the tree Lean's parser gives, is refused in that same project, where `decide +kernel` is admitted. -/
theorem refuses_decide_native_in_that_project :
    decision (readingOf [`name] [byExample (n `Lean.Parser.Tactic.decide [a "decide", plusItem `native])]) = .refused := by
  decide +kernel

/-- Another Lean named in `lean-toolchain` is refused in that same project. -/
theorem refuses_another_toolchain :
    decision { readingOf [`name] [] with toolchainFile := some "leanprover/lean4:v4.34.0" } = .refused := by
  decide +kernel

/-! ## What the output says -/

open Regula.Closed in
/-- The last line of each proof verdict, word for word. -/
theorem proof_verdict_lines :
    Verdict.proofLine .pass = "regula: proof verdict: pass, which says nothing about what ran during the build" ∧
    Verdict.proofLine .fail = "regula: proof verdict: fail" ∧
    Verdict.proofLine .incomplete = "regula: proof verdict: incomplete (RG2001)" := by
  decide +kernel

open Regula.Closed in
/-- The last line of each report of the full gate, word for word. -/
theorem full_gate_lines :
    Report.label (.full .pass) =
      "regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.35.0" ∧
    Report.label (.full .fail) = "regula: full verdict: fail" ∧
    Report.label (.full .incomplete) = "regula: full verdict: incomplete" ∧
    Report.label .proofOnly =
      "regula: only a proof verdict is possible for this project, and nothing was built, so no full verdict: `lake build --wfail`, `lake check` and `lake lint` in the project give it, and they run the project's code and its dependencies'" ∧
    Report.label .refused = "regula: refused before compiling (RG1010), so no build ran and no verdict is given" ∧
    Report.label .incomplete = "regula: incomplete (RG2001): the check could not read the project, so no build ran" := by
  decide +kernel

open Regula.Closed in
/-- So neither verdict can be mistaken for the other: each line of the proof verdict starts with the words `regula: proof verdict: `, each of the full
verdict with `regula: full verdict: `, and no other report's line starts with either. -/
theorem verdicts_named :
    (∀ v : Verdict, "regula: proof verdict: ".isPrefixOf (Verdict.proofLine v) = true) ∧
    (∀ v : Verdict, "regula: full verdict: ".isPrefixOf (Report.label (.full v)) = true) ∧
    (∀ r ∈ [Report.proofOnly, .refused, .incomplete],
      "regula: proof verdict: ".isPrefixOf (Report.label r) = false ∧ "regula: full verdict: ".isPrefixOf (Report.label r) = false) := by
  refine ⟨fun v => ?_, fun v => ?_, ?_⟩
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel
  · decide +kernel

end RegulaSpecification.Owner
