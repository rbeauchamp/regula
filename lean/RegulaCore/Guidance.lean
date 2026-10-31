import RegulaCore.Feedback
import RegulaCore.Guide
import RegulaCore.Prose
import RegulaCore.Setup
import RegulaCore.Verdict

/-! # Offline rule guidance for agents

The `regula` executable prints these texts; nothing here needs a network or another tool.
Every text is generated from the rule registry (`descriptor`), the rule explanations (`guide`)
and the `lake lint` exit codes (`Regula.Closed.Verdict.exitCodes`) of the installed Regula
build, so it matches that build by construction.

## Main declarations

- `explain`: the full rule as Markdown (`lake exe regula explain <ID>`).
- `rulesIndex`: the compact index of every rule (`lake exe regula rules`).
- `writingSections`, `writingSections_perm`: every rule exactly once, ordered for writing code
  rather than for auditing.
- `agentGuide`, `skill`: the agent briefing (`lake exe regula agent-guide`) and the same text
  as an Agent Skills `SKILL.md` (`lake exe regula skill`), within `agentGuideBudget` bytes. It
  prints each distinct compliant example once; a later rule with the same one names the rule
  that shows it (`sameExampleAs`, `sameExampleAs_spec`).
- `citation`, `citation_installed`, `agentGuideIn`, `skillIn`, `skill_unreleased`: the briefing
  tells an agent to link each rule ID it mentions to the rule's page, with a link to the
  installed build's edition, the one a finding prints, and names every rule through that same
  link itself; the briefing of each edition differs only in those links.
- `Command`, `parseCommand`, `parseCommand_arguments`, `parseCommand_sound`: the printing
  commands.
- `Invocation`, `parseInvocation`, `parseInvocation_arguments`, `parseInvocation_sound`: the
  whole command line, which adds `init` and `doctor` (`Regula.Setup`) to the printing commands.

## Checks at build time

The `#guard`s below evaluate, over the complete `RuleId.all` (`RuleId.mem_all`), that every
descriptor meets `RuleDescriptor.wellFormed` (nonempty agent fields within their byte budgets,
one-line requirement and remedy, distinct examples) and that the agent guide of every published
edition fits its budget.
They are compiled evaluation, not kernel proofs: kernel reduction of these long string
literals costs seconds per field. A failing check fails the build of this module, which the
acceptance build includes.
-/

namespace Regula.Guidance

open Regula.Site (guide)
open Regula.Closed (Verdict)

/-- Registry prose with repository links written as paths relative to the Regula package root. -/
def packageProse (text : String) : String := text.replace "(@repo/" "("

/-- A fence long enough to contain `text` (Markdown examples contain three-backtick fences). -/
def fenceFor (text : String) : String :=
  if (text.splitOn "```").length > 1 then "````" else "```"

/-- `text` in a fenced block of `language`. -/
def fenced (language text : String) : String :=
  let fence := fenceFor text
  let body := if text.endsWith "\n" then text else text ++ "\n"
  fence ++ language ++ "\n" ++ body ++ fence ++ "\n"

private def paragraphs (xs : List String) : String :=
  String.join (xs.map fun p => packageProse p ++ "\n\n")

private def numbered (xs : List String) : String :=
  String.join
      ((List.range xs.length).zip xs |>.map fun (i, p) => s!"{i + 1}. " ++ packageProse p ++ "\n")

/-- The `lake lint` exit codes, from the checker's own table (`Verdict.exitCodes`). -/
def exitCodes : String := Verdict.exitCodes

/-- The checked example pair when an adopter can apply it as shown; otherwise where the
qualification inputs are and the correction they demonstrate. -/
def examples (id : RuleId) : String :=
  let e := (descriptor id).examples
  match e.adopterExample with
  | some compliant =>
      "Noncompliant (`" ++ e.noncompliantPath id ++ "`):\n\n" ++
          fenced e.language.fence e.noncompliant ++ "\n" ++
      "Compliant (`" ++ e.compliantPath id ++ "`):\n\n" ++
          fenced e.language.fence compliant ++ "\n" ++
      e.correction ++ "\n\n"
  | none =>
      "The checked pair (`" ++ e.noncompliantPath id ++ "`, `" ++ e.compliantPath id ++
      "`) consists of qualification inputs, not project files. " ++ e.caption ++ "\n\n"

/-- What `checkedBy` says of a retired rule. -/
def notChecked : String :=
  "no check: the rule is retired to written guidance, which review checks"

/-- What checks a rule that is not retired: the Lake command that the specification hands RG2003
or RG2005 to, and `lake lint` for each other rule. -/
def activeCheck : RuleId → String
  | .sourceBuild => "`lake build --wfail`, which decides it in place of Regula"
  | .admission => "`lake check`, which decides it in place of Regula; Regula's checker does not \
      report it"
  | _ => "`lake lint`, over the finished build"

/-- What checks the rule now: no check for a rule whose lifecycle in the registry is retired
(`Lifecycle.isRetired`), which the specification's `fate` retires, and `activeCheck` for each
other rule. The retired case is read from the lifecycle, so no table can disagree with it. -/
def checkedBy (id : RuleId) : String :=
  if (descriptor id).lifecycle.isRetired then notChecked else activeCheck id

/-- The full rule as Markdown. For a rule whose subjects a registration declaration selects
(`registrationFor`: `Regula.RegisteredDecision`), only source options and flags are said not to
change the result. -/
def explain (id : RuleId) : String :=
  let d := descriptor id
  let g := guide id
  "# " ++ id.spelling ++ ": " ++ d.title ++ "\n\n" ++
  "**Requirement.** " ++ d.requirement ++ "\n\n" ++
  "- Category: " ++ d.category.label ++ "; scope: " ++ d.scope.label ++ "; subreason: `" ++
    d.applicability ++ "`\n" ++
  "- Normative clauses: " ++ "; ".intercalate (d.normativeClauses.map fun c =>
    c.label ++ " (`" ++ c.source ++ "`, " ++ c.url ++ ")") ++ "\n" ++
  "- Checked by: " ++ checkedBy id ++ "\n" ++
  "- Finding form: `" ++ Regula.Closed.findingForm ++ "`\n" ++
  "- Rule page: " ++ helpUrl id ++ "\n\n" ++
  "## Problem\n\n" ++ packageProse g.problem.toString ++ "\n\n" ++
  "## Why it matters\n\n" ++ paragraphs (d.rationale :: g.rationaleDetail) ++
  "## How to fix it\n\n" ++ d.remedy ++ "\n\n" ++ "Common compliant rewrites:\n\n" ++
      numbered d.rewrites ++ "\n" ++
  "## Examples\n\n" ++ examples id ++
  "## What triggers it\n\n" ++ paragraphs g.trigger ++
  "## Configuration and exceptions\n\n" ++
    (if d.lifecycle.isRetired then "No check reports this rule, so no option, attribute or flag \
      changes a result: the rule is written guidance, which review checks.\n\n"
    else "No source option" ++
      (if (registrationFor id).isSome then "" else ", attribute") ++ " or command-line flag \
      makes this rule pass on a claimed surface (" ++ installed.edition.url "enforcement/" ++
      ").\n\n") ++ paragraphs g.configuration ++
  "## Limitations\n\n" ++ paragraphs g.limitations ++
  "## Open review obligations\n\n" ++ "A passing result leaves these for review:\n\n" ++
    String.join (g.residuals.map fun r => "- `" ++ r.spelling ++ "`: " ++ r.description ++ ".\n") ++
    "\n" ++
  "Paths are relative to the Regula package root (in an adopting project, " ++
  "`.lake/packages/regula/`). The examples are the rule's registered example pair.\n"

/-- The mark after a retired rule's title in the rule index and the briefing, from its lifecycle;
empty for an active rule. -/
def retiredMark (id : RuleId) : String :=
  if (descriptor id).lifecycle.isRetired then " (retired: written guidance)" else ""

/-- The compact index of every rule. -/
def rulesIndex : String :=
  "# Regula rules\n\n" ++
  "Run `lake exe regula explain <ID>` for the full rule, `lake exe regula agent-guide` for the \
    briefing.\n\n" ++
  String.join (RuleId.all.map fun id =>
    "- " ++ id.spelling ++ " " ++ (descriptor id).title ++ retiredMark id ++ " — " ++
        (descriptor id).requirement ++ "\n")

/-- The rules grouped by what an agent is writing, each group with a one-line scope. -/
def writingSections : List (String × String × List RuleId) := [
  ("Every declaration", "Applies to each definition, theorem and instance in a claimed module.",
    [.proofHole, .projectAxiom, .compilerTrusting, .escapeHatch, .profileExceeded, .unknownAxiom,
     .sourceBuild, .admission]),
  ("Documentation in Lean sources",
      "Applies to claimed modules and public declarations that state a material claim.",
    [.moduleDocumentation, .materialDocumentation, .materialIntent]),
  ("Executable code",
      "Applies to `ExecutableContract` registrations, `RegisteredDecision` functions and code \
        reached from executable roots. The shared-test rule compares names: a copy of a test \
        under a second name passes. A shared function with a result other than `Bool` or `BEq`, \
        and a field of a structure that the two sides read, are not refused.",
    [.executableContract, .decisionContract, .sharedTest, .executionBoundary,
      .executionUnresolved]),
  ("Project configuration",
    "Applies to `foundation_manifest.json`, the Lake options of claimed targets and the build \
      environment.",
    [.configuration, .communityConfiguration, .closedSubset, .coverage, .environment]),
  ("Lean examples in Markdown", "Applies to `lean` fences in the project's Markdown documentation.",
    [.positiveExample, .negativeExample, .trustedExample, .fenceStructure])]

/-- The briefing lists every registered rule exactly once. -/
theorem writingSections_perm : List.Perm (writingSections.flatMap (·.2.2)) RuleId.all := by
  decide

/-- Every rule in the briefing's order. -/
def briefingOrder : List RuleId := writingSections.flatMap (·.2.2)

/-- The earlier rule of the briefing whose compliant example has exactly the bytes of `id`'s, if
any: the briefing prints each distinct compliant example once. -/
def sameExampleAs (id : RuleId) : Option RuleId :=
  (briefingOrder.takeWhile (· != id)).find? fun other =>
    (descriptor other).examples.adopterExample.isSome &&
      (descriptor other).examples.adopterExample == (descriptor id).examples.adopterExample

/-- A rule that refers to another's example refers to an earlier rule with the same compliant
example. -/
theorem sameExampleAs_spec {id other : RuleId} (h : sameExampleAs id = some other) :
    (descriptor other).examples.adopterExample = (descriptor id).examples.adopterExample ∧
      other ∈ briefingOrder.takeWhile (· != id) := by
  unfold sameExampleAs at h
  refine ⟨?_, List.mem_of_find?_eq_some h⟩
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-- Rule `id`'s ID as a Markdown link to its page in edition `e`. -/
def citation (e : Edition) (id : RuleId) : String :=
  "[" ++ id.spelling ++ "](" ++ e.url id.route ++ ")"

/-- One rule of the briefing of edition `e`: identity, requirement, remedy and the compliant
example (named by the earlier rule that shows the same one), or the correction where the checked
files are qualification inputs. Every rule ID it names, its own and those of the registry's
prose, is a `citation` in `e`. -/
def briefRule (e : Edition) (id : RuleId) : String :=
  let d := descriptor id
  let cited := Prose.linkIds (citation e)
  "### " ++ citation e id ++ " " ++ d.title ++ retiredMark id ++ "\n\n" ++ cited d.requirement ++
      "\nFix: " ++
      cited d.remedy ++ "\n\n" ++
  match d.examples.adopterExample, sameExampleAs id with
  | some _, some other => "Compliant example: as " ++ citation e other ++ ".\n"
  | some compliant, none => fenced d.examples.language.fence compliant
  | none, _ => "Compliant form: " ++ cited d.examples.correction ++ "\n"

/-- In the installed build's edition, a citation links to the page that a finding links
(`helpUrl`, `Regula.Shell.page`): a release's own page (`helpUrl_release`), and a development
page exactly for an unreleased build (`helpUrl_dev_iff`). -/
theorem citation_installed (id : RuleId) :
    citation installed.edition id = "[" ++ id.spelling ++ "](" ++ helpUrl id ++ ")" := rfl

/-- The agent briefing of a build whose pages are edition `e`: how to check, how findings read,
how to cite a rule, and every rule for writing code. Only the citations' links depend on `e`. -/
def agentGuideIn (e : Edition) : String :=
  "# Regula agent briefing\n\n" ++
  "This project's Lean code and proofs must meet the Regula standard. Apply these rules while " ++
  "writing Lean, not only after the linter runs. This is the complete rule set of the " ++
  "installed Regula version, ordered for writing code. A rule marked retired is written " ++
  "guidance: no check reports it, and review checks it.\n\n" ++
  "- Build the claimed targets with `lake build --wfail`, then check the finished build with " ++
  "`lake lint`. Exit codes: " ++ exitCodes ++ ".\n" ++
  "- A finding is one line: its rule ID, the constant and its module, what is wrong, and the " ++
  "link to the rule's page. `lake exe regula explain <ID>` prints the full rule, with why, " ++
  "common rewrites and a compliant example, offline; `lake exe regula rules` lists all rules.\n" ++
  "- When you mention a rule ID in an issue, a comment, a pull request or a document, link it " ++
  "to the rule's page for the installed Regula build, the link that a finding " ++
  "prints: `" ++ citation e .executionBoundary ++ "`.\n" ++
  "- No option, attribute or flag waives a rule on a claimed surface. Do not disable a Lean " ++
  "warning, weaken a statement, or drop a registration to pass.\n" ++
  "- Follow the Lean community's style, naming and documentation conventions (standard §6.7). " ++
  "Every claimed target enables `linter.missingDocs` (document every definition) in its " ++
  "`leanOptions`. Review checks this required setting. " ++ citation e .communityConfiguration ++
  " admits that option by name without checking its value. `lake build --wfail` rejects " ++
  "warnings that enabled linters emit. Run Batteries' linters with `lake build && lake exe runLinter`. " ++
  "Disable a community linter only for a single declaration, " ++
  "where its guidance allows, with the reason; that never discharges a rule.\n" ++
  "- Passing is mechanical: a theorem must still state the intended claim, with its hypotheses " ++
  "and limits, which review checks.\n\n" ++
  String.join (writingSections.map fun (heading, scope, rules) =>
    "## " ++ heading ++ "\n\n" ++ scope ++ "\n\n" ++ String.join
        (rules.map fun id => briefRule e id ++ "\n"))

/-- The agent briefing of the installed build, whose citation links name its edition
(`citation_installed`). -/
def agentGuide : String := agentGuideIn installed.edition

/-- Byte budget of the agent briefing, so pasting it into an agent's context stays cheap. -/
def agentGuideBudget : Nat := 20480

/-- The briefing of a build whose pages are edition `e`, as an Agent Skills `SKILL.md`. -/
def skillIn (e : Edition) : String :=
  "---\nname: regula\n" ++
  "description: Regula, the strict standard that this project's Lean code and proofs must meet. " ++
  "Use before writing or changing Lean definitions, theorems, proofs, lakefile or " ++
  "foundation_manifest.json, or Lean examples in Markdown, and when `lake lint` reports an RG rule \
    ID.\n" ++
  "---\n\n" ++ agentGuideIn e

/-- The installed build's briefing as an Agent Skills `SKILL.md`. -/
def skill : String := skillIn installed.edition

/-- An unreleased build's skill is the development edition's, which is the committed
`.agents/skills/regula/SKILL.md` of this repository (`Regula.RegistryChecks`): `main` is always
unreleased, and the release commit changes only `installed`, so its tree keeps that file. -/
theorem skill_unreleased (h : installed = .unreleased) : skill = skillIn .dev := by
  simp [skill, h, Build.edition]

/-- No agent-facing field carries a site-only `@repo/` link token. -/
def plainFields (id : RuleId) : Bool :=
  let d := descriptor id
  ([d.requirement, d.rationale, d.remedy, d.examples.caption] ++ d.rewrites).all fun s =>
    (s.splitOn "@repo/").length == 1

-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard RuleId.all.all fun id => (descriptor id).wellFormed && plainFields id
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
-- It covers the installed build's briefing, whose edition is published (`installed_published`).
#guard published.all fun e => (agentGuideIn e).utf8ByteSize ≤ agentGuideBudget

/-- The `regula` command line. -/
inductive Command where
  /-- Print rule `id` in full as Markdown (`explain`). -/
  | explain (id : RuleId)
  /-- Print the compact index of every rule (`rulesIndex`). -/
  | rules
  /-- Print the agent briefing of the standard (`agentGuide`). -/
  | agentGuide
  /-- Print the briefing as an Agent Skills `SKILL.md` (`skill`). -/
  | skill
  /-- Print the usage text (`usage`). -/
  | help
  deriving DecidableEq

/-- The canonical arguments of each command. -/
def Command.arguments : Command → List String
  | .explain id => ["explain", id.spelling]
  | .rules => ["rules"]
  | .agentGuide => ["agent-guide"]
  | .skill => ["skill"]
  | .help => ["help"]

/-- The usage text: every command, what it prints, and the exit codes. -/
def usage : String :=
  "usage: lake exe regula init [--skill] | doctor | explain <RULE-ID> | rules | agent-guide |\n" ++
  "       skill | help\n" ++
  "  init [--skill]     write the missing setup: lint driver, leanOptions, a starter\n" ++
  "                     foundation_manifest.json and agent guidance (an AGENTS.md section,\n" ++
  "                     or with --skill .agents/skills/regula/SKILL.md); changes nothing set\n" ++
  "  doctor             check the setup and print each missing or wrong piece with its fix\n" ++
  "  explain <RULE-ID>  the full rule as Markdown: requirement, rationale, remedy, examples\n" ++
  "  rules              the compact index of every rule\n" ++
  "  agent-guide        the agent briefing of the standard, ordered for writing code\n" ++
  "  skill              the briefing as an Agent Skills SKILL.md\n" ++
  "Output matches this installed Regula build and needs no network.\n" ++
  "exit codes: 0 printed or set up, 1 a setup problem remains (init, doctor),\n" ++
  "  2 invalid invocation or unknown rule ID"

/-- Unknown commands, extra arguments and unknown rule IDs are refused. -/
def parseCommand : List String → Except String Command
  | ["explain", s] => match RuleId.parse? s with
    | some id => .ok (.explain id)
    | none => .error s!"unknown rule ID: {s} (run `lake exe regula rules`)"
  | ["rules"] => .ok .rules
  | ["agent-guide"] => .ok .agentGuide
  | ["skill"] => .ok .skill
  | ["help"] | ["--help"] | ["-h"] => .ok .help
  | [] => .error "missing command"
  | args => .error s!"unknown or incomplete command: {" ".intercalate args}"

/-- Every command is reachable from its canonical arguments. -/
theorem parseCommand_arguments (c : Command) : parseCommand c.arguments = .ok c := by
  cases c with
  | explain id => simp [Command.arguments, parseCommand, RuleId.parse_spelling]
  | _ => rfl

/-- A parsed command is exactly what its arguments name. -/
theorem parseCommand_sound {args : List String} {c : Command} (h : parseCommand args = .ok c) :
    args = c.arguments ∨ (c = .help ∧ (args = ["--help"] ∨ args = ["-h"])) := by
  unfold parseCommand at h
  split at h
  · rename_i s
    split at h
    · rename_i id hid
      cases h
      exact Or.inl (by simp [Command.arguments, RuleId.spelling_of_parse hid])
    · cases h
  all_goals (cases h <;> simp [Command.arguments])

/-- The text a command prints. -/
def output : Command → String
  | .explain id => explain id
  | .rules => rulesIndex
  | .agentGuide => agentGuide
  | .skill => skill
  | .help => usage

/-- A `regula` invocation: a printing command, or a setup command (`Regula.Setup`). -/
inductive Invocation where
  /-- Print the output of `command`. -/
  | print (command : Command)
  /-- Write the missing setup, with guidance `guidance` when the project has none. -/
  | init (guidance : Regula.Setup.Guidance)
  /-- Check the setup and print each problem with its fix. -/
  | doctor
  deriving DecidableEq

/-- The canonical arguments of each invocation. -/
def Invocation.arguments : Invocation → List String
  | .print command => command.arguments
  | .init .agentsMd => ["init"]
  | .init .skill => ["init", "--skill"]
  | .doctor => ["doctor"]

/-- The whole command line: `init`, `init --skill` and `doctor`, and otherwise `parseCommand`,
which refuses unknown commands, extra arguments and unknown rule IDs. -/
def parseInvocation : List String → Except String Invocation
  | ["init"] => .ok (.init .agentsMd)
  | ["init", "--skill"] => .ok (.init .skill)
  | ["doctor"] => .ok .doctor
  | args => .print <$> parseCommand args

/-- Every invocation is reachable from its canonical arguments. -/
theorem parseInvocation_arguments (i : Invocation) : parseInvocation i.arguments = .ok i := by
  cases i with
  | print c =>
    cases c with
    | explain id =>
      simp [Invocation.arguments, Command.arguments, parseInvocation, parseCommand,
        RuleId.parse_spelling]
      rfl
    | _ => rfl
  | init g => cases g <;> rfl
  | doctor => rfl

/-- A parsed invocation is exactly what its arguments name. -/
theorem parseInvocation_sound {args : List String} {i : Invocation}
    (h : parseInvocation args = .ok i) :
    args = i.arguments ∨ (i = .print .help ∧ (args = ["--help"] ∨ args = ["-h"])) := by
  unfold parseInvocation at h
  split at h
  · cases h; exact .inl rfl
  · cases h; exact .inl rfl
  · cases h; exact .inl rfl
  · cases hc : parseCommand args with
    | error e => rw [hc] at h; cases h
    | ok c =>
      rw [hc] at h
      cases h
      rcases parseCommand_sound hc with h | ⟨rfl, h⟩
      · exact .inl h
      · exact .inr ⟨rfl, h⟩

end Regula.Guidance
