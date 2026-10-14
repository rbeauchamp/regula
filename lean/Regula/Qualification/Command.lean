/-! # The command line of `qualify`

The closed vocabulary of the selections `lake exe qualify` accepts (`Command`), the argument list
of each (`Command.arguments`) and the parser the dispatcher runs (`Command.parse`), which accepts
exactly those lists (`Command.parse_sound`, `Command.parse_arguments`). The evidence document of
each selection (`Command.evidence`) is the one that the leading arguments of its list name
(`Evidence.named_of_parse`), the reading that marks it before a run and in a refusal. The
inventory of campaigns (`Regula.Campaigns`) classifies each form of selection by the workflow job
that runs it. This module imports nothing, so that inventory and its checks can import it beside
the other executables' vocabularies. -/
namespace Regula.Qualification

/-- A group of the dependency-snapshot controls (`qualify acceptance-snapshots GROUP`). -/
inductive SnapshotGroup where
  /-- Ignored Git and non-Git dependency input coverage and mutation. -/
  | dependencies
  /-- RG3001 fresh, incremental and build-lint history refusal and restoration. -/
  | history
  /-- The dirty decision against a literal-pathspec status. -/
  | gitStatus
  /-- The three groups under one deadline. -/
  | all
  deriving DecidableEq, Repr

/-- The argument that names the group. -/
def SnapshotGroup.spelling : SnapshotGroup → String
  | .dependencies => "dependencies"
  | .history => "history"
  | .gitStatus => "git-status"
  | .all => "all"

/-- The group an argument names. -/
def SnapshotGroup.parse : String → Option SnapshotGroup
  | "dependencies" => some .dependencies
  | "history" => some .history
  | "git-status" => some .gitStatus
  | "all" => some .all
  | _ => none

/-- Every group's argument names it. -/
theorem SnapshotGroup.parse_spelling (group : SnapshotGroup) :
    parse group.spelling = some group := by
  cases group <;> rfl

/-- A group of the acceptance fault controls (`qualify acceptance GROUP --evidence PATH`): only
`fences`, the faults injected into the documentation step's compilation output. -/
inductive AcceptanceGroup where
  /-- A missing, a duplicated and a misindexed fence result. -/
  | fences
  deriving DecidableEq, Repr

/-- The argument that names the group. -/
def AcceptanceGroup.spelling : AcceptanceGroup → String
  | .fences => "fences"

/-- The group an argument names. -/
def AcceptanceGroup.parse : String → Option AcceptanceGroup
  | "fences" => some .fences
  | _ => none

/-- A group the parser accepts is the one its argument spells. -/
theorem AcceptanceGroup.parse_sound {text : String} {group : AcceptanceGroup}
    (h : parse text = some group) : text = group.spelling := by
  unfold parse at h; split at h <;> first | (cases h; rfl) | cases h

/-- A selection of `lake exe qualify`, one constructor for each form of its command line. -/
inductive Command where
  /-- `registry`: the registry controls. -/
  | registry
  /-- `native`: the native linter controls. -/
  | native
  /-- `combined`: registry, native copy-workspace and consumer-domain controls, then native
  linter beside unique-constants. -/
  | combined
  /-- `unique-constants`: no constant declared by two modules of a claimed environment. -/
  | uniqueConstants
  /-- `native-launcher`: the paired launcher diagnostic. -/
  | nativeLauncher
  /-- `rule-examples --evidence PATH`: the whole corpus. -/
  | ruleExamples (evidence : String)
  /-- `rule-examples --evidence PATH --rules RULE ...`: the corpus records of those rules. -/
  | ruleExamplesRules (evidence : String) (rules : List String)
  /-- `rule-examples --evidence PATH --shard K/N`: one shard of the corpus. -/
  | ruleExamplesShard (evidence spec : String)
  /-- `producers`. -/
  | producers
  /-- `producers --evidence PATH`: the campaign, and its export. -/
  | producersExport (evidence : String)
  /-- `producers-combined`: `producers`, then `history`. -/
  | producersCombined
  /-- `history`. -/
  | history
  /-- `self-audit`. -/
  | selfAudit
  /-- `self-audit --shard K/4`. -/
  | selfAuditShard (spec : String)
  /-- `self-audit-module MODULE SOURCE`: the self-audit's worker for one module. -/
  | selfAuditModule (module source : String)
  /-- `self-audit-json-module MODULE`: the self-audit's worker for one module's `Json`
  comparisons. -/
  | selfAuditJsonModule (module : String)
  /-- `environments --evidence PATH`. -/
  | environments (evidence : String)
  /-- `acceptance GROUP --evidence PATH`. -/
  | acceptance (group : AcceptanceGroup) (evidence : String)
  /-- `acceptance-snapshots GROUP`. -/
  | acceptanceSnapshots (group : SnapshotGroup)
  /-- `prep-measure`. -/
  | prepMeasure
  /-- `documentation-dependencies`. -/
  | documentationDependencies
  /-- `input-inventory`. -/
  | inputInventory
  /-- `receipt-boundaries`. -/
  | receiptBoundaries
  /-- `observers`: each program of the package recorded its removal check. -/
  | observers
  /-- `closure-evidence`. -/
  | closureEvidence
  /-- `configuration-capture`. -/
  | configurationCapture
  /-- `verso-recorded-paths`. -/
  | versoRecordedPaths
  /-- `copy-relocation`. -/
  | copyRelocation
  /-- `copy-relocation-load PROJECT COPIES`: the `copy-relocation` control's worker for the loads
  of one project and of its copy. -/
  | copyRelocationLoad (project copies : String)
  /-- `copy-relocation-git SCRATCH`: the `copy-relocation` control's process for its steps that run
  Git and Lake, with Git's repository variables of its parent's choosing. -/
  | copyRelocationGit (scratch : String)
  /-- `fence-evidence`. -/
  | fenceEvidence
  /-- `frozen-exits`. -/
  | frozenExits
  /-- `documentation-source`. -/
  | documentationSource
  /-- `documentation-source --source-read-only`. -/
  | documentationSourceReadOnly
  /-- `enumeration`: the constructor refuses each failed listing of a stand-in program. -/
  | enumeration
  /-- `enumeration-copy SOURCE TARGET`: the worker of `enumeration`, one copy. -/
  | enumerationCopy (source target : String)
  /-- `enumeration-failure`: a failed read of a directory, injected through device-mapper. -/
  | enumerationFailure
  /-- `readers`: no declaration of a module of a package of the repository refers to Lean's
  directory readers. -/
  | readers
  deriving DecidableEq, Repr

/-- The argument list of each selection. -/
def Command.arguments : Command → List String
  | .registry => ["registry"]
  | .native => ["native"]
  | .combined => ["combined"]
  | .uniqueConstants => ["unique-constants"]
  | .nativeLauncher => ["native-launcher"]
  | .ruleExamples evidence => ["rule-examples", "--evidence", evidence]
  | .ruleExamplesRules evidence rules =>
      "rule-examples" :: "--evidence" :: evidence :: "--rules" :: rules
  | .ruleExamplesShard evidence spec => ["rule-examples", "--evidence", evidence, "--shard", spec]
  | .producers => ["producers"]
  | .producersExport evidence => ["producers", "--evidence", evidence]
  | .producersCombined => ["producers-combined"]
  | .history => ["history"]
  | .selfAudit => ["self-audit"]
  | .selfAuditShard spec => ["self-audit", "--shard", spec]
  | .selfAuditModule module source => ["self-audit-module", module, source]
  | .selfAuditJsonModule module => ["self-audit-json-module", module]
  | .environments evidence => ["environments", "--evidence", evidence]
  | .acceptance group evidence => ["acceptance", group.spelling, "--evidence", evidence]
  | .acceptanceSnapshots group => ["acceptance-snapshots", group.spelling]
  | .prepMeasure => ["prep-measure"]
  | .documentationDependencies => ["documentation-dependencies"]
  | .inputInventory => ["input-inventory"]
  | .receiptBoundaries => ["receipt-boundaries"]
  | .observers => ["observers"]
  | .closureEvidence => ["closure-evidence"]
  | .configurationCapture => ["configuration-capture"]
  | .versoRecordedPaths => ["verso-recorded-paths"]
  | .copyRelocation => ["copy-relocation"]
  | .copyRelocationLoad project copies => ["copy-relocation-load", project, copies]
  | .copyRelocationGit scratch => ["copy-relocation-git", scratch]
  | .fenceEvidence => ["fence-evidence"]
  | .frozenExits => ["frozen-exits"]
  | .documentationSource => ["documentation-source"]
  | .documentationSourceReadOnly => ["documentation-source", "--source-read-only"]
  | .enumeration => ["enumeration"]
  | .enumerationCopy source target => ["enumeration-copy", source, target]
  | .enumerationFailure => ["enumeration-failure"]
  | .readers => ["readers"]

/-- The selections from `prep-measure` on, which `Command.parse` tries after its own forms. A
second match keeps each `split` of the proof `Command.parse_sound` within Lean's default heartbeat
limit; together the two matches try the forms in the order of `Command`. -/
def Command.parseLater : List String → Option Command
  | ["prep-measure"] => some .prepMeasure
  | ["documentation-dependencies"] => some .documentationDependencies
  | ["input-inventory"] => some .inputInventory
  | ["receipt-boundaries"] => some .receiptBoundaries
  | ["observers"] => some .observers
  | ["closure-evidence"] => some .closureEvidence
  | ["configuration-capture"] => some .configurationCapture
  | ["verso-recorded-paths"] => some .versoRecordedPaths
  | ["copy-relocation"] => some .copyRelocation
  | ["copy-relocation-load", project, copies] => some (.copyRelocationLoad project copies)
  | ["copy-relocation-git", scratch] => some (.copyRelocationGit scratch)
  | ["fence-evidence"] => some .fenceEvidence
  | ["frozen-exits"] => some .frozenExits
  | ["documentation-source"] => some .documentationSource
  | ["documentation-source", "--source-read-only"] => some .documentationSourceReadOnly
  | ["enumeration"] => some .enumeration
  | ["enumeration-copy", source, target] => some (.enumerationCopy source target)
  | ["enumeration-failure"] => some .enumerationFailure
  | ["readers"] => some .readers
  | _ => none

/-- The selection an argument list names, the only parser of the dispatcher: unknown or extra
arguments select nothing. -/
def Command.parse : List String → Option Command
  | ["registry"] => some .registry
  | ["native"] => some .native
  | ["combined"] => some .combined
  | ["unique-constants"] => some .uniqueConstants
  | ["native-launcher"] => some .nativeLauncher
  | ["rule-examples", "--evidence", evidence] => some (.ruleExamples evidence)
  | "rule-examples" :: "--evidence" :: evidence :: "--rules" :: rules =>
      some (.ruleExamplesRules evidence rules)
  | ["rule-examples", "--evidence", evidence, "--shard", spec] =>
      some (.ruleExamplesShard evidence spec)
  | ["producers"] => some .producers
  | ["producers", "--evidence", evidence] => some (.producersExport evidence)
  | ["producers-combined"] => some .producersCombined
  | ["history"] => some .history
  | ["self-audit"] => some .selfAudit
  | ["self-audit", "--shard", spec] => some (.selfAuditShard spec)
  | ["self-audit-module", module, source] => some (.selfAuditModule module source)
  | ["self-audit-json-module", module] => some (.selfAuditJsonModule module)
  | ["environments", "--evidence", evidence] => some (.environments evidence)
  | ["acceptance", group, "--evidence", evidence] =>
      (AcceptanceGroup.parse group).map (.acceptance · evidence)
  | ["acceptance-snapshots", group] => (SnapshotGroup.parse group).map .acceptanceSnapshots
  | args => parseLater args

/-- Every selection's argument list is accepted, as that selection. -/
theorem Command.parse_arguments (command : Command) : parse command.arguments = some command := by
  cases command with
  | acceptance group => cases group; rfl
  | acceptanceSnapshots group => cases group <;> rfl
  | _ => rfl

/-- A group the parser accepts is the one its argument spells. -/
theorem SnapshotGroup.parse_sound {text : String} {group : SnapshotGroup}
    (h : parse text = some group) : text = group.spelling := by
  unfold parse at h; split at h <;> first | (cases h; rfl) | cases h

/-- The later forms' parser accepts an argument list only as the list of the selection it returns.
-/
theorem Command.parseLater_sound {args : List String} {command : Command}
    (h : parseLater args = some command) : args = command.arguments := by
  unfold parseLater at h
  split at h <;> first | (cases h; rfl) | cases h

/-- The parser accepts an argument list only as the list of the selection it returns, so the
dispatcher accepts nothing beyond `Command`'s forms. -/
theorem Command.parse_sound {args : List String} {command : Command}
    (h : parse args = some command) : args = command.arguments := by
  unfold parse at h
  split at h <;> try (cases h; rfl)
  · obtain ⟨group, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [arguments, AcceptanceGroup.parse_sound hg]
  · obtain ⟨group, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [arguments, SnapshotGroup.parse_sound hg]
  · exact parseLater_sound h


/-- The evidence document that a selection writes, by its format: the path that `--evidence`
names, with the group of an acceptance fault campaign as its arguments spell it, or the fixed
report of the paired launcher diagnostic. -/
inductive Evidence where
  /-- The rule-example corpus's evidence. -/
  | ruleExamples (path : String)
  /-- The producer campaign's export. -/
  | producers (path : String)
  /-- The environment census's evidence. -/
  | environments (path : String)
  /-- The evidence of the acceptance fault campaign of `group`. -/
  | acceptance (group path : String)
  /-- The report of the paired launcher diagnostic, `tmp/native-launcher-diagnostic.json` below
  the package root. -/
  | launcherReport
  deriving DecidableEq, Repr

/-- The evidence document that each selection writes, and none for a selection that writes none.
-/
def Command.evidence : Command → Option Evidence
  | .ruleExamples path | .ruleExamplesRules path _ | .ruleExamplesShard path _ =>
      some (.ruleExamples path)
  | .producersExport path => some (.producers path)
  | .environments path => some (.environments path)
  | .acceptance group path => some (.acceptance group.spelling path)
  | .nativeLauncher => some .launcherReport
  | .registry | .native | .combined | .uniqueConstants | .producers
  | .producersCombined | .history | .selfAudit | .selfAuditShard _ | .selfAuditModule _ _
  | .selfAuditJsonModule _ | .acceptanceSnapshots _ | .prepMeasure | .documentationDependencies
  | .inputInventory | .receiptBoundaries | .observers | .closureEvidence | .configurationCapture
  | .versoRecordedPaths | .copyRelocation | .copyRelocationLoad _ _ | .copyRelocationGit _
  | .fenceEvidence | .frozenExits | .documentationSource | .documentationSourceReadOnly
  | .enumeration | .enumerationCopy _ _ | .enumerationFailure | .readers => none

/-- The evidence document that an argument list names from its leading arguments, so that one the
parser refuses for a later argument still has its document recognized: a selection's name, then
`--evidence` and a path, with the group between them for `acceptance`, or `native-launcher`. -/
def Evidence.named : List String → Option Evidence
  | "rule-examples" :: "--evidence" :: path :: _ => some (.ruleExamples path)
  | "producers" :: "--evidence" :: path :: _ => some (.producers path)
  | "environments" :: "--evidence" :: path :: _ => some (.environments path)
  | "acceptance" :: group :: "--evidence" :: path :: _ => some (.acceptance group path)
  | "native-launcher" :: _ => some .launcherReport
  | _ => none

/-- On an argument list that the parser accepts, the evidence named by its leading arguments is
that of the selection it returns, so the two readings of one command line agree on its document.
-/
theorem Evidence.named_of_parse {args : List String} {command : Command}
    (h : Command.parse args = some command) : named args = command.evidence := by
  rw [Command.parse_sound h]
  cases command with
  | acceptance group => cases group; rfl
  | acceptanceSnapshots group => cases group <;> rfl
  | _ => rfl

end Regula.Qualification
