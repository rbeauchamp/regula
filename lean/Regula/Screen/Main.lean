import Regula.MaterialClaim
import Regula.RegistryCodec
import Regula.Screen.Calibrate
import Regula.Checker.Lake

/-! # Intent screen executable

`intentScreen`: the opt-in probabilistic intent screen (`docs/guides/intent-screening.md`).

    lake exe intentScreen screen --config FILE (--module M | --library L) ...
      [--intent-sections] [--declaration NAME ...] [--json FILE]
    lake exe intentScreen calibrate --config FILE --split dev|test --report FILE --records FILE

`screen` judges every public `@[regula_material]` declaration of the listed modules and of the
Lake-discovered modules of each listed root library (with `--intent-sections`, also every
public declaration there whose docstring has a nonempty Intent section; or exactly the listed
declarations) and prints screened evidence, findings at the configured severities
and escalation routes. It exits 0 when no error-severity finding is raised, 1 when one is, and
2 when the screen is incomplete (missing key, network or service failure, malformed answer or
unreadable claim, which stop the run, or a refused discharge reference, which leaves only its
clause unresolved while every other clause and claim is screened). It is never part of
offline acceptance. -/

namespace Regula.Screen.Main

open Lean System
open RegulaPolicy.Screening
open Regula.Checker.Screening
open Questions

private def decimalOf (value : Json) : Except String Decimal := do
  let .num n := value | throw "threshold is not a number"
  if n.mantissa < 0 then throw "threshold is negative"
  return ⟨n.mantissa.toNat, n.exponent⟩

private def exactFields (value : Json) (allowed : List String) (what : String) :
    Except String Unit := do
  let .obj fields := value | throw s!"{what} is not an object"
  for (key, _) in fields.toList do
    unless allowed.contains key do throw s!"unknown field `{key}` in {what}"

/-- A judgment's thresholds are keyed by the rule-severity spellings; `information` is
optional and defaults to the warning threshold (an empty information band). -/
private def judgmentPolicy (j : Judgment) (value : Json) : Except String JudgmentPolicy := do
  let (e, w, i) := (Regula.Severity.error.spelling, Regula.Severity.warning.spelling,
    Regula.Severity.information.spelling)
  exactFields value [e, w, i, "min-confidence"] "a judgment policy"
  if (value.getObjVal? "min-confidence").toOption.isSome && !j.reportsConfidence then
    throw s!"min-confidence is not allowed for {j.spelling}: its answers report no confidence \
      (only strength does)"
  let error ← decimalOf (← value.getObjVal? e)
  let warning ← decimalOf (← value.getObjVal? w)
  let information ← match value.getObjVal? i with
    | .ok v => decimalOf v
    | .error _ => pure warning
  let thresholds ← if h : error ≤ warning ∧ warning ≤ information then pure
                                                                        (Thresholds.mk error warning
                                                                            information h.1 h.2)
    else throw "thresholds must satisfy error ≤ warning ≤ information"
  let minConfidence ← match value.getObjVal? "min-confidence" with
    | .ok c => some <$> decimalOf c
    | .error _ => pure none
  return { thresholds := some thresholds, minConfidence }

/-- Parse the configuration file (schema version 1, no unknown fields). -/
def parseConfig (text : String) : Except String Config := do
  let json ← Json.parse text
  exactFields json ["schema-version", "model", "cache", "state", "judgments"] "the configuration"
  unless (← json.getObjValAs? Nat "schema-version") == 1 do throw "unsupported schema-version"
  let model ← json.getObjValAs? String "model"
  let model : PinnedModel ← if h : isPinned model = true then pure ⟨model, h⟩
    else throw s!"model `{model}` is not a pinned version such as jev-1.13.0"
  let cache ← json.getObjValAs? String "cache"
  let some mode := StateMode.parse? (← json.getObjValAs? String "state")
    | throw "state must be full, statement or explanation"
  let judgments ← match json.getObjVal? "judgments" with
    | .ok j => pure j
    | .error _ => pure (Json.mkObj [])
  exactFields judgments (Judgment.all.map (·.spelling)) "judgments"
  let mut table : List (Judgment × JudgmentPolicy) := []
  for j in Judgment.all do
    if let .ok p := judgments.getObjVal? j.spelling then
      table := (j, ← judgmentPolicy j p) :: table
  let final := table
  return { model, cache, mode, policy := fun j => (final.lookup j).getD {} }

private def severityText : Option ScreenSeverity → String
  | none => "none" | some s => s.toSeverity.spelling

private def routeText : Route → String
  | .screened => "screened" | .escalate => "escalate"

/-- The machine record of one judged answer for `claim`: its evidence class, judgment, subject,
model, question, support and confidence, request digest, and the severity and route `policy`
gives it. -/
def judgedJson (policy : Policy) (claim : Name) (j : Judged) : Json :=
  Json.mkObj [("claim", .str claim.toString), ("class", .str j.evidenceClass.spelling),
    ("judgment", .str j.judgment.spelling),
    ("subject", .str j.subject), ("model", .str j.model.val), ("question", .str j.question),
    ("probability", .str j.support.render),
    ("confidence", match j.confidence with | some c => .str c.render | none => .null),
    ("inputsDigest", .str j.inputsDigest), ("severity", .str (severityText (j.severity policy))),
    ("route", .str (routeText (j.route policy)))]

private def locationText : Regula.Location → String
  | .source s =>
      s!"{s.val.snapshot.uri}:{s.selectionLsp.start.line + 1}:{s.selectionLsp.start.character + 1}"
  | .module n => s!"module {n}"
  | .project p => s!"project/configuration {p}"

/-- One finding in the linter diagnostic shape (`Regula.RegistryCodec.diagnosticJson`), with
its judgment's `findingId` in place of a registry rule and its evidence class. -/
structure ScreenFinding where
  /-- The screened claim's declaration. -/
  claim : Name
  /-- Where the finding is reported: the claim's source range, or its module. -/
  location : Regula.Location
  /-- The judged answer that raised the finding. -/
  answer : Judged
  /-- The severity the policy's thresholds give the answer. -/
  severity : ScreenSeverity

/-- The finding's detail: the judgment, the quoted subject and the answer's evidence. -/
def ScreenFinding.detail (f : ScreenFinding) : String :=
  s!"{f.answer.judgment.spelling} of \"{f.answer.subject}\": {f.answer.evidence}"

/-- The one-line terminal text: finding ID, evidence class, severity, location, claim and
detail. -/
def ScreenFinding.text (f : ScreenFinding) : String :=
  s!"{f.answer.judgment.findingId} \
    [{f.answer.evidenceClass.spelling}; {f.severity.toSeverity.spelling}; " ++
    s!"{locationText f.location}]: {f.claim}: {f.detail}"

/-- The finding as a diagnostic JSON object, with its evidence class and severity. -/
def ScreenFinding.json (f : ScreenFinding) : Json :=
  Json.mkObj [("id", .str f.answer.judgment.findingId),
    ("arguments", Json.mkObj
        [("declaration", Regula.RegistryCodec.nameJson f.claim), ("detail", .str f.detail)]),
    ("location", Regula.RegistryCodec.locationJson f.location), ("related", Json.arr #[]),
    ("class", .str f.answer.evidenceClass.spelling),
    ("severity", .str f.severity.toSeverity.spelling),
    ("text", .str f.text)]

private unsafe def loadEnvironment (modules : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules (modules.map fun module => { module, importAll := true }) {} 0 (loadExts := true)
    (level := .private)

/-- The parsed command line of `intentScreen`. -/
structure Args where
  /-- The subcommand: `screen` or `calibrate`; empty until one is given. -/
  command : String := ""
  /-- The `--config` file. -/
  config : Option String := none
  /-- Modules given with `--module`, in order. -/
  modules : Array Name := #[]
  /-- Root Lean libraries given with `--library`, in order. -/
  libraries : Array String := #[]
  /-- `--intent-sections`: also screen unregistered declarations whose docstrings RG5002 and
  RG5003 would accept. -/
  intentSections : Bool := false
  /-- Declarations given with `--declaration`; when any is given, only they are screened. -/
  declarations : Array Name := #[]
  /-- The `--json` report path. -/
  json : Option String := none
  /-- The corpus split `--split` names for `calibrate`: `dev` or `test`. -/
  split : Option String := none
  /-- The Markdown report path `--report` names for `calibrate`. -/
  report : Option String := none
  /-- The evidence rows path `--records` names for `calibrate`. -/
  records : Option String := none

/-- Parse the arguments into `acc`, a later flag replacing an earlier single-valued one; the
first bare word is the command, and any other argument is an error. -/
def parseArgs (args : List String) (acc : Args := {}) : Except String Args :=
  match args with
  | [] => .ok acc
  | "--config" :: v :: rest => parseArgs rest { acc with config := some v }
  | "--module" :: v :: rest => parseArgs rest { acc with modules := acc.modules.push v.toName }
  | "--library" :: v :: rest => parseArgs rest { acc with libraries := acc.libraries.push v }
  | "--intent-sections" :: rest => parseArgs rest { acc with intentSections := true }
  | "--declaration" :: v :: rest =>
      parseArgs rest { acc with declarations := acc.declarations.push v.toName }
  | "--json" :: v :: rest => parseArgs rest { acc with json := some v }
  | "--split" :: v :: rest => parseArgs rest { acc with split := some v }
  | "--report" :: v :: rest => parseArgs rest { acc with report := some v }
  | "--records" :: v :: rest => parseArgs rest { acc with records := some v }
  | cmd :: rest => if acc.command.isEmpty && !cmd.startsWith "-" then parseArgs rest
                                                                       { acc with command := cmd }
    else .error s!"unexpected argument {cmd}"

/-- The two command forms, printed when the command line is not accepted. -/
def usage : String :=
  "usage: intentScreen screen --config FILE (--module M | --library L) ... [--intent-sections] \
    [--declaration NAME ...] [--json FILE]\n" ++
  "       intentScreen calibrate --config FILE --split dev|test --report FILE --records FILE"

/-- The run's service usage line: requests sent, cache answers and billed input tokens, with the
list price when the model is `jev-1.13.0`. -/
def costNote (model : PinnedModel) (u : Usage) : String :=
  let price := if model.val == "jev-1.13.0" then
      "; the jev-1.13.0 list price was $0.042 per million input tokens on 2026-09-24" else ""
  s!"service usage: {u.requests} request(s) sent, {u.cached} answered from cache, " ++
    s!"{u.tokensText} input tokens billed (output tokens are free{price})"

/-- The machine record of one claim: each clause with its evidence classes (a discharge's
checked implication beside, not inside, its screened correspondence) and the open review
obligations. `complete` is false exactly when a discharge reference was refused; `status` is
the proved `ClaimScreen.status`. -/
def claimJson (policy : Policy) (s : ClaimScreen) : Json :=
  Json.mkObj [("claim", .str s.claim.toString),
    ("complete", .bool s.complete), ("status", .str (s.status policy).spelling),
    ("clauses", Json.arr (s.clauses.map fun (text, e) =>
      let discharge := match e with
        | .discharged proof formal axioms _ => Json.mkObj [("theorem", .str proof.toString),
            ("formalClause", .str formal),
            ("axioms", Json.arr (axioms.map (.str ·.toString)).toArray)]
        | .judged _ => .null
        | .refused proof reason =>
            Json.mkObj [("theorem", .str proof.toString), ("refused", .str reason)]
      Json.mkObj
          [("clause", .str text), ("classes", Json.arr (e.classes.map (.str ·.spelling)).toArray),
        ("discharge", discharge)]).toArray),
    ("openReview", Json.mkObj [("class", .str EvidenceClass.openReview.spelling),
      ("obligations", Json.arr (unresolved.map (.str ·.spelling)).toArray)])]

/-- The `--json` report. `reason` is set only for a run that did not finish. -/
def reportJson (complete : Bool) (exitStatus : UInt32) (reason : Option String)
    (incomplete : Array Json)
    (findings : Array ScreenFinding) (claims records : Array Json) : Json :=
  Json.mkObj [("schemaVersion", (1 : Nat)), ("class", .str EvidenceClass.screened.spelling),
    ("note", "Screened results are model judgments: never checked evidence and never a completed \
      R-INTENT review."),
    ("complete", .bool complete), ("exitStatus", exitStatus.toNat),
    ("reason", match reason with | some r => .str r | none => .null),
    ("incomplete", Json.arr incomplete),
    ("findings", Json.arr (findings.map (·.json))), ("claims", Json.arr claims),
    ("results", Json.arr records)]

/-- Record an unfinished run at the `--json` path, replacing any earlier report. -/
def writeUnfinished (path : System.FilePath) (reason : String) : IO Unit :=
  IO.FS.writeFile path (reportJson false 2 (some reason) #[] #[] #[] #[]).pretty

/-- The `screen` command. It loads the listed modules (and every module of each listed library),
selects the `--declaration` names or else every public `@[regula_material]` declaration of
those modules (plus, with `--intent-sections`, each one RG5002/RG5003 would accept), screens
each claim, prints its lines, findings and service usage, and writes the `--json` report when
asked. It returns 2 when a discharge reference was refused, 1 when a finding has error severity,
and 0 otherwise. -/
unsafe def screen (args : Args) (cfg : Config) : IO UInt32 := do
  let mut modules := args.modules
  unless args.libraries.isEmpty do
    let inventory ← Regula.Checker.Lake.surfaceInventory (← Regula.Checker.repoRoot)
    for library in args.libraries do
      let some info := inventory.libraries.find? (·.library == library)
        | throw <| IO.userError s!"--library {library} is not a root Lean library of this workspace"
      modules := modules ++ info.modules.filter (!modules.contains ·)
  if modules.isEmpty then throw <| IO.userError "screen requires at least one --module or --library"
  let env ← loadEnvironment modules
  let selected ← if !args.declarations.isEmpty then pure args.declarations else do
    let mut names := #[]
    for (name, _) in env.constants.toList do
      if isPrivateName name then continue
      let some idx := env.getModuleIdxFor? name | continue
      unless modules.contains env.header.modules[idx.toNat]!.module do continue
      let registered := Regula.materialClaimAttribute.hasTag env name
      -- `--intent-sections` adds exactly the declarations RG5003 would accept if registered.
      let withIntent ← if args.intentSections && !registered then do
          let doc ← findDocString? env name
          pure (RegulaPolicy.materialDocumentationFailure doc).isNone
        else pure false
      if registered || withIntent then names := names.push name
    pure (names.qsort (·.toString < ·.toString))
  if selected.isEmpty then
    IO.println "intent screen: no selected declarations in the listed modules"
    if let some path := args.json then IO.FS.writeFile path
                                        (reportJson true 0 none #[] #[] #[] #[]).pretty
    return 0
  let mut usage : Usage := {}
  let mut records := #[]
  let mut claims := #[]
  let mut findings : Array ScreenFinding := #[]
  let mut incomplete : Array Json := #[]
  for name in selected do
    let input ← runMeta env (readClaim name)
    let location ← runMeta env (claimLocation name)
    let (s, u) ← (screenClaim cfg input).run usage
    usage := u
    for line in s.lines cfg.policy do IO.println line
    records := records ++ (s.answers.map (judgedJson cfg.policy name)).toArray
    claims := claims.push (claimJson cfg.policy s)
    for (text, e) in s.clauses do
      if let .refused proof reason := e then
        incomplete := incomplete.push
            (Json.mkObj [("claim", .str name.toString), ("clause", .str text),
          ("theorem", .str proof.toString), ("refused", .str reason)])
    findings := findings ++ ((s.findings cfg.policy).map fun (answer, severity) =>
      { claim := name, location, answer, severity : ScreenFinding }).toArray
  for f in findings do IO.println f.text
  let complete := incomplete.isEmpty
  let exitStatus : UInt32 := if !complete then 2 else if findings.any
                                                       (·.severity == .error) then 1 else 0
  unless complete do
    IO.println s!"intent screen incomplete: {incomplete.size} discharge reference(s) refused; \
      those clauses are neither checked nor judged"
  IO.println (costNote cfg.model usage)
  if let some path := args.json then
    IO.FS.writeFile path
        (reportJson complete exitStatus none incomplete findings claims records).pretty
  return exitStatus

/-- The values of every `FLAG VALUE` pair in the raw arguments, found without a full parse. -/
def flagValues (flag : String) : List String → List String
  | f :: v :: rest => if f == flag then v :: flagValues flag rest else flagValues flag (v :: rest)
  | _ => []

/-- A path made absolute and resolved through symbolic links as far as it exists. -/
def resolvedPath (p : System.FilePath) : IO System.FilePath := do
  let cwd ← IO.currentDir
  let abs := if p.isAbsolute then p else cwd / p
  if ← abs.pathExists then return ← IO.FS.realPath abs
  match abs.parent, abs.fileName with
  | some dir, some name => if ← dir.pathExists then return (← IO.FS.realPath dir) / name else
                                                     return abs.normalize
  | _, _ => return abs.normalize

/-- Admit `path` as the `--json` report target. It is refused when it names one of the run's
other files (`--config`, `--report`, `--records`), or an existing file that is not an earlier
intentScreen report (`schemaVersion` 1 and `class` `screened`). Invariant: no stale passing
report survives a failed run, because every such report is an intentScreen report and is
replaced before any work; no other file is ever overwritten by an argument mistake. -/
def admitReportPath (path : System.FilePath) (others : List String) : IO Unit := do
  let target ← resolvedPath path
  for other in others do
    if (← resolvedPath other) == target then
      throw <|
          IO.userError
              s!"--json {path} names the same file as another argument ({other}); nothing was \
                written"
  if ← path.pathExists then
    let earlier := (Json.parse (← IO.FS.readFile path)).toOption.filter fun j =>
      (j.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
        (j.getObjValAs? String "class").toOption == some EvidenceClass.screened.spelling
    if earlier.isNone then
      throw <|
          IO.userError
              s!"--json {path} exists and is not an intentScreen report; it was left untouched"

/-- The `intentScreen` entry point. It admits and pre-writes an unfinished `--json` report, reads
the configuration and runs `screen` or `calibrate`. Any error prints
`intent screen incomplete: …`, records the reason in the `--json` report when there is one,
and returns 2. -/
unsafe def main (argv : List String) : IO UInt32 := do
  let target? ← try
      match (flagValues "--json" argv).getLast? with
      | some path =>
        admitReportPath path (["--config", "--report", "--records"].flatMap (flagValues · argv))
        writeUnfinished path "the run did not finish"
        pure (some (path : System.FilePath))
      | none => pure none
    catch e =>
      IO.eprintln s!"intent screen incomplete: {e}"
      return 2
  try
    let args ← IO.ofExcept (parseArgs argv)
    if args.json.isSome && args.command != "screen" then
      throw <| IO.userError s!"--json is accepted only by the screen command\n{usage}"
    let some configPath := args.config | throw <| IO.userError usage
    let cfg ← IO.ofExcept (parseConfig (← IO.FS.readFile configPath))
    match args.command with
    | "screen" => screen args cfg
    | "calibrate" =>
      let (some split, some report, some records) := (args.split, args.report, args.records)
        | throw <| IO.userError usage
      let split ← match split with
        | "dev" => pure Corpus.Split.dev | "test" => pure Corpus.Split.test
        | _ => throw <| IO.userError usage
      let env ← loadEnvironment #[`Regula.Screen.Corpus]
      Calibrate.run cfg.cache cfg.model split env report records
      return 0
    | _ => throw <| IO.userError usage
  catch e =>
    IO.eprintln s!"intent screen incomplete: {e}"
    if let some path := target? then
      try writeUnfinished path s!"{e}"
      catch w => IO.eprintln s!"intent screen: could not record the unfinished run in {path}: {w}"
    return 2

end Regula.Screen.Main

/-- The `intentScreen` executable's root: runs `Regula.Screen.Main.main`. -/
unsafe def main (argv : List String) : IO UInt32 := Regula.Screen.Main.main argv
