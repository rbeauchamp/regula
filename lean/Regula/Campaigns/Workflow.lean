import Regula.Campaigns

/-! # The workflow jobs of the inventory, read from the workflow files

`Job.invocations` states the `verify.sh` invocations of each workflow job of the inventory of
campaigns (`Regula.Campaigns`). `Workflow.invocations` reads them from the text of the job's
workflow file: the job's steps whose command is `./scripts/verify.sh`, in order, each once for
each value of its matrix in place of `${{ matrix.KEY }}`. The registry checks
(`Regula.RegistryChecks`) require the two to be equal for every job, so a step or a matrix value
removed from a workflow fails acceptance. A form the reader does not know is refused, not skipped.

The diagnostics workflow's `campaign` matrix is the list its `applies` job writes,
`Regula.DiagnosticsGate.campaigns`. Its text names that output, so the reader takes the list from
its argument `applies`, which the registry checks give as the invocations
`Regula.Campaigns.Diagnostics.campaigns_eq` equates to that list.

Not read: that GitHub runs a job's steps when its triggers and `if:` say, and the YAML structure
beyond the line forms below. -/
namespace Regula.Campaigns

/-- The workflow file and the id of each job. -/
def Job.location : Job → String × String
  | .ciVerify => (".github/workflows/ci.yml", "verify")
  | .ciMathlib => (".github/workflows/ci.yml", "mathlib")
  | .ciRuleExamples => (".github/workflows/ci.yml", "rule-examples")
  | .ciSite => (".github/workflows/ci.yml", "site")
  | .diagnosticsCampaign => (".github/workflows/diagnostics.yml", "campaign")
  | .diagnosticsNightly => (".github/workflows/diagnostics.yml", "rule-examples-nightly")
  | .dogfoodSelf => (".github/workflows/dogfood.yml", "self")
  | .dogfoodDefaultPath => (".github/workflows/dogfood.yml", "default-path")

namespace Workflow

/-- The line without its leading and trailing spaces. -/
private def trimmed (line : String) : String := line.trimAscii.toString

/-- The text without the quotes of a quoted YAML scalar. -/
private def unquote (text : String) : String :=
  let text := trimmed text
  if text.length ≥ 2 && ((text.startsWith "'" && text.endsWith "'") ||
      (text.startsWith "\"" && text.endsWith "\"")) then
    ((text.drop 1).dropEnd 1).toString
  else text

/-- Whether a line starts a job: two spaces of indentation, then an id and a colon alone. -/
private def jobHeader (line : String) : Bool :=
  line.startsWith "  " && !line.startsWith "   " && !line.startsWith "  #" && line.endsWith ":"

/-- The lines of the job `id`: those after its line `  ID:` below `jobs:`, up to the next job.
`none` when the file has no such job. -/
def jobLines (text id : String) : Option (List String) :=
  match ((text.splitOn "\n").dropWhile (· != "jobs:")).dropWhile (· != s!"  {id}:") with
  | [] => none
  | _ :: rest => some (rest.takeWhile (!jobHeader ·))

/-- Where the values of a matrix key come from. -/
inductive Values where
  /-- Listed in the workflow. -/
  | listed (values : List String)
  /-- The list the diagnostics workflow's `applies` job writes. -/
  | applies

/-- The values of the matrix key `key` in a job's lines, in one of four forms: a block list
below `KEY:`, the `KEY:` entries of an `include` list, a flow list `KEY: [...]`, or the output
`campaigns` of the job `applies`. `none` when the job gives none of them. -/
def matrixValues (lines : List String) (key : String) : Option Values :=
  let header := s!"{key}:"
  let entry := s!"- {key}: "
  let block := match (lines.dropWhile (trimmed · != header)) with
    | [] => []
    | _ :: rest => (rest.takeWhile (trimmed · |>.startsWith "- ")).map
        fun line => unquote ((trimmed line).drop 2).toString
  let entries := lines.filterMap fun line =>
    ((trimmed line).dropPrefix? entry).map (unquote ·.toString)
  let flow := lines.findSome? fun line =>
    ((trimmed line).dropPrefix? s!"{key}: [").bind fun rest =>
      (rest.toString.dropSuffix? "]").map fun inner =>
        (inner.toString.splitOn ",").map unquote
  if lines.any (trimmed · == s!"{key}: $\{\{ fromJSON(needs.applies.outputs.campaigns) }}") then
    some .applies
  else if !block.isEmpty then some (.listed block)
  else if !entries.isEmpty then some (.listed entries)
  else flow.map .listed

/-- The command of a `verify.sh` step: the text after `run: ./scripts/verify.sh`, which may
open a list item, or `none` for a line that is no such step. -/
def stepArguments (line : String) : Option String :=
  let line := trimmed line
  let line := ((line.dropPrefix? "- ").map (·.toString)).getD line
  if line == "run: ./scripts/verify.sh" then some ""
  else ((line.dropPrefix? "run: ./scripts/verify.sh ").map (·.toString))

/-- The words of a command. -/
private def words (command : String) : List String :=
  (command.splitOn " ").filter (!·.isEmpty)

/-- The invocations of one step's command: the command alone, or once for each value of the one
matrix key it names. Refused when it names something else of the workflow's context or a key
without values. -/
def expand (lines : List String) (applies : List String) (command : String) :
    Except String (List (List String)) :=
  match command.splitOn "${{ matrix." with
  | [plain] =>
      if plain.contains '$' then .error s!"unread expression in `{command}`"
      else .ok [words plain]
  | [before, rest] =>
      match rest.splitOn " }}" with
      | [key, after] =>
          if before.contains '$' || after.contains '$' then
            .error s!"unread expression in `{command}`"
          else match matrixValues lines key with
            | some (.listed values) => .ok (values.map fun value => words (before ++ value ++ after))
            | some .applies => .ok (applies.map fun value => words (before ++ value ++ after))
            | none => .error s!"no values of matrix key {key} for `{command}`"
      | _ => .error s!"unread expression in `{command}`"
  | _ => .error s!"more than one matrix key in `{command}`"

/-- The `verify.sh` invocations of the job `id` of a workflow's text, in the order of its steps. -/
def invocations (text id : String) (applies : List String) :
    Except String (List (List String)) := do
  let some lines := jobLines text id | throw s!"no job {id}"
  let commands := lines.filterMap stepArguments
  if commands.isEmpty then throw s!"job {id} runs no ./scripts/verify.sh step"
  return (← commands.mapM (expand lines applies)).flatten

/-- A job with a block-list matrix. -/
private def sample : String := "\n".intercalate [
  "on:", "jobs:", "  self:", "    strategy:", "      matrix:", "        campaign:",
  "          - diagnostics self-lint", "          - diagnostics self-audit 1/2",
  "    steps:", "      - name: Check", "        run: ./scripts/verify.sh ${{ matrix.campaign }}",
  "  other:", "    steps:", "      - run: ./scripts/verify.sh docs"]

#guard (invocations sample "self" []).toOption ==
  some [["diagnostics", "self-lint"], ["diagnostics", "self-audit", "1/2"]]
#guard (invocations sample "other" []).toOption == some [["docs"]]
-- A value removed from the matrix is missing from the invocations.
#guard (invocations (sample.replace "          - diagnostics self-audit 1/2\n" "") "self"
    []).toOption == some [["diagnostics", "self-lint"]]
-- A step whose expression the reader does not know is refused.
#guard (invocations (sample.replace "matrix.campaign" "inputs.campaign") "self" []).toOption ==
  none
#guard (invocations
    ("jobs:\n  r:\n    steps:\n      - run: ./scripts/verify.sh diagnostics r ${{ matrix.shard }}\n" ++
      "    strategy:\n      matrix:\n        shard: ['1/2', '2/2']") "r" []).toOption ==
  some [["diagnostics", "r", "1/2"], ["diagnostics", "r", "2/2"]]

end Workflow

/-- Each job's invocations as its workflow file gives them, refused unless they are
`Job.invocations`. `read` reads a workflow file, and `applies` is the list the diagnostics
workflow's `applies` job writes. -/
def Job.workflowRefusal (read : String → String) (applies : List String) (job : Job) :
    Option String :=
  let (file, id) := job.location
  match Workflow.invocations (read file) id applies with
  | .error reason => some s!"{file} job {id}: {reason}"
  | .ok found =>
      if found == job.invocations then none
      else some s!"{file} job {id} runs {found}, and the inventory of campaigns states \
        {job.invocations}"

end Regula.Campaigns
