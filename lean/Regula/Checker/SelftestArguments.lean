/-! # The command line of `checkerSelftest`

The closed vocabulary of the selections `lake exe checkerSelftest` accepts (`Selection`) and the
parser the executable runs (`Selection.parse`): one of the focused `--…-only` controls, the
internal transcript worker, or the suite with its options. The inventory of campaigns
(`Regula.Campaigns`) classifies each selection but a request for help, which runs no control, as
one campaign (`Regula.Campaigns.SelftestCampaign.ofSelection`), the unit it classifies by the
workflow job that runs it. The parser checks the suite's options against one another, and a shard
against the shards of its partition (`Partition.shards`), with `Options.validate`. This module
imports nothing, so that inventory can import it beside the other executables' vocabularies. -/
namespace Regula.Checker.SelftestArguments

/-- Disjoint groups whose union is the complete build-bound qualification. -/
inductive Partition where
  /-- In-process fixture verdicts, the Markdown scanner and the fence corpus. -/
  | fixtures
  /-- Structural and manifest controls. -/
  | structural
  /-- Execution-evidence controls: the compiler-path mutations and the correspondence
  controls, each with its positive and fresh restoration. -/
  | execution
  /-- Every fixture through a real `axiomGate --file` invocation, and the source-attribution
  controls. -/
  | cli
  /-- The end-to-end fence corpus and the external-adopter and clean-checkout controls. -/
  | environments
  /-- Ordinary-build enforcement controls (`build-policy`). -/
  | buildPolicy
  /-- `lake lint` dispatch and exit-class controls (`lint-driver`). -/
  | lintDriver
  deriving Repr, BEq, DecidableEq

/-- The name of the partition after `--partition`. -/
def Partition.label : Partition → String
  | .fixtures => "fixtures"
  | .structural => "structural"
  | .execution => "execution"
  | .cli => "cli"
  | .environments => "environments"
  | .buildPolicy => "build-policy"
  | .lintDriver => "lint-driver"

/-- The full run enumerates each supported partition exactly once. -/
def Partition.all : List Partition :=
    [.fixtures, .structural, .execution, .cli, .environments, .buildPolicy, .lintDriver]

theorem Partition.all_complete (partition : Partition) : partition ∈ all := by
  cases partition <;> simp [all]

theorem Partition.all_nodup : all.Nodup := by decide

/-- The partition `--partition` names. -/
def Partition.parse (label : String) : Option Partition :=
  all.find? (·.label == label)

/-- The number of shards each partition's controls are divided into, so that each shard runs under
the deadline of its own invocation: `--shard INDEX/COUNT`, with `COUNT` this number, runs one of
them, and the shards of a partition together run each of its controls once (the self-test's
`shards_cover`). -/
def Partition.shards : Partition → Nat
  | .fixtures => 5
  | .structural => 5
  | .execution => 4
  | .cli => 6
  | .environments => 6
  | .buildPolicy => 3
  | .lintDriver => 5

/-- The shard of a partition of `shards` shards that `--shard index/count` selects: `index`
counted from 1, of `count`, which must be that number of shards. -/
def shardOf? (shards : Nat) : Nat × Nat → Option (Fin shards)
  | (index + 1, count) =>
      if bound : count = shards ∧ index < shards then some ⟨index, bound.2⟩ else none
  | _ => none

/-- `shardOf?` selects shard `index` exactly for `index + 1` of `shards`. -/
theorem shardOf?_eq_some {shards : Nat} {spec : Nat × Nat} {shard : Fin shards} :
    shardOf? shards spec = some shard ↔ spec = (shard.val + 1, shards) := by
  obtain ⟨index, count⟩ := spec
  cases index with
  | zero => simp [shardOf?]
  | succ index =>
    simp only [shardOf?]
    by_cases bound : count = shards ∧ index < shards
    · simp only [bound, and_self, ↓reduceDIte]
      obtain ⟨rfl, -⟩ := bound
      simp [Fin.ext_iff]
    · simp only [bound, ↓reduceDIte]
      simp only [reduceCtorEq, false_iff, Prod.mk.injEq, Nat.add_right_cancel_iff, not_and]
      intro sameIndex sameCount
      exact bound ⟨sameCount, sameIndex ▸ shard.isLt⟩

/-- The parsed options of the suite. -/
structure Options where
  /-- `--jobs N`: the number of parallel workers; must be positive. -/
  jobs : Nat := 4
  /-- `--structural-only`: run only the structural and execution controls after the baseline
  build. -/
  structuralOnly : Bool := false
  /-- `--build-bound`: also run the conditional, build-bound tier. -/
  buildBound : Bool := false
  /-- `--partition NAME`: run only this build-bound group; requires `--build-bound`. -/
  partition : Option Partition := none
  /-- `--shard INDEX/COUNT`: run only that shard of the selected partition, `INDEX` counted from
  1 and `COUNT` the partition's number of shards (`Partition.shards`). -/
  shard : Option (Nat × Nat) := none
  /-- `--help` or `-h`: print the usage and exit. -/
  help : Bool := false

/-- The options an argument list sets, from `options`: each flag once, a partition by its name
and a shard as `INDEX/COUNT` written without leading zeros. -/
def Options.parse : List String → Options → Except String Options
  | [], options => .ok options
  | "--" :: rest, options => parse rest options
  | "--jobs" :: value :: rest, options => match value.toNat? with
    | some jobs => parse rest { options with jobs }
    | none => .error "--jobs requires a natural number"
  | "--structural-only" :: rest, options =>
      if options.structuralOnly then .error "duplicate --structural-only"
      else parse rest { options with structuralOnly := true }
  | "--build-bound" :: rest, options =>
      if options.buildBound then .error "duplicate --build-bound"
      else parse rest { options with buildBound := true }
  | "--partition" :: value :: rest, options =>
      if options.partition.isSome then .error "duplicate --partition"
      else match Partition.parse value with
        | some partition => parse rest { options with partition := some partition }
        | none => .error s!"unknown partition: {value}"
  | "--shard" :: value :: rest, options =>
      if options.shard.isSome then .error "duplicate --shard"
      else match value.splitOn "/" with
        | [index, count] => match index.toNat?, count.toNat? with
          | some index, some count =>
            if value == s!"{index}/{count}" then
              parse rest { options with shard := some (index, count) }
            else .error s!"unknown shard: {value}"
          | _, _ => .error s!"unknown shard: {value}"
        | _ => .error s!"unknown shard: {value}"
  | "--help" :: rest, options | "-h" :: rest, options => parse rest { options with help := true }
  | flag :: _, _ => .error s!"unknown or incomplete argument: {flag}"

/-- The options, refused unless they select a run together: a partition only in the build-bound
tier, a shard only of the selected partition and one it has (`shardOf?`), and `--structural-only`
with neither the build-bound tier nor a partition. -/
def Options.validate (options : Options) : Except String Options := do
  if options.partition.isSome && !options.buildBound then
    throw "--partition requires --build-bound"
  if let some spec := options.shard then
    match options.partition with
    | none => throw s!"--shard {spec.1}/{spec.2} requires --partition"
    | some partition =>
      if (shardOf? partition.shards spec).isNone then
        throw s!"--shard {spec.1}/{spec.2}: --partition {partition.label} has the shards \
          INDEX/{partition.shards}, INDEX from 1"
  if options.structuralOnly && (options.buildBound || options.partition.isSome) then
    throw "--structural-only conflicts with --build-bound and --partition"
  return options

/-- A focused control, selected by its flag alone. -/
inductive Focused where
  /-- `--forced-collector-only`: the force-loaded collector. -/
  | forcedCollector
  /-- `--policy-transport-only`: the policy parser, decoder and admission controls. -/
  | policyTransport
  /-- `--native-adopter-only`: the production linter import. -/
  | nativeAdopter
  /-- `--policy-domain-only`: the policy transport and the public paths. -/
  | policyDomain
  /-- `--combined-snapshot-only`: Markdown discovery of the combined public command. -/
  | combinedSnapshot
  /-- `--fences-only`: the in-process and public fence corpus, and the combined snapshot. -/
  | fences
  /-- `--build-lint-only`: the ordinary-build policy controls. -/
  | buildLint
  /-- `--compiler-paths-only`: the compiler-path mutations. -/
  | compilerPaths
  deriving Repr, DecidableEq

/-- The flag that selects the control. -/
def Focused.flag : Focused → String
  | .forcedCollector => "--forced-collector-only"
  | .policyTransport => "--policy-transport-only"
  | .nativeAdopter => "--native-adopter-only"
  | .policyDomain => "--policy-domain-only"
  | .combinedSnapshot => "--combined-snapshot-only"
  | .fences => "--fences-only"
  | .buildLint => "--build-lint-only"
  | .compilerPaths => "--compiler-paths-only"

/-- Every focused control once. -/
def Focused.all : List Focused :=
  [.forcedCollector, .policyTransport, .nativeAdopter, .policyDomain, .combinedSnapshot, .fences,
    .buildLint, .compilerPaths]

theorem Focused.all_complete (focused : Focused) : focused ∈ all := by
  cases focused <;> simp [all]

/-- A selection of `lake exe checkerSelftest`. -/
inductive Selection where
  /-- A focused control. -/
  | focused (control : Focused)
  /-- `--transcript-worker MODULE SOURCE REJECT OUT`: the internal worker the fixture pipeline
  starts for one transcript. -/
  | transcriptWorker (moduleWire source rejectWarnings out : String)
  /-- The suite, with its options. -/
  | suite (options : Options)

/-- The selection an argument list names: a focused control's flag alone, the transcript worker's
five arguments, or else the suite's options (`Options.parse`), refused unless they select a run
together (`Options.validate`). -/
def Selection.parse (args : List String) : Except String Selection :=
  match Focused.all.find? (fun control => args == [control.flag]) with
  | some control => .ok (.focused control)
  | none => match args with
    | ["--transcript-worker", moduleWire, source, rejectWarnings, out] =>
        .ok (.transcriptWorker moduleWire source rejectWarnings out)
    | _ => .suite <$> (Options.parse args {} >>= Options.validate)

/-- The file that a selection writes for its caller: the transcript worker's `OUT`; a focused
control and the suite report on standard output and write none. -/
def Selection.output : Selection → Option String
  | .transcriptWorker _ _ _ out => some out
  | .focused _ | .suite _ => none

/-- A focused control's flag alone selects it. -/
theorem Selection.parse_focused (focused : Focused) :
    parse [focused.flag] = .ok (.focused focused) := by
  cases focused <;> rfl

end Regula.Checker.SelftestArguments
