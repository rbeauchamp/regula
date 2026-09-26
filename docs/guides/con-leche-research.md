# Optional con-leche export research: decision record

This is the maintained research record for [#8](https://github.com/rbeauchamp/regula/issues/8),
the optional con-leche export study. It is supplementary to the linter and website and does not
gate core delivery ([#10](https://github.com/rbeauchamp/regula/issues/10)). Recorded on
2026-09-25 against revision `56c53c2bb3ab5c2a7ddbbcb45759e65502b24c0d` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

## Decision: no-go

**No-go.** Regula will not add an optional con-leche adapter, and
[#9](https://github.com/rbeauchamp/regula/issues/9) is closed as not planned. This is a research
result. Regula has no con-leche checking integration, successful or otherwise.

The reasons, in the order the study took them:

1. **Value.** The only claim con-leche could add is about an export artifact, not the source. An
   independently implemented checker, proved consistent, would have accepted a lean4export stream
   of the claimed declarations. That result is conditional on set-theory assumptions. No Regula
   rule, diagnostic, editor message or rule page would use it. An adopter who wants this kernel
   diversity can already run con-leche on a lean4export stream without Regula. Regula would add
   only the binding of export roots to its owned inventory. That value does not justify the cost
   in item 3.
2. **Correspondence.** A statement-preserving claim cannot be justified.
   - The exporter-to-source relation is trusted.
   - Con-leche's preservation theorem does not cover the 192 owned inductive types (191 blocks)
     or their 630 constructors and recursors.
   - The exporter skips the 32 generated `_unsafe_rec` helpers by default.
   - Two claimed roots declare the same name `main`, so no single export can hold the whole
     surface.

   What would remain is an artifact-only claim with trusted correspondence.
3. **Cost.** Costs that would recur:
   - con-leche runs a second toolchain (`v4.33.0`), has no releases and has an unusually
     fast-moving default branch (`master`);
   - it has a `v4.34.0-rc2` pin variant but no `v4.34.0` one;
   - any adapter would have to be written in Lean, with a process protocol, qualification
     controls, proofs of its pure parts and a manual CI job;
   - every future Regula toolchain bump would wait on upstream pin support.

   Downgrading Regula to Lean 4.33 is costed [below](#costed-option-downgrading-regula-to-lean-433)
   and rejected.

The order was value first. On 2026-09-25 the operator directed that the claim con-leche could add
be written down before any compatibility or export work, and that the study stop at a no-go if
the claim did not justify the cost. It did not. So **no export was produced and con-leche was
never run on a Regula artifact**: the compatibility question is unperformed, not passed or failed.
Nothing below is evidence that Regula's export is compatible or incompatible.

## What con-leche could add

The strongest claim con-leche could honestly support for Regula has this form.

- **Premise.** Given an explicit root set R, lean4export `v4.34.0` produced the NDJSON stream E
  from the built Regula environment, and `con-leche --verified` at a fixed pin exited `0` on E
  with the matching verdict line.
- **Model.** By con-leche's `model_exists`, the checker's *output* environment has a set model
  in any `V` with `[SetTheory V]`. The metatheory axioms are `propext`, `Classical.choice` and
  `Quot.sound`. `[SetTheory V]` is ZF without infinity or choice, plus an ω-chain of
  Grothendieck universes. So every theorem type that environment accepts denotes a nonempty set.
- **Preservation.** By `checkDecls_consts`, also stated under `[SetTheory V]`, each definition,
  theorem, opaque or axiom record (other than `sorryAx` and `Quot.sound`) of the checker input
  appears in that environment with the same name and level parameters. Its type is the checker's
  annotation of the record's type, up to ζ-reduction.

Who it is for: an adopter who distrusts Lean's C++ kernel and wants a second, independently
implemented checker with a machine-checked consistency theorem.

What it cannot do:

- It says nothing about the Lean source. Source → elaborated environment → `.olean` → exporter
  record is the trusted boundary. A stream digest identifies bytes only.
- It is not Lean acceptance. The model theorem is neither an equivalence with official kernel
  acceptance nor a statement of all delta/iota equations. A decline is not evidence that a
  theorem is false.
- It is not Regula policy. Con-leche accepts a stream that declares `sorryAx` without using it,
  while Regula rejects project logical axioms whether used or not. Con-leche has no notion of
  ownership, foundation profile, generated-role authentication or documentation.
- It is not execution evidence. It is no claim about compiled code, `implemented_by`, `extern`
  or native evaluation, and it covers con-leche's own compiled binary only under trust in the
  Lean compiler and runtime, including the `Nat` runtime behind its accelerated operations.
- It is not §8.9. `freshChecker` rechecks the serialized `.olean` graph with the official
  kernel. Any con-leche result would be a differently named, separate artifact claim.

## Pins, licenses and credit

| Component | Pin | License | Notes |
| --- | --- | --- | --- |
| con-leche | [`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`](https://github.com/leanprover/con-leche/tree/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526) (`master`, 2026-09-21) | Apache 2.0 | Toolchain `leanprover/lean4:v4.33.0`. No GitHub releases. The package has no Lake dependencies. |
| lean4export | tag `v4.34.0` = [`076e8e57707e813375e8f9da8bf989799ace9680`](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680) | Apache 2.0 | Toolchain `v4.34.0`. The `v4.34.0` Lean distribution has no bundled `leanexport` binary (checked in the local toolchain's `bin/`). |
| Regula source | Lean `v4.34.0` (`293d5d0c`) | MIT | Not downgraded. |

The earlier research pin `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0` (Lean 4.33.0) is superseded
for this record by `ae0c0c4`. Links below use the new pin.

Credit: con-leche is by its authors and contributors. Its README says it was "implemented
and proven to be consistent by Claude (Fable and Opus), under heavy supervision by Joachim
Breitner at the Lean FRO" ([README](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/README.md)).
lean4export is by Lean FRO and contributors. This record quotes their theorem names, command-line
text and design, and cites them. No con-leche or lean4export code or proof is copied into Regula,
and Regula does not depend on either. No upstream endorsement is implied.

## Checker protocol at the pin

Source: [`Main.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/Main.lean)
and the binary's own `--help` output. The binary was built locally. It was run only for `--help`
and for one missing input file; no stream was checked.

- **Invocation:** `con-leche [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]] FILE.ndjson`.
  `--verified` is the default and the only mode the theorems cover. A `--trusted` accept is
  outside the proved result.
- **Exit codes:** `0` accepted; `1` rejected, out of memory, or an uncaught I/O exception; `2`
  declined (an unsupported feature, or a census-only diagnostic run); `3` usage error, malformed
  input or internal failure. Upstream documents `134`, a generic abort code, for a run whose
  runtime could not create a worker thread.
  Exit `1` is a reject only when stderr carries the driver's `con-leche: <error> [at ...] (<mode>)`
  verdict line. The Lean runtime also exits `1` for out of memory, printing
  `INTERNAL PANIC: out of memory` on stderr, and for any I/O exception that escapes `main`,
  printing `uncaught exception:` on stderr. A missing input file at the pin exits `1` with
  `uncaught exception: no such file or directory`, so an unreadable input is a process error,
  not a reject.
- **Help:** `--help` anywhere prints usage on stdout and exits `0` without reading input. Exit
  `0` alone is therefore not acceptance.
- **Evidence of an intended accept:** all of the following, together.
  - Exit `0`.
  - Stdout is exactly `con-leche: accepted N declarations (--verified)`, where `N` is the
    stream's declaration-record count: one per def, theorem, opaque, axiom, inductive or quot
    record, not counting name, level or expression lines. Generated model records and built-in
    prelude records are not counted.
  - The invocation had no `--trusted` flag and none of the four debug variables below set.
  - A single file argument whose digest is bound to the request.

  Every verdict line names its mode.
- **Environment switches:** upstream names four debug switches. With `CON_LECHE_INMODEL=0`, it
  says the verdict is not the checker's verdict on the stream. `CON_LECHE_INMODEL_CENSUS=1` stops
  after the parse and always exits `2`. `CON_LECHE_INMODEL_DUMP=OUT` writes a copy of the input
  with the generated model records spliced in. `CON_LECHE_PROJREC_TRACE`, named in `DESIGN.md`
  rather than `--help`, writes a trace to stderr. Regula's evidence rule, not
  upstream's, is to refuse any run with one of them set.
- **Workers:** by default the check phase uses one worker per hardware thread. Each worker
  reserves about 1 GiB of address space, so upstream says a run under an address-space limit
  (`ulimit -v`) must lower the count. A reproducible run should pass an explicit `--jobs`.
- **Nat pins:** a pin-certified `Nat` operation is accepted only against a pin variant. The
  embedded variants are `v4.33.0` (which, per the pin README, covers v4.29.0 to v4.33.1),
  `v4.34.0-rc2` and `nightly-2026-09-10`. When no variant matches, the stream declines (exit
  `2`). Whether Lean `v4.34.0`'s definitions match the `v4.34.0-rc2` variant was not tested.
- **Exporter hazards**, from lean4export
  [`Export.lean`](https://github.com/leanprover/lean4export/blob/076e8e57707e813375e8f9da8bf989799ace9680/Export.lean)
  and [`Main.lean`](https://github.com/leanprover/lean4export/blob/076e8e57707e813375e8f9da8bf989799ace9680/Main.lean)
  at the pin:
  - Roots are passed after `--` and decoded with `Syntax.decodeNameLit … |>.get!`.
  - A missing constant triggers `panic!`, but the process still exits `0`. The upstream matrix
    script notes the same, and reads missing names off stderr.
  - Unsafe and `partial` constants are skipped unless `--export-unsafe` is given.
  - `mdata` is dropped unless `--export-mdata` is given.
  - `--ignore-missing` skips missing constants without a panic, which would defeat the stderr
    check. A revival must forbid it.

## Boundary account

| Step | What holds | Status |
| --- | --- | --- |
| Lean source → elaborated environment | Regula's own gate: fresh elaboration and `Admission.validate` replay with the official kernel | Regula evidence, separate claim |
| Environment/`.olean` → lean4export records | None. The exporter walks the imported environment. | Trusted |
| Stream bytes → parsed declarations | The fast parser is proved equal (`@[csimp]`) to a naive reference parser, but the naive parser's faithfulness is not proved. The main corollary `no_False_declaration` is stated on raw bytes under `[SetTheory V]`, but only for streams satisfying `jsonWithTheoremFalse`. | Parse faithfulness trusted; fast = naive proved; corollary conditional and narrow |
| Parse-time rewrites: projection rewrites, in-process `_model` generation for mutual/nested blocks | Generated records are checked like any others and cannot cause a wrong accept, but no theorem relates them to the source block. | Trusted for correspondence |
| Parsed declarations → `preparePrelude` | `preparePrelude_perm`: the output is a permutation of the input plus added prelude records | Proved upstream |
| Checker input → output environment | `checkDecls_consts`: name, level parameters and annotated type are kept for definition, theorem, opaque and axiom records other than `sorryAx` and `Quot.sound`. Not for inductive blocks, basis blocks or quotient records, and not for bodies. | Proved upstream, conditional on `[SetTheory V]`, partial |
| Output environment → model | `model_exists` under `[SetTheory V]` | Proved upstream, conditional |
| Compiled con-leche binary, Lean runtime, `Nat` bignums, IO driver | None | Trusted |

Upstream sources:
[`MainTheorem.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean),
[`StreamConsts.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/Verify/Cached/StreamConsts.lean),
[`Prepare.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/Verify/Frontend/Prepare.lean),
[`Denotes.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/Denotes.lean),
[`SetTheory/Core.lean`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/SetTheory/Core.lean),
[`pins/README.md`](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/pins/README.md).
The capstone proofs were not rebuilt locally; only the `con-leche` executable target was built.
The theorem statements are cited from the source, and the proofs rely on upstream CI.

## Coverage and correspondence ledger

The expected inventory comes from the project's own gate, `lake exe axiomGate -- --json-out`, at
`56c53c2`: `status` `completed`, toolchain `4.34.0`. Its `scope.surfaces[].report.declarations`
list the owned declarations of the six claimed surfaces: the policy, verification, qualification
and core libraries, `Audit` and `AuditApp`, which includes the claimed executable
root `Main`. A temporary probe cross-checked it. The probe took the modules from
`lake query <lib>:modules` for the six libraries and took ownership from Lean's `const2ModIdx`,
the rule `Probe.ownedConstants` uses.

| Item | Observed | Consequence for an export claim |
| --- | --- | --- |
| Owned declaration entries (gate) | 8,351 entries, 8,349 unique names: 4,454 `def`, 3,074 `theorem`, 192 `inductive`, 437 `ctor`, 193 `recursor`, 1 `opaque`. Of these, 716 are private and 32 are partial. | The export root list must be this whole inventory. Equal counts would not show coverage. |
| Library-only probe | 8,347 names. Missing: `main.match_1` and `main.match_3` from the executable root `Main`, which `lake query <lib>:modules` does not list. | Roots must come from the manifest's claimed libraries *and* executable roots, not library globs. |
| Name collision | `main` is declared by both the verification library and `Main`. | No single environment, and so no single stream, holds both. The full surface needs at least two exports whose union must be reconciled. |
| Realized equation lemma | The equation lemma `ExecutableContract.run.eq_1` is owned by two surfaces (a policy module and a qualification module). | Ownership of realized generated declarations is not unique per module. A stream records one copy. |
| Generated `_unsafe_rec` helpers | 32, all `partial`: policy library 18, qualification library 5, core library 5, `Audit` 2, `AuditApp` 2. They match the gate's authorized helper count. | lean4export skips them by default. They carry no logical evidence, but an adapter must list them as authenticated exclusions, not as silent omissions. |
| Name literals | All 8,347 probe names round-tripped through `Syntax.decodeNameLit`, the exporter's root parser. | Private names can be passed as roots. |
| Inductive blocks | 192 inductive types in 191 blocks (the generated `Template.Maps.below` and `Maps.below_1` share one mutual block), with 437 constructors and 193 recursors. Mutual and nested blocks are modelled in-process. | Outside `checkDecls_consts`. Their preservation is not proved. |
| Axioms in the dependency closure | Exactly `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`, `Lean.ofReduceBool` or `Lean.trustCompiler`. | Con-leche accepts these three. It also tolerates an unused `sorryAx` declaration and admits the compiler-trust family (`Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`) through pins; none of those occurs here. The axioms would not cause a decline. |
| Static dependency closure | 30,132 safe, non-partial constants from the 8,347 library-module roots, which omit `Main`'s `main.match_1` and `main.match_3`: `Init` 10,792, `Mathlib` 8,499, owned 8,315, `Std` 2,328, `Lean` 103, `Batteries` 89, the project's excluded operational library 6. Computed by a temporary probe that follows lean4export's traversal, not by an export. | This sizes the stream an export would be. No export exists to confirm it. |

Missing obligations if the work were revived:
- a theorem or checked relation from the exporter to the environment;
- preservation for inductive, basis and quotient records;
- a correspondence for projection rewrites and in-process models;
- reconciliation across several streams for the colliding roots;
- an authenticated exclusion list for the generated helpers.

## Bounded evaluation

This plan was fixed before any export or checker run:

- **Stage 1:** one representative dependency cone, the `RegulaPolicy.Codec` and `AuditApp`
  roots. The first cone is Mathlib-free and the second uses Mathlib. Together they cover
  structures, inductives and well-founded definitions.
- **Stage 2:** the complete surface as two streams, and only if stage 1 raised no blocker.
- **Budgets:**
  - checker: one 360-second invocation per stage, `--verified --jobs=4`, under `timeout`;
  - export: 600 seconds per stream;
  - setup: 3,600 seconds;
  - no retries without a changed input.

Setup observations. These were taken before the value decision and are not compatibility
evidence. Machine: 14 hardware threads, 24 GiB, macOS 27.0 arm64.

- lean4export `v4.34.0` built in 3.6 s wall time, with 1.4 GB peak RSS.
  Binary SHA-256 `ad235f7ce3177ea0de2b66316f06361aff890683264c94cb31e91a46eeda60a2`.
- `lake build con-leche` at `ae0c0c4` with Lean `v4.33.0` completed in 47 s wall time
  (195 s user), with 2.5 GB peak RSS. Binary SHA-256
  `e28ef96f95aa4ccfcd47c237b8febc81ad00fdd0b301cde6be50e3fd6a4852ab`.
- `con-leche --help` exited `0` and printed the usage, modes, worker, switch and verdict-count
  text. The meanings of exits `1` and `3` and the out-of-memory rule come from the `Main.lean`
  module docstring.
- The gate run that produced the inventory took 107 s wall time. It is ordinary gate evidence.

Checker runs: **none performed.** Stage 1 and stage 2 are incomplete by design, because the
value decision stopped the study first. Upstream CI and upstream PERF timings are upstream data,
not a local bound.

## Costed option: downgrading Regula to Lean 4.33

This option was never taken; Regula stays on `v4.34.0`.

- **What it would unblock:** at most a same-toolchain match between Regula's `Nat` definitions
  and con-leche's primary `v4.33.0` pin, and its built-in prelude. The `v4.34.0-rc2` variant and
  the lean4export `v4.34.0` tag may already cover a `v4.34.0` export, but that is untested. A
  downgrade would fix none of the value, correspondence or name-collision findings.
- **What it would cost:**
  - moving the Lean, Mathlib (`5ed2965…`), Batteries and Verso (`cad4b63…`) pins backwards;
  - re-porting code written against 4.34.0 APIs, such as the strict JSON parser adapted from
    Lean `v4.34.0` and the engine producers' collectors;
  - invalidating all delivered qualification evidence: acceptance, rule examples, site and
    diagnostic campaigns;
  - pinning Regula *behind* upstream Lean on behalf of an optional checker.
- **Likely lag:** con-leche's `lean-toolchain` has been `v4.33.0`, unchanged, since the file
  was added in the repository's second commit (`ab16c06d`, 2026-08-19). Lean `v4.34.0`
  was released on 2026-09-14 and was still unadopted 11 days later. `v4.35.0-rc1` appeared on
  2026-09-15. The `v4.34.0-rc2` pin variant arrived on 2026-09-10. A 37-day history is too
  short to estimate a lag distribution. The lag is structural, because every toolchain needs a
  new pinner and dump upstream.

## Reproduction

```sh
# Inventory at the recorded revision (ordinary gate, ~110 s); owned
# declarations are under scope.surfaces[].report.declarations of the JSON output.
git checkout 56c53c2bb3ab5c2a7ddbbcb45759e65502b24c0d
lake exe axiomGate -- --json-out /path/to/gate.json

# Exporter and checker at the recorded pins (setup only; this study built them
# in the ignored `tmp/` scratch directory).
git clone https://github.com/leanprover/lean4export && git -C lean4export checkout v4.34.0
(cd lean4export && lake build lean4export)
git clone https://github.com/leanprover/con-leche && git -C con-leche checkout ae0c0c4e4ce6a0081648aff03fe9c39d002c4526
(cd con-leche && lake build con-leche && ./.lake/build/bin/con-leche --help)
```

The stage-1 and stage-2 commands were never run, and are listed only so a revival can reuse
the fixed plan. From the Regula root, pass `lake env` the exporter binary, the root modules, then
`--` and every expected owned name, redirecting to a stream file. Then run
`con-leche --verified --jobs=4` on that file under `timeout 360`. A revival must also check the
exporter's stderr for `not found` panics and reconcile the verdict count against the stream's
declaration records.

The temporary inventory and closure probes, the upstream clones and their builds lived in the
ignored `tmp/` directory and were removed after these results were recorded. The gate command
above reproduces the inventory counts at the recorded revision; later revisions add
owned declarations. The closure count is a derived observation from that
removed probe.

## When to revisit

Reopen #9 only if all of these hold:

- a con-leche release or tag supports Regula's toolchain;
- a theorem, or a checked relation, covers inductive-record preservation and the
  exporter-to-environment step;
- an adopter asks for kernel diversity through Regula, rather than through direct use.

Until then, this record and the closed #9 stand.

Return to the [documentation index](../README.md).
