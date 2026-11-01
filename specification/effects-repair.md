# Effect-contract repair

This test-phase repair addresses the supplied findings F1 and F2 at `bca33f7a4d7504f23b7964be3c5f38c3579e8194`. The accepted intent is unchanged: decisions are proved over the executing definitions, external behaviour is an explicit hypothesis, verdict meanings are preserved, and nothing is released. The outer executor owns the other pipeline phases.

F1 is reproduced by derivation: instantiating the old `B.h4 path real` with `real = path` proves `¬ B.Crosses path` for every path, without an observation. The missing contract is that H4 constrains only successful real-path responses in the trace. The repair must admit a model with both a crossing and an unchanged non-crossing path. Its guarantee reaches the observation, not a later filesystem state.

F2 confuses one `println` argument with one physical line. Untrusted diagnostic text can contain a newline and supply an unprefixed verdict-looking line. The repair must constrain the serialized characters of every diagnostic, and connect that invariant to the printer and the whole-run contract. The compiler, Lean's UTF-8 output operation and the external stream remain trusted.

The design uses a response-indexed hypothesis for F1 and a construction with universal proofs for F2. A type alone cannot establish the behaviour of an external filesystem or output stream. The proof boundary must include serialization, rather than treating a message as an indivisible line; this is the specification link that let F2 pass unnoticed.

H4 and `read_no_link` compiled successfully on Lean 4.35.0, including `realPathBehaviour_crossing`, a universal construction from any two paths with different components. The inequality of those components is its explicit premise; it does not assert a concrete filesystem state. Before the output repair, the existing executable given the supplied multiline invalid profile printed an unindented passing-verdict line and exited 2. That run diagnoses F2; it is not correctness evidence.

The output repair constructs one diagnostic line by escaping LF and CR before adding the prefix. `detailText_no_break` and `detailText_lines` prove this for every string. `printed` now splits arguments into physical LF-delimited lines; `serialized_split` proves its correspondence to the concatenated character stream including `IO.println`'s terminators. `EndsWith` requires a single final line, and `endsWith_serialized`, `say_spec` and `run_meets` carry the distinction through the program actually interpreted. This reaches requested output, not partial OS writes, terminal rendering, external writers or child-process output. Those distinctions are now explicit in the documentation.

The original specification links failed in two ways: an external hypothesis omitted its observation premise, and an output contract treated an arbitrary string as a line. The repaired response-indexed structure and serialized-line contract prevent those same omissions from proving the claims again. No rule predicate or verdict mapping changed, and no test was added or changed.

## Focused verification

- **Machine-checked:** `lake -d specification build RegulaSpecification.Proofs.Behaviour`, exit 0, using Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Lake rebuilt the affected reader, shell, effect contracts and dependent proof modules through `Behaviour`; its final report was 52 dependency jobs. This was one target's dependency closure, not the repository gate or a test suite.
- **Machine-checked axiom coverage:** `lake -d specification env lean --stdin` imported that target and printed the transitive axioms of `realPathBehaviour_crossing`, `read_no_link`, `detailText_no_break`, `detailText_lines`, `serialized_split`, `endsWith_serialized`, `say_spec`, `run_meets`, `run_meets_record`, `executed_meets` and `table_rows`. All eleven reported exactly `propext`, `Classical.choice` and `Quot.sound`, the Standard-Logical foundation, and no `sorryAx` or project axiom. This is the named declarations' closure, not a new whole-repository axiom census.
- **Source linkage:** the table's print row calls `IO.println`; Lean's pinned `Init/System/IO.lean:1276-1277` defines that operation by appending LF. UTF-8 encoding, buffering, external function behaviour and compiled execution remain trusted as stated in the specification. No sampled run is used as proof of the repaired universal invariant.
- Every compiler invocation and the initial diagnostic ran through `no-mistakes admit --memory 16GiB --limit "none; the whole heavy-work budget, because nothing bounds the peak of the gate's builds" --`. No linter, formatter, full gate, pipeline-control or publication command ran in this phase.

**Independent review:** a fresh-context reviewer read the repair, the affected contracts and the pinned output implementation, and found no blocking F1/F2 issue. The review explicitly retained the component-inequality premise of the crossing construction and the requested-output boundary. It performed no builds and created no artifacts or processes. Its request to reconcile this record's pending-check text is incorporated here.

Open: none within this assigned repair phase. The outer executor retains responsibility for the remaining pipeline phases.

Sources: the accepted change intent and the supplied F1/F2 findings; `Proofs/Behaviour.lean`, `EffectsRecord.lean`, `Regula.Reader.say` and `Regula.Effect.table` supply the current contracts and execution linkage.

## Resource custody

The repair worker owned disposable scratch under `tmp/formal-linkage/`. Existing `.lake` and `specification/.lake` dependencies and build outputs predated this repair and are shared with later configured commands. The two existing build directories (192 MiB and 38 MiB) were preserved under scratch before the focused Lake build. Dependencies were reused in place and left untouched. Free space before allocation was 144 GiB, with estimated additional allocation below 2 GiB.

**Cleanup receipt:** both original build directories were restored from their preserved copies; `diff -qr` compared each restored directory with its copy and exited 0. The owned scratch root, including preserved copies and the direct-compiler output, was then removed, and its absence checked. No task-owned background process or server remains, and no machine service was changed. The original dependencies and pipeline-owned build artifacts remain for the outer executor; this record and the intentional source changes remain as deliverables. Current free space: 144 GiB. The reviewer created no resources to clean up.
