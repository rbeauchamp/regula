# Performance notes

Practical guidance for efficient Lean code. These notes add no conformance rules. The
standard's normative requirement is the §3.6 contract obligation, which includes optimizations
([§3.6](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#36-contracts-for-executable-and-effectful-mechanisms)):
an optimized implementation meets the same contract, so an optimization preserves the
intended result, input domain, error behavior and relevant ordering of effects, and a faster
implementation of a different specification is not an optimization of the original contract.
These notes complement
[§3.2.5 on proof economy](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#325-proof-economy-four-cost-domains-and-one-trust-question)
and do not replace the correctness, foundation or execution-boundary rules of §3.6.

Efficient Lean code usually comes from choosing an appropriate representation and algorithm,
letting the runtime reuse storage, and avoiding work the result does not need. Start with the
simplest implementation that has the right semantics and a reasonable cost model; reserve
representation-specific tuning, forced inlining and parallel execution for a meaningful cost.

The examples use Core, Std or Lean itself, target the
[supported toolchain](../../README.md#supported-toolchain) (Lean `v4.34.0`) and are checked by
the documentation audit. The [references](#references) cite that release's sources; the
unversioned reference-manual pages and the tutorial are explanatory supplements.

## Where to start

| Situation | Good starting point | Important limit |
| --- | --- | --- |
| A CPU-bound application | [Build and run the release executable](#1-build-and-measure-the-execution-mode-you-intend-to-use). | Editor evaluation and compilation time are different measurements. |
| An evolving array, string or map | [Pass the current value forward](#2-preserve-opportunities-for-exclusive-ownership) without retaining old versions. | `let mut` does not guarantee exclusive ownership. |
| Updating an element that is itself a container | [Use `modify`/`modifyM`](#3-use-update-apis-that-avoid-avoidable-sharing) or the reference update API. | Other aliases can still require copying. |
| Growing a sequential result | [Use the appropriate builder](#4-choose-the-collection-and-builder-for-the-access-pattern); reserve a sensible known capacity. | Capacity is not logical size. |
| A numeric inner loop | [Keep the concrete scalar representation](#5-keep-a-numeric-calculation-in-its-concrete-representation). | Changing overflow or rounding changes the contract. |
| Large byte or floating-point collections | [Consider `ByteArray` or `FloatArray`](#6-use-compact-storage-when-large-numeric-collections-justify-it). | Generic `Array` storage is not packed. |
| A reduction, existence test or search | [Traverse directly and stop early](#7-avoid-unnecessary-passes-intermediate-collections-and-late-answers). | Preserve effect order and floating-point evaluation order. |
| Repeated text construction | [Append into one evolving string](#8-build-text-incrementally-and-respect-utf-8). | Retained prefixes and prepending defeat that cost model. |
| Temporary regions of a large input | [Use views; copy small long-lived results](#9-use-views-for-short-lived-processing-own-small-long-lived-results). | A small view can retain a large backing allocation. |
| Large linear traversals | [Prefer library implementations or accumulator loops](#10-prefer-stack-appropriate-traversals-and-library-implementations). | Termination does not imply bounded stack use. |
| Repeated key lookup | [Match the map to the query](#11-match-associative-containers-to-the-query). | Key costs and persistence requirements matter. |
| A validated value or index | [Keep proof-bearing interfaces](#12-keep-proofs-and-exploit-established-bounds). | Executable validation still costs work. |
| An expensive abstraction boundary | [Consider targeted specialization or inlining](#13-specialize-or-inline-only-at-relevant-boundaries). | More generated code can cost more. |
| Bulk input and output | [Work in chunks](#14-batch-bulk-output-and-stream-inputs). | Buffering changes latency and retention. |
| Independent expensive work | [Use coarse, bounded tasks](#15-parallelize-coarse-independent-work). | Scheduling, synchronization and sharing have costs. |
| Slow proofs or metaprograms | [Reuse results and profile the right phase](#16-apply-the-same-economy-to-proofs-builds-and-metaprograms). | Compiler-trusting proof production changes the trust account. |

The sections below are recommendations conditioned on the stated workload.

## 1. Build and measure the execution mode you intend to use

*When:* the code will run compiled, especially when execution time is significant compared with
startup.

Lake's `LeanConfig` defaults to `release`, which on the C backend supplies `-O3 -DNDEBUG`;
`relWithDebInfo` keeps `-O3` and adds debug information. Project flags can override the
defaults, and the TOML loader recognizes these build-type names.[^lake-config][^lake-toml]
There is normally no missing optimization switch in a release-configured project. Build an
executable target before measuring and run it with representative runtime input. A standalone
`lakefile.toml`, with `leanprover/lean4:v4.34.0` in `lean-toolchain`:

```toml
name = "perf_examples"
defaultTargets = ["perfExample"]
buildType = "release"

[[lean_exe]]
name = "perfExample"
root = "Main"
```

This minimal execution example is not a complete adoption of the standard's surface manifest or
audit.
Its `Main.lean` deliberately adds modulo `2^64`; it does not promise an unbounded sum:

```lean
import Init

/-- Add the converted indices below `count`, using UInt64 arithmetic. -/
def sumIndices (count : Nat) : UInt64 := Id.run do
  let mut total : UInt64 := 0
  for i in [:count] do
    total := total + i.toUInt64
  return total

/-- Read one natural-number argument and print the computed result. -/
def main (args : List String) : IO Unit := do
  let [arg] := args
    | throw (IO.userError "Usage: perfExample <count>")
  let some count := arg.toNat?
    | throw (IO.userError "count must be a natural number")
  IO.println (sumIndices count)
```

```sh
lake build perfExample
time ./.lake/build/bin/perfExample 1000000
```

This separates build cost from execution cost; the timed process still includes startup,
argument parsing and output. `#eval`, `lean --run` and kernel reduction answer different
questions from a built native executable.[^compilation] Do not use `native_decide` as a substitute
for an application build, or disable proof checking to make a build appear faster.

## 2. Preserve opportunities for exclusive ownership

*When:* repeatedly extending or modifying an array, byte buffer, string or collection whose
runtime can reuse an unshared allocation.

Lean uses reference counting. The runtime can mutate an allocation in place when it is unshared;
otherwise it preserves the old value, commonly by copying. Reuse depends on runtime sharing, not on
the number of variable names in the source.[^reference-counting][^arrays] Pass the evolving value to
the next operation and avoid retaining old versions the application does not need:

```lean
import Init

/-- The caller receives only the extended array. -/
def extend (xs : Array Nat) (x : Nat) : Array Nat :=
  xs.push x

/-- A different contract: the caller receives both versions. -/
def extendWithSnapshot (xs : Array Nat) (x : Nat) : Array Nat × Array Nat :=
  (xs, xs.push x)
```

The second cannot discard the original because it returns it. If retaining each prefix forces
copying prefixes of lengths `1, 2, …, n`, the copied-element count is their sum, hence quadratic.
Look for unnecessary aliases in history collections, closures, diagnostic state and queued work.
If every prefix must be retained, choose a representation suited to persistent versions.

*Limits:* persistent snapshots are sometimes the requirement; do not destroy them merely to
obtain uniqueness. A unique outer object does not make every object inside it unique. Reuse is an
implementation opportunity, not a linear-type guarantee or a performance theorem.

## 3. Use update APIs that avoid avoidable sharing

*When:* updating a nested array or another reference-counted value inside a container or
mutable reference.

`Array.modifyM` has a runtime replacement, `modifyMUnsafe`, that takes the element out of its
slot before applying the update, so the old slot does not keep it alive; `Array.modify` uses that
path. `ST.Ref.modify` and `modifyGet` likewise avoid the extra reference of a read-then-write
sequence.[^array-basic][^st]

```lean
import Init

/-- Append to the selected row; an out-of-range row index leaves rows unchanged. -/
def extendRow (rows : Array (Array Nat)) (rowIndex value : Nat) : Array (Array Nat) :=
  rows.modify rowIndex (fun row => row.push value)

/-- Append through the reference's update operation. -/
def appendPending (pending : IO.Ref (Array Nat)) (value : Nat) : IO Unit :=
  pending.modify (fun xs => xs.push value)
```

`IO.Ref` is the IO specialization of `ST.Ref`.[^io] A separate `get`, `push` and `set` can leave
the old array referenced by the cell during the update. The update APIs avoid that alias; they
do not promise zero allocation.

*Limits:* `Array.modify` leaves an invalid index unchanged; an API that promises rejection needs
an explicit check. Use the safe public interfaces, not their internal unsafe machinery. A
protocol over several references needs its own concurrency reasoning.

## 4. Choose the collection and builder for the access pattern

*When:* constructing sequences, implementing queues or accumulators, indexing repeatedly, or
maintaining persistent versions.

Arrays provide indexed access and capacity-based growth; lists provide front-oriented structure
and tail sharing; converting between them builds another representation.[^arrays][^list-basic][^list-impl]
For a custom list-producing traversal, prepend to a reversed accumulator and reverse once:

```lean
import Init

/-- Keep even inputs in their original order, illustrating a list builder. -/
def collectEven (xs : List Nat) : List Nat := Id.run do
  let mut reversed : List Nat := []
  for x in xs do
    if x % 2 == 0 then
      reversed := x :: reversed
  return reversed.reverse
```

In ordinary code `List.filter` expresses this operation directly. Repeated `acc ++ [x]`
traverses an ever longer left list, which is quadratic. Avoid repeated `length` calls and
indexing from a list's head; choose an array when positional access is the requirement.

An array's capacity is spare storage, not its size: `Array.emptyWithCapacity n` starts empty,
while `Array.replicate n value` has `n` entries.[^arrays]

```lean
import Init

/-- Produce exactly `count` natural-number offsets. -/
def strideOffsets (count stride : Nat) : Array Nat := Id.run do
  let mut offsets : Array Nat := Array.emptyWithCapacity count
  for i in [:count] do
    offsets := offsets.push (i * stride)
  return offsets
```

Reserve an inexpensive, credible size for a substantial output; let geometric growth handle
uncertain sizes. Reservation does not prevent copies caused by aliases.

## 5. Keep a numeric calculation in its concrete representation

*When:* arithmetic is a meaningful part of a loop, especially with machine words, floats or
repeated conversions.

Known concrete scalar types can use native scalar values, while polymorphic interfaces may box.
`Nat` has an efficient small-value representation with an arbitrary-precision
fallback.[^boxing][^runtime-header][^uint] Choose the semantics first; for intentionally modular word
arithmetic, keep the accumulator and constants in the word type:

```lean
import Init

/-- A simple rolling word accumulator, with all arithmetic modulo 2^64. -/
def rollingWord (seed : UInt64) (words : Array UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := seed
  for word in words do
    acc := acc * 33 + word
  return acc
```

It is not a cryptographic hash or a demonstration that `Array UInt64` is packed storage. Convert
at a representation boundary, then keep the inner calculation concrete; hoist genuinely invariant
conversions out of loops.

*Limits:* use `Nat` or `Int` when the result is unbounded. Fixed-width arithmetic wraps; `USize`
is platform-sized. Floating-point conversion and reassociation change answers; replacing exact
arithmetic with floats needs a specification and correspondence. A concrete type enables
optimization; it does not certify the generated instruction sequence or a speedup on every target.

## 6. Use compact storage when large numeric collections justify it

*When:* memory footprint or bandwidth matters for large homogeneous byte or float collections.

`ByteArray` and `FloatArray` store packed bytes and `double`s; a generic `Array` of numbers uses
object-sized slots and is not packed.[^byte-arrays][^float-array][^runtime-header] Some boxed values
fit in tagged immediates, but a generic slot is still not a packed byte.[^boxing] Keep the compact
representation through the processing stage:

```lean
import Init.Data.FloatArray.Basic

/-- Left-to-right accumulation of squared Float values. -/
def sumSquares (samples : FloatArray) : Float := Id.run do
  let mut total : Float := 0.0
  for sample in samples do
    total := total + sample * sample
  return total
```

`FloatArray` leaves floating-point semantics unchanged: the example fixes a left-to-right
accumulation order and does not assert exact real arithmetic or the absence of exceptional values.

A whole-collection conversion can erase the benefit for a short computation, and a logical
`data : Array …` field does not make extracting it free. Keep generic containers when their API,
persistence or small size fits better. A `ByteArray` holds bytes, not validated text or wider
words; byte order, bounds and alignment come from an explicit encoding, not the buffer.

## 7. Avoid unnecessary passes, intermediate collections and late answers

*When:* transforming a collection only to reduce it, or searching for one answer.

Core collections provide folds, iteration and short-circuiting search; a `for` over a range
iterates by bounds without materializing a list.[^array-basic][^list-basic][^range][^iterators]

```lean
import Init

/-- Sum qualifying natural numbers without building a filtered collection. -/
def sumAtLeast (xs : Array Nat) (cutoff : Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    if cutoff ≤ x then
      total := total + x
  return total

/-- Stop as soon as the input contains a value above the limit. -/
def hasOversized (xs : Array Nat) (limit : Nat) : Bool := Id.run do
  for x in xs do
    if limit < x then
      return true
  return false
```

`Array.any` and `find?` are the library forms. Avoid `toList`/`toArray` round trips, filtering
only to test nonemptiness, and collecting values only to sum them. Check each API's evaluation
contract before computing an expensive fallback eagerly: `Option.getD` is `@[macro_inline]` and
evaluates its default only for `none`.[^prelude]

```lean
import Init

/-- Reuse a cached string; invoke the fallback only for an absent value. -/
def cachedOrBuild (cached : Option String) (build : Unit → String) : String :=
  cached.getD (build ())
```

*Limits:* two passes may be clearer or reuse a result. The compiler can optimize some
compositions, so source syntax alone is not an allocation trace. Fusion must preserve effects,
errors and floating-point association.

## 8. Build text incrementally and respect UTF-8

*When:* rendering many fragments, or walking text in parsers.

The string runtime appends in place to an exclusive left operand and grows its
capacity.[^string-runtime] Keep one evolving output:

```lean
import Init

/-- Concatenate lines in order, placing a newline after each one. -/
def renderLines (lines : Array String) : String := Id.run do
  let mut output := ""
  for line in lines do
    output := output ++ line
    output := output.push '\n'
  return output
```

Each append still costs work proportional to the fragment, and capacity growth sometimes copies
the output; the pattern avoids recopying the whole prefix on every iteration. Repeated prepending
or retaining old outputs has a different cost model. Do not convert a string to a character list
to scan it; use positions, slices or traversal APIs over the UTF-8 text.

*Limits:* byte offsets, code-point positions and user-perceived characters differ. `String.take`
counts code points and returns a `String.Slice`.[^string-take] `String.Iterator` is an outgoing API;
the source points to the iterator framework and `String.Pos` instead.[^string-iterator] The runtime
stores a string's character length, so `String.length` does not rescan it.[^runtime-header]

## 9. Use views for short-lived processing; own small long-lived results

*When:* a parser or windowed computation uses a region of a much larger string or array.

`String.Slice` and `Subarray` are views of an underlying value, not copies; `Slice.copy` makes an
owned string.[^string-take][^string-basic][^arrays]

```lean
import Init.Data.String.TakeDrop

/-- A temporary view of up to sixteen code points. -/
def inspectPrefix (input : String) : String.Slice :=
  input.take 16

/-- An owned string result containing those code points. -/
def retainPrefix (input : String) : String :=
  (input.take 16).copy
```

Borrow while parsing and own at the long-lived result: copying a small token stored in a cache
lets a large input buffer become unreachable. A view retained while its backing array is updated
can defeat exclusive reuse. A view avoids allocation, not traversal: finding a code-point
boundary can still scan, and views and copies leave decoding and bounds obligations unchanged.

## 10. Prefer stack-appropriate traversals and library implementations

*When:* processing inputs whose depth or length can be large.

Accumulator-based tail recursion avoids pending stack work,[^tail-recursion] and Core supplies
efficient runtime implementations: `List.foldr`'s replacement `foldrTR` is array-based.[^list-impl]

```lean
import Init

/-- A left-to-right word sum using the library fold. -/
def sumWords (xs : List UInt64) : UInt64 :=
  xs.foldl (fun total x => total + x) 0

/-- Count matching inputs with structurally decreasing tail recursion. -/
def countMatching (predicate : Nat → Bool) (xs : List Nat) : Nat :=
  go xs 0
where
  /-- Add the number of matching elements of the list to the running count. -/
  go : List Nat → Nat → Nat
    | [], count => count
    | x :: rest, count =>
        go rest (if predicate x then count + 1 else count)
```

Inspect native behavior before rewriting a library function whose logical definition looks
non-tail-recursive. A tail-recursive traversal can still allocate a large result or retain
substantial input. A termination proof supplies no stack or time bound, and a replacement that
changes traversal or arithmetic order needs semantic justification.

## 11. Match associative containers to the query

*When:* repeated membership tests, keyed indexing, grouping or ordered retrieval.

Std's hash maps use bucket arrays with separate chaining; its tree maps are size-bounded balanced
trees with ordered queries. Both recommend linear use.[^dhashmap][^dtree-map] Use a hash map when
ordering is unnecessary, a tree map for ordered operations and an array for a dense bounded index.
Hashing and comparison of large keys are not free. Ask for the result once:

```lean
import Std.Data.HashMap.Basic

/-- Look up the stored score, using zero only for an absent key. -/
def scoreOrZero (scores : Std.HashMap String Nat) (name : String) : Nat :=
  scores.getD name 0

/-- Insert only when absent, returning any value that was already present. -/
def rememberOnce (seen : Std.HashMap String Nat) (name : String) (value : Nat) :
    Option Nat × Std.HashMap String Nat :=
  seen.getThenInsertIfNew? name value
```

`getThenInsertIfNew?` is documented as potentially faster than `get?` followed by
`insertIfNew`.[^hashmap] Hash iteration order is not a stable serialization format, and a cache
needs a valid key, intentional retention and an invalidation policy.

## 12. Keep proofs and exploit established bounds

*When:* a value is already validated, an index comes with a bound, or an optimization proposes
deleting proof-bearing wrappers.

Proofs are erased from compiled code.[^erasure] `Array.set` takes a bound proof and performs no
runtime bounds check.[^array-set] Decide a raw condition once and pass the evidence on:

```lean
import Init

/-- Use a caller-supplied index bound. -/
def readAt {α : Type} (xs : Array α) (i : Fin xs.size) : α :=
  xs[i.val]'i.isLt

/-- Decide a raw index once; the successful branch reuses that bound. -/
def replaceAt? (xs : Array Nat) (i value : Nat) : Option (Array Nat) :=
  if h : i < xs.size then
    some (xs.set i value h)
  else
    none
```

Reuse admitted invariants instead of revalidating internally. The `!` in an API name is not an
optimization guarantee. Erasure does not remove a runtime `Decidable` branch, a validation scan,
ordinary data stored alongside a proof, or every wrapper and typeclass dictionary, and an erased
classical proof does not make classically chosen data executable
([§3.8](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#38-delivering-executable-witnesses-with-required-evidence)).

## 13. Specialize or inline only at relevant boundaries

*When:* a hot small wrapper, higher-order loop or generic arithmetic interface prevents useful
optimization.

The compiler distinguishes `inline`, `noinline`, `always_inline` and `macro_inline`;
`@[specialize]` creates variants for static function and instance parameters.[^inline][^specialize]

```lean
import Init

/-- One concrete word operation, small enough to expose at a hot call site. -/
@[inline] def mixWord (acc word : UInt64) : UInt64 :=
  acc * 33 + word

/-- Sum accepted words; specialization may exploit the fixed predicate. -/
@[specialize] def sumAccepted (accept : UInt64 → Bool)
    (xs : List UInt64) (acc : UInt64) : UInt64 :=
  match xs with
  | [] => acc
  | x :: rest =>
      sumAccepted accept rest (if accept x then acc + x else acc)
```

These show placement, not a measured need. Excess inlining and specialization duplicate code and
increase compile time. When a convenient reference and an efficient implementation differ, a
proved `@[csimp]` equality connects them for compilation without changing kernel
reduction;[^csimp] prefer that, or an existing library replacement, over unsafe primitives or
unproved replacements. [`Audit.Economy`](../../audit/Audit/Economy.lean)'s `closedSumWithProof`
returns the closed form with the exact contract `2 * s = n * (n + 1)`, reusing the universal sum
proof; the proof is erased at runtime. That is checked functional evidence, not a measured
speedup or a machine-arithmetic cost bound.

## 14. Batch bulk output and stream inputs

*When:* formatting, small writes or whole-input materialization dominate the useful work.

`IO.FS.Stream` has byte and text operations; output can be buffered and flushing is
explicit.[^io] One output call is not necessarily one operating-system call, so source-level call
counts do not establish syscall counts. Work in byte chunks for binary data, process input
incrementally when the whole input is not needed, and batch small records:

```lean
import Init

/-- Batch output by a caller-selected positive number of lines. -/
def writeLinesBatched (stream : IO.FS.Stream) (lines : Array String)
    (batchLines : Nat) (_positive : 0 < batchLines) : IO Unit := do
  let mut buffer := ""
  let mut count := 0
  for line in lines do
    buffer := (buffer ++ line).push '\n'
    count := count + 1
    if batchLines ≤ count then
      stream.putStr buffer
      buffer := ""
      count := 0
  if count > 0 then
    stream.putStr buffer
```

The proof parameter states the configuration domain; it is not a runtime test. The function does
not flush after each batch, and IO failures propagate. This bounds lines between writes, not
bytes, and receives a materialized array, so it is not a whole-process bounded-memory claim.
Arbitrary byte chunks can split a UTF-8 encoding, so incremental decoding must keep decoder state.

## 15. Parallelize coarse independent work

*When:* independent computations are expensive enough to amortize scheduling.

`Task.spawn` launches evaluation and `Task.get` waits; values shared across threads use the
runtime's multi-threaded reference counting.[^tasks][^multithreading][^reference-counting]

```lean
import Init

/-- Expose two independent computations; task scheduling determines overlap. -/
def workPair (work : Array UInt64 → UInt64)
    (left right : Array UInt64) : UInt64 × UInt64 :=
  let pending := Task.spawn (fun _ => work left)
  let rightResult := work right
  (pending.get, rightResult)
```

The function exposes one parallel opportunity; it does not prove a speedup or force a schedule.
Divide substantial work into a bounded number of chunks; avoid a task per cheap operation.
Thresholds and worker counts are workload decisions. A parallel floating-point reduction can
round differently, and effect ordering, cancellation and concurrency correctness remain separate
obligations.

## 16. Apply the same economy to proofs, builds and metaprograms

When elaboration, tactic search or kernel checking dominates, reuse a theorem instead of
replaying a large reduction:

```lean
import Init.Data.List.Lemmas

/-- Reuse the universal theorem instead of expanding a particular long list. -/
example (xs : List Nat) : xs.reverse.reverse = xs :=
  List.reverse_reverse xs
```

A small term can still require expensive kernel reduction
([§3.2.5](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#325-proof-economy-four-cost-domains-and-one-trust-question)).[^list-lemmas]
`simp only`, named rewrites and decomposed lemmas narrow expensive search when needed. Raising a
heartbeat limit changes a budget, not the algorithm. Compiler-trusting proof production such as
`native_decide` is not a trust-preserving shortcut for a positive proof surface.[^decide]

Profile the phase you need to improve. `trace.profiler.threshold` is in milliseconds unless
heartbeat profiling is selected:[^trace]

```sh
lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=20 Path/Module.lean
```

This is an elaboration diagnostic, not an application benchmark. Do not infer kernel-checking
time solely from a tactic command's visible duration.

Reuse valid build artifacts during development. `precompileModules` defaults to `false`;
enabling it for a library builds shared libraries loaded on import, which can accelerate
imported metaprograms at extra compilation cost.[^precompile][^compilation] Opt in per library
and compare build-plus-use cost:

```toml
[[lean_lib]]
name = "MyTactics"
precompileModules = true
```

This is an entry for an existing package, not a complete configuration or a claim that its source
exists. It does not make the kernel execute compiled code, and the fresh-source and
kernel-admission evidence of
[§7.3](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#73-clean-elaboration-and-diagnostics)
remains separate.

For expression traversal, `Expr.find?` searches and `Expr.replace` rewrites with memoization of
shared nodes (`replaceNoCache` does not).[^find-expr][^replace-expr][^replace-runtime]

```lean
import Lean.Util.FindExpr

/-- Search the expression syntax for a reference to a specified constant. -/
def containsConstant (expression : Lean.Expr) (target : Lean.Name) : Bool :=
  (expression.find? (fun subexpression =>
    match subexpression with
    | .const name _ => name == target
    | _ => false)).isSome
```

This is a syntactic search, not a definitional-equality test or a scan of every dependency of the
named constants. Cache only computations whose context (environment, local context, metavariable
assignments, transparency) is fixed or part of the key, and bound the cache's lifetime.
`Expr.replace`'s memoization is evidence about that visitor, not a cache-validity result for other
metaprograms.

## 17. Measure the remaining tradeoffs

Avoiding a provably unnecessary traversal needs no benchmark. Measure when several reasonable
choices remain and their costs decide something real. Before measuring, state the decision
criterion, the time or memory metric and a bounded run budget. Keep the output semantics equal,
use representative inputs, build the target first, supply runtime input and consume the result,
and separate or include setup and output according to the question. Use repetitions to see
material variation and report the toolchain, build mode, input, hardware and
limitations.[^lake-config][^trace]

Make the benchmark's aliasing representative: keeping the original array to run several variants
makes each operate on a shared array, while a fresh value per run hides the copying cost of
production snapshots. `dbgTraceIfShared` and compiler IR traces help investigate sharing; `#eval`
can give misleading sharing observations.[^reference-counting] `relWithDebInfo` supports native
sampling.[^lake-config]

Keep evidence categories separate. A proof establishes its proposition; a source explanation
establishes the inspected mechanism; an operation count establishes a cost in its model; a
benchmark observes one execution. No timing proves semantic equivalence, and no foundation label
proves memory efficiency.

## References

Lean sources are cited at the `v4.34.0` release tag.

[^lake-config]: [`Lake/Config/LeanConfig.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/lake/Lake/Config/LeanConfig.lean): `BuildType`, `BuildType.leancArgs`, `LeanConfig.buildType`.
[^lake-toml]: [`Lake/Load/Toml.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/lake/Lake/Load/Toml.lean): `BuildType.decodeToml`.
[^compilation]: Lean Language Reference, [Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/): native execution, interpretation and precompiled imports.
[^reference-counting]: Lean Language Reference, [Reference Counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/): reuse, sharing, `dbgTraceIfShared` and IR diagnostics.
[^arrays]: Lean Language Reference 4.34.0, [Arrays](https://lean-lang.org/doc/reference/4.34.0/Basic-Types/Arrays/): representation, sharing, capacity, conversions and subarrays.
[^array-basic]: [`Init/Data/Array/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/Array/Basic.lean): `modifyMUnsafe`, `modifyM`, `modify`, `forIn` and folds.
[^st]: [`Init/System/ST.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/System/ST.lean): `Ref.modify`, `modifyGet` and their `Prim.Ref` runtime replacements.
[^io]: [`Init/System/IO.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/System/IO.lean): `IO.Ref`, `IO.FS.Stream`, buffering and `flush`.
[^list-basic]: [`Init/Data/List/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Basic.lean): list operations, folds and search.
[^list-impl]: [`Init/Data/List/Impl.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Impl.lean): tail-recursive implementations such as `filterMapTR` and `foldrTR` and their `csimp` equalities.
[^range]: [`Init/Data/Range/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/Range/Basic.lean): `Std.Legacy.Range`, `forIn'` and the `[:stop]` notation.
[^boxing]: Lean Language Reference, [Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/): scalar representations, polymorphic boxing and tagged immediates.
[^runtime-header]: [`include/lean/lean.h`](https://github.com/leanprover/lean4/blob/v4.34.0/src/include/lean/lean.h): array slots, scalar-array layout, small naturals and the stored string length. These are runtime implementation facts, not guarantees for every future backend.
[^uint]: [`Init/Data/UInt/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/UInt/Basic.lean) and [`BasicAux.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/UInt/BasicAux.lean): machine-word operations and `UInt64.ofNat`/`Nat.toUInt64`.
[^byte-arrays]: Lean Language Reference, [Byte Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Byte-Arrays/), and [`Init/Data/ByteArray/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/ByteArray/Basic.lean).
[^float-array]: [`Init/Data/FloatArray/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/FloatArray/Basic.lean): runtime-overridden representation, `push`, `forIn` and folds.
[^string-runtime]: [`runtime/object.cpp`](https://github.com/leanprover/lean4/blob/v4.34.0/src/runtime/object.cpp): `lean_string_push`, `lean_string_append` and capacity growth.
[^string-take]: [`Init/Data/String/TakeDrop.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/String/TakeDrop.lean): `String.take` and `drop`, counting code points and returning slices.
[^string-basic]: [`Init/Data/String/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/String/Basic.lean): `Slice.copy` and slice positions.
[^string-iterator]: [`Init/Data/String/Iterator.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/String/Iterator.lean): the outgoing `String.Iterator` API.
[^iterators]: Lean Language Reference, [Iterators](https://lean-lang.org/doc/reference/latest/Iterators/): producers, transformers and consumers.
[^tail-recursion]: *Functional Programming in Lean*, [Tail Recursion](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Tail-Recursion/).
[^dhashmap]: [`Std/Data/DHashMap/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Std/Data/DHashMap/Basic.lean): bucket array, separate chaining and linear-use guidance.
[^dtree-map]: [`Std/Data/DTreeMap/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Std/Data/DTreeMap/Basic.lean) and [`Std/Data/TreeMap/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Std/Data/TreeMap/Basic.lean): size-bounded trees, ordered queries and comparator laws.
[^hashmap]: [`Std/Data/HashMap/Basic.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Std/Data/HashMap/Basic.lean): `getD` and `getThenInsertIfNew?`.
[^erasure]: [`Lean/Compiler/LCNF/ToLCNF.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Compiler/LCNF/ToLCNF.lean): `visitAppArg` and `visitLet` erase proof terms; see also [§3.2.4](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#324-decidability-logical-vs-executable).
[^array-set]: [`Init/Data/Array/Set.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/Array/Set.lean): `Array.set`, `setIfInBounds` and `set!`.
[^inline]: [`Lean/Compiler/InlineAttrs.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Compiler/InlineAttrs.lean): `inline`, `noinline`, `always_inline` and `macro_inline`.
[^specialize]: [`Lean/Compiler/Specialize.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Compiler/Specialize.lean): specialization of static parameters.
[^csimp]: [`Lean/Compiler/CSimpAttr.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Compiler/CSimpAttr.lean): the supported constant-equality replacement.
[^tasks]: [`Init/Core.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Core.lean): `Task`, `Task.spawn`, `Task.get` and priorities.
[^multithreading]: Lean Language Reference, [Multi-Threaded Execution](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Multi-Threaded-Execution/).
[^decide]: [`Lean/Elab/Tactic/Decide.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Elab/Tactic/Decide.lean) and [`Lean/Meta/Native.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Meta/Native.lean): kernel decision and native proof evaluation.
[^trace]: [`Lean/Util/Trace.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Util/Trace.lean): `trace.profiler`, its threshold and heartbeat mode.
[^precompile]: [`Lake/Config/LeanLibConfig.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/lake/Lake/Config/LeanLibConfig.lean): `precompileModules`.
[^find-expr]: [`Lean/Util/FindExpr.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Util/FindExpr.lean): `Expr.find?` and `findExt?`.
[^replace-expr]: [`Lean/Util/ReplaceExpr.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Util/ReplaceExpr.lean): `Expr.replace` and `replaceNoCache`.
[^replace-runtime]: [`kernel/replace_fn.cpp`](https://github.com/leanprover/lean4/blob/v4.34.0/src/kernel/replace_fn.cpp): memoized replacement for shared nodes.
[^list-lemmas]: [`Init/Data/List/Lemmas.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/List/Lemmas.lean): `List.reverse_reverse`.
[^prelude]: [`Init/Prelude.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Prelude.lean): `Option.getD` and its conditional default.
