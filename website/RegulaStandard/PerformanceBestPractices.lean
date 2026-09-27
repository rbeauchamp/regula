import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "7. Performance Best Practices" =>
%%%
tag := "7-performance-best-practices"
file := "7-performance-best-practices"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "7-overview"
number := false
%%%

Efficient Lean code usually comes from choosing an appropriate representation and algorithm, letting the runtime reuse storage, and avoiding work the result does not need. These are ordinary engineering habits, not an instruction to tune every function. Start with the simplest implementation that has the right semantics and a reasonable cost model. Reserve representation-specific tuning, forced inlining, and parallel execution for cases where they address a meaningful cost.

This chapter covers native application performance, allocation and retained memory, and the development-time costs of proofs and metaprograms. It complements {ref "325-proof-economy-four-cost-domains-and-one-trust-question"}[§3.2.5 on proof economy]; it does not replace the correctness, foundation, or execution-boundary rules in {ref "36-contracts-for-executable-and-effectful-mechanisms"}[§3.6]. An optimization must preserve the intended result, input domain, error behavior, and relevant ordering of effects. A faster implementation of a different specification is not an optimization of the original contract.

*Version scope.* The repository and this chapter's checked examples target Lean `v4.34.0`. Implementation-specific descriptions retain the inspected `v4.33.1` source snapshot identified in the reference catalogue; that historical evidence does not establish every runtime mechanism on the newer release. The reference catalogue distinguishes pinned source from the versioned `4.33.0` Array manual and the moving language reference and tutorial. A moving manual is useful explanation, not a substitute for checking the supported release. The examples use Core, Std, or Lean itself; none requires Mathlib.

# Practical selection guide
%%%
tag := "practical-selection-guide"
number := false
%%%

:::table +header
*
  * Situation
  * Good starting point
  * Important limit
*
  * A CPU-bound application
  * Build and run the release executable (§7.1).
  * Editor evaluation and compilation time are different measurements.
*
  * An evolving array, string, or map
  * Pass the current value forward without retaining unnecessary old versions (§7.2).
  * `let mut` does not guarantee exclusive ownership.
*
  * Updating an element that is itself a container
  * Use `modify`/`modifyM` or the corresponding reference update API (§7.3).
  * Other aliases can still require copying.
*
  * Growing a sequential result
  * Use the appropriate list or array builder; reserve a sensible known capacity (§7.4).
  * Capacity is not logical size; over-reservation wastes memory.
*
  * A numeric inner loop
  * Keep the intended concrete scalar representation through the calculation (§7.5).
  * Changing overflow or rounding changes the contract.
*
  * Large byte or floating-point collections
  * Consider `ByteArray` or `FloatArray` (§7.6).
  * Generic `Array` storage is not automatically packed.
*
  * A reduction, existence test, or search
  * Traverse directly and stop when the answer is known (§7.7).
  * Preserve effect order and floating-point evaluation order.
*
  * Repeated text construction
  * Append into one evolving string; use UTF-8-aware APIs (§7.8).
  * Retained prefixes and repeated prepending defeat that cost model.
*
  * Temporary regions of a large input
  * Use views while processing; copy small results that must outlive the input (§7.9).
  * A small view can retain a large backing allocation.
*
  * Large linear traversals
  * Prefer library implementations or accumulator loops (§7.10).
  * Termination does not imply bounded stack use.
*
  * Repeated key lookup
  * Choose a hash map, ordered tree, or dense array for the actual query (§7.11).
  * Key costs and persistence requirements matter.
*
  * A validated value or index
  * Keep proof-bearing interfaces and reuse established bounds (§7.12).
  * Executable validation still costs work.
*
  * A demonstrably expensive abstraction boundary
  * Consider targeted specialization or inlining (§7.13).
  * More generated code can cost more to compile and execute.
*
  * Bulk input/output
  * Work in suitable chunks and avoid per-element formatting/output (§7.14).
  * Buffering changes latency and may retain more data.
*
  * Independent expensive work
  * Use coarse, bounded tasks (§7.15).
  * Scheduling, synchronization, and sharing have costs.
*
  * Slow proofs or metaprograms
  * Reuse results, profile the correct phase, and use library visitors (§7.16).
  * Compiler-trusting proof production changes the trust account.
:::

The sections below supply the source basis, examples, and qualifications for this guide. They are recommendations conditioned on the stated workload, not a second conformance checklist.

# 7.1 Build and measure the execution mode you intend to use
%%%
tag := "71-build-and-measure-the-execution-mode-you-intend-to-use"
number := false
%%%

*When.* An application, service component, or computational library will run as compiled code, especially when execution time is significant compared with startup.

Lake's `LeanConfig` defaults to `release`. On the pinned C-backend path, release supplies `-O3 -DNDEBUG`; `relWithDebInfo` retains `-O3` and adds debug information. Additional project flags can override the defaults. The TOML loader recognizes these build-type names.\[^lake-config\]\[^lake-toml\]

Use an executable target, build it before measuring, and run the resulting executable with representative runtime input. There is normally no missing optimization switch to add to an otherwise ordinary release-configured Lake project. For a standalone illustration, place this configuration in `lakefile.toml` and select `leanprover/lean4:v4.34.0` in `lean-toolchain`:

```toml
name = "perf_examples"
defaultTargets = ["perfExample"]
buildType = "release"

[[lean_exe]]
name = "perfExample"
root = "Main"
```

This is a minimal execution example, not a complete adoption of the standard's surface manifest or audit. In an existing project, add the appropriate target without replacing its other configuration. Use the following `Main.lean`. Its accumulator deliberately uses addition modulo `2^64`; it does not promise an unbounded natural-number sum.

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

With the default Lake output layout, the commands are:

```sh
lake build perfExample
./.lake/build/bin/perfExample 1000000
time ./.lake/build/bin/perfExample 1000000
```

This separates build cost from process execution cost. The timed process still includes startup, argument parsing, and one output operation; it is not an isolated inner-loop benchmark. A library benchmark should instead exercise the library through a suitable compiled driver and account for those surrounding costs.

*Limits.* `#eval`, `lean --run`, and kernel reduction are useful tools, but they are not interchangeable with a built native executable. Evaluation can use an interpreter alongside precompiled imported code; kernel reduction answers a different question altogether. Native precompilation can help frequently executed imported metaprograms, but its compilation overhead can outweigh that benefit for small workloads.\[^compilation\] Do not use `native_decide` as a substitute for an application build, or disable proof checking to make a proof build appear faster.

# 7.2 Preserve opportunities for exclusive ownership through updates
%%%
tag := "72-preserve-opportunities-for-exclusive-ownership-through-updates"
number := false
%%%

*When.* Repeatedly extending or modifying an array, byte buffer, string, or collection whose runtime implementation can reuse an unshared allocation.

Lean uses reference counting. Runtime implementations can mutate an allocation when doing so is unobservable because it is unshared; otherwise they preserve existing values, commonly by copying. The language still presents immutable values. Reference-counting optimizations depend on runtime sharing, not simply on the number of variable names in the source.\[^reference-counting\]\[^arrays\]

Pass the evolving value to the next operation and use the returned value. Avoid retaining an old version unless the application actually needs it.

```lean
import Init

/-- The caller receives only the extended array. -/
def extend (xs : Array Nat) (x : Nat) : Array Nat :=
  xs.push x

/-- A different contract: the caller receives both versions. -/
def extendWithSnapshot (xs : Array Nat) (x : Nat) : Array Nat × Array Nat :=
  (xs, xs.push x)
```

These functions intentionally have different contracts. The second cannot discard the original array because it returns it. When both versions remain observable, extending the array must preserve the old contents. The first exposes an opportunity for reuse, but its caller may still hold another reference.

For a local builder, `let mut current := initial` followed by `current := update current` expresses the useful data flow clearly. It does not require an `IO.Ref`; a pure `Id.run` computation is often enough. Look for unnecessary aliases in history collections, closures, diagnostic state, and queued work, not only in adjacent `let` bindings. If every growing prefix must be retained, choose a representation suited to persistent versions instead of expecting flat-array updates to remain cheap.

There is a simple cost warning behind this rule: if retaining each old prefix forces copying prefixes of lengths `1, 2, …, n`, the copied-element count is their sum, hence quadratic. This is an algorithmic consequence under that copying assumption, not a measurement of every program containing `push`.

*Limits.* Read-only sharing is useful; persistent snapshots are sometimes the requirement. Do not destroy those semantics merely to obtain uniqueness. A proof-only reference may disappear during proof erasure and need not cause runtime sharing. Conversely, a unique outer object does not imply that every object stored inside it is unique. Reuse is an implementation opportunity, not a linear-type guarantee or a performance theorem.

# 7.3 Use update APIs that avoid introducing avoidable sharing
%%%
tag := "73-use-update-apis-that-avoid-introducing-avoidable-sharing"
number := false
%%%

*When.* Updating a nested array or another reference-counted value stored inside a container or mutable reference.

The pinned implementation of `Array.modifyM` uses a runtime replacement that removes the selected element from the array before applying the update and putting the result back. This avoids keeping the old element alive solely through its old slot. `Array.modify` uses that path. The public reference APIs similarly provide `modify` and `modifyGet`; their runtime implementations avoid the extra reference retained by a naive read-then-write sequence.\[^array-basic\]\[^st\]

Express an element update through the container's operation rather than manually extracting, transforming, and reinserting it:

```lean
import Init

/-- Append to the selected row; an out-of-range row index leaves rows unchanged. -/
def extendRow (rows : Array (Array Nat)) (rowIndex value : Nat) : Array (Array Nat) :=
  rows.modify rowIndex (fun row => row.push value)
```

Here the outer array need not keep its old row reference merely while the callback constructs the updated row. Both the outer allocation and the row still need the appropriate uniqueness for in-place reuse. Repeating the same initial row in multiple slots creates sharing that this operation cannot wish away.

For an effectful accumulator already stored in an `IO.Ref`, use its update API:

```lean
import Init

/-- Append through the reference's update operation. -/
def appendPending (pending : IO.Ref (Array Nat)) (value : Nat) : IO Unit :=
  pending.modify (fun xs => xs.push value)
```

`IO.Ref` is the IO specialization of `ST.Ref`.\[^io\] A separate `get`, followed by `xs.push value`, followed by `set`, can leave the old `xs` referenced by the cell during the update. The purpose of this advice is to avoid that avoidable alias, not to promise zero allocation.

*Limits.* Preserve the operation's error policy: `Array.modify` leaves an invalid index unchanged. An API that promises rejection needs an explicit check or an appropriate proof-requiring operation. Use the safe public interfaces; do not reproduce their internal unsafe slot-taking machinery. A compound protocol involving several references needs its own concurrency reasoning, regardless of the efficiency of one update.

# 7.4 Choose the collection and builder for the access pattern
%%%
tag := "74-choose-the-collection-and-builder-for-the-access-pattern"
number := false
%%%

*When.* Constructing sequences, implementing queues or accumulators, indexing repeatedly, or maintaining persistent versions.

Arrays provide indexed access and capacity-based growth, with updates sensitive to sharing. Lists provide linked, front-oriented structure. Converting between lists and arrays constructs another representation. The standard library supplies traversal and builder implementations rather than requiring each application to implement them.\[^arrays\]\[^list-basic\]\[^list-impl\]

Prefer a list for front insertion, head/tail processing, and useful tail sharing. Prefer an array for frequent indexed access and a sequentially grown result that normally has one evolving owner. Neither is universally superior. A tiny association list may be simpler than a map, and an array is a poor default for repeatedly retaining large historical versions.

For a custom list-producing traversal, prepend to a reversed accumulator and reverse once rather than repeatedly append a singleton to the growing left prefix:

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

This is a teaching implementation. In ordinary code, the existing `List.filter` expresses this particular operation more directly. The builder pattern matters when the surrounding custom traversal cannot simply be replaced by that operation. Repeated `acc ++ [x]` traverses an increasingly long left list; the resulting sum of traversed lengths explains its quadratic behavior.

Avoid loops that repeatedly call a list's length or repeatedly index from its head. Traverse its spine once, or choose an array when positional access is the actual requirement. Do not convert an array to a list merely to obtain a fold that the array already provides.

## Reserve capacity when the estimate is useful
%%%
tag := "reserve-capacity-when-the-estimate-is-useful"
number := false
%%%

An array's capacity is spare storage, not its logical size. `Array.emptyWithCapacity n` begins empty and reserves room; `Array.replicate n value` instead constructs `n` logical entries. The distinction matters both for correctness and allocation.\[^arrays\]

```lean
import Init

/-- Produce exactly `count` natural-number offsets. -/
def strideOffsets (count stride : Nat) : Array Nat := Id.run do
  let mut offsets : Array Nat := Array.emptyWithCapacity count
  for i in [:count] do
    offsets := offsets.push (i * stride)
  return offsets
```

Reserve an inexpensive, credible output size when producing a substantial collection. Let ordinary geometric growth handle uncertain sizes. An extra traversal just to compute an exact capacity is not automatically worthwhile, and reserving a huge worst-case output for a sparse filter may increase peak memory needlessly. Capacity reservation does not prevent copies caused by aliases.

# 7.5 Keep a numeric calculation in its intended concrete representation
%%%
tag := "75-keep-a-numeric-calculation-in-its-intended-concrete-representation"
number := false
%%%

*When.* Arithmetic is a meaningful part of a computational loop, especially with machine words, floating-point values, or repeated conversions at abstraction boundaries.

Lean's compiler can represent known concrete scalar types with native scalar values, while polymorphic interfaces may require boxed representations. `Nat` also has an efficient small-value representation and falls back to arbitrary-precision operations when necessary; it is not uniformly a heap-allocated linked numeral. The pinned runtime header and integer definitions expose these distinctions.\[^boxing\]\[^runtime-header\]\[^uint\]

Choose the semantics first. For an intentionally modular word calculation, keep the accumulator, constants, and intermediate operations in the word type:

```lean
import Init

/-- A simple rolling word accumulator, with all arithmetic modulo 2^64. -/
def rollingWord (seed : UInt64) (words : Array UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := seed
  for word in words do
    acc := acc * 33 + word
  return acc
```

This does not bounce through `Nat` or a text representation after each elementary operation. It is not a cryptographic hash, an exact unbounded sum, or a demonstration that `Array UInt64` is packed storage. An element can be loaded from generic storage and then participate in a concretely typed arithmetic chain; storage and arithmetic are separate decisions.

Convert at a representation boundary when conversion is necessary, then keep the inner calculation concrete. Avoid repeated `toNat`/word conversions, integer/float conversions, or boxing through an unnecessarily generic callback inside the arithmetic chain. Hoist an input-independent conversion or computation out of a loop when its value and semantics really are invariant. Do not replace useful general interfaces throughout a program merely because one hot loop benefits from a concrete implementation.

*Limits.* Use `Nat` or `Int` when the required result is unbounded; their small-value fast paths make blanket replacement especially unjustified. Fixed-width arithmetic can wrap; `USize` is platform-sized. Floating-point conversion, reassociation, and reordering can change answers. Replacing mathematical real or exact rational operations with floating point needs the appropriate specification and correspondence, not a performance slogan. A concrete type enables optimization; it does not certify the generated instruction sequence or a speedup for every target.

# 7.6 Use compact storage when large numeric collections justify it
%%%
tag := "76-use-compact-storage-when-large-numeric-collections-justify-it"
number := false
%%%

*When.* Memory footprint, allocation, or bandwidth is significant for large homogeneous collections of bytes or floating-point numbers.

`ByteArray` stores bytes in a specialized buffer, and `FloatArray` has a specialized runtime representation with contiguous `double` elements. Generic arrays store values using Lean's generic object representation. In particular, a generic array of numerics is not automatically a byte-packed or double-packed array.\[^byte-arrays\]\[^float-array\]\[^runtime-header\]

:::table +header
*
  * Representation
  * Suitable use
  * Boundary to understand
*
  * `Array α`
  * General values, records, pointers, heterogeneous-by-construction domain objects
  * Generic element representation; do not infer packing from `α`.
*
  * `ByteArray`
  * Binary input/output, encodings, byte-oriented algorithms
  * Bytes are not automatically valid text or wider typed words.
*
  * `FloatArray`
  * Large collections using Lean `Float` arithmetic
  * Approximate floating-point semantics remain unchanged.
*
  * `List α`
  * Front-oriented traversal and useful structural sharing
  * Linked nodes are not compact numeric storage.
:::

A boxed value does not necessarily require a separate heap object: some values fit in tagged immediates. Nevertheless, an object-sized generic slot is not the same layout as a packed byte. Distinguish element boxing, slot width, and extra heap allocation.\[^boxing\]

Keep the compact representation through the processing stage instead of converting to a generic array for every operation:

```lean
import Init.Data.FloatArray.Basic

/-- Left-to-right accumulation of squared Float values. -/
def sumSquares (samples : FloatArray) : Float := Id.run do
  let mut total : Float := 0.0
  for sample in samples do
    total := total + sample * sample
  return total
```

The example preserves a particular accumulation order. It does not assert exact real arithmetic or the absence of exceptional floating-point values.

Prefer the specialized container when its element semantics and API fit a substantial workload. Keep generic containers when their ergonomics, library operations, persistence behavior, or small size make them more appropriate. An extra whole-collection conversion can erase a benefit for a short computation. In particular, a logical `data : Array ...` field in a specialized type does not imply that extracting that generic representation is free: its runtime representation and conversion can be different.\[^float-array\]\[^byte-arrays\]

*Limits.* Do not extrapolate `FloatArray` into an assumed built-in packed array for every scalar type. For wider-word binary storage, select an actual supported encoding with explicit byte order, bounds, and alignment assumptions; a byte buffer does not supply them by itself. Custom layouts and foreign numerical libraries are separate design choices, not baseline requirements.

# 7.7 Avoid unnecessary passes, intermediate collections, and late answers
%%%
tag := "77-avoid-unnecessary-passes-intermediate-collections-and-late-answers"
number := false
%%%

*When.* Transforming a collection only to reduce it, searching for one answer, or composing conversion and traversal operations over large inputs.

Core collections expose direct folds, iteration, filtering, and short-circuiting search operations. A range used by `for` has a bounds-based iteration implementation rather than requiring a materialized `List.range`. Std's iterator framework provides another way to describe producer/consumer pipelines without requiring an intermediate collection at every stage.\[^array-basic\]\[^list-basic\]\[^range\]\[^iterators\]

A count or reduction can inspect inputs directly:

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

The first function does not define a filtered output at all. The second exposes the early exit directly; `Array.any` is also an appropriate library interface. Use `find?` when the element itself is needed, rather than first determining that it exists and then searching again.

Avoid `toList`/`toArray` round trips, constructing a full range solely to iterate it, filtering solely to test nonemptiness, or collecting transformed values solely to sum them. When a result collection is required, prefer an appropriate combined operation such as `filterMap`, or a single clear builder. Reuse an expensive predicate result instead of recomputing it in successive phases when doing so actually reduces cost and does not retain excessive memory.

*Limits.* Two passes may be clearer, enable a useful size computation, or use a highly optimized library implementation. An intermediate result may be reused and therefore worth retaining. The compiler can optimize some compositions, so source syntax alone is not an allocation trace. Fusion must preserve observable effects, error behavior, and the intended arithmetic order. Do not fuse a floating-point reduction into a differently associated computation without addressing that semantic change.

## Do not compute an expensive fallback before it is needed
%%%
tag := "do-not-compute-an-expensive-fallback-before-it-is-needed"
number := false
%%%

Check the particular API's evaluation contract rather than assuming every default argument is eager or every convenience function is lazy. The pinned `Option.getD` is `@[macro_inline]`; its documentation states that the default is evaluated only in the `none` case.\[^prelude\] Keep a fallback computation at that conditional use rather than deliberately computing and retaining it beforehand.

```lean
import Init

/-- Reuse a cached string; invoke the fallback only for an absent value. -/
def cachedOrBuild (cached : Option String) (build : Unit → String) : String :=
  cached.getD (build ())
```

This is a specific documented behavior of `Option.getD`, not a blanket guarantee for every similarly named map operation or arbitrary function parameter. For an interface without that behavior, an explicit branch or a thunk-taking API can make the intended demand clear.

# 7.8 Build text incrementally and respect UTF-8
%%%
tag := "78-build-text-incrementally-and-respect-utf-8"
number := false
%%%

*When.* Rendering many fragments, producing logs or reports, or walking text in parsers and text-processing code.

The pinned string runtime supports appending to an exclusive left-hand string and growing its capacity as needed; a shared left operand requires preservation of the old data. This makes the direction of growth and the lifetime of old prefixes important.\[^string-runtime\]

Keep one evolving output and append fragments or characters:

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

Appending a fragment still costs work proportional to the fragment's bytes, and capacity growth sometimes copies the existing output. The point is to avoid needlessly copying the entire growing prefix on every iteration. Repeatedly prepending to a growing string, or retaining every old output version, has a different cost model. An existing joining operation is also suitable when it expresses the exact formatting policy.

Do not format values repeatedly inside an inner loop when the same formatted value can be computed once. Avoid converting an entire string to a character list just to scan it. Use string positions, slices, or supported traversal APIs that advance through the original UTF-8 text.

*Unicode and version limits.* A byte offset, a Unicode code-point position, and a user-perceived character are different concepts. The pinned `String.take` counts code points and returns a slice. The older `String.Iterator` API is explicitly described as outgoing; the source recommends `String.Pos` instead.\[^string-take\]\[^string-iterator\] Do not port old iterator examples mechanically. Also, do not assume `String.length` rescans its contents on this pin: the runtime stores the character length in the string object.\[^runtime-header\] Inspect the actual operation rather than applying a generic “strings are slow” rule.

# 7.9 Use views for short-lived processing; own small long-lived results
%%%
tag := "79-use-views-for-short-lived-processing-own-small-long-lived-results"
number := false
%%%

*When.* A parser, tokenizer, or windowed computation uses a region of a much larger string or array.

`String.Slice` operations can describe a region without allocating a new string, and `Slice.copy` obtains a string containing its bytes. A `Subarray` likewise refers to an underlying array and bounds. These are views, not independent copies.\[^string-take\]\[^string-basic\]\[^arrays\]

Separate a transient view from a result intended to survive independently:

```lean
import Init.Data.String.TakeDrop

/-- A temporary view of up to sixteen code points. -/
def inspectPrefix (input : String) : String.Slice :=
  input.take 16

/-- An owned string result containing those code points. -/
def retainPrefix (input : String) : String :=
  (input.take 16).copy
```

Use the view while the input is already needed. When storing a small token in a long-lived result or cache, copying that token can allow a much larger input buffer to become unreachable. The same reasoning applies to a short array window retained after the rest of the array is no longer useful. Decide from lifetime and retained size, not merely from whether an operation allocates immediately.

A view retained while its backing array is updated can also preserve an old reference and defeat exclusive reuse. Conversely, copying every temporary token wastes allocation when the input must remain alive anyway. The right boundary is often “borrow while parsing, own at the long-lived result,” rather than “always slice” or “always copy.”

*Limits.* Avoid promising constant-time character seeking merely because no string is allocated: finding a code-point boundary can still require traversal. If a slice covers the whole input, an implementation may reuse the already suitable string; the meaningful requirement is not retaining an unnecessarily larger backing region. Views and copies do not change text-decoding or bounds obligations.

# 7.10 Prefer stack-appropriate traversals and the library's efficient implementations
%%%
tag := "710-prefer-stack-appropriate-traversals-and-the-librarys-efficient-implementations"
number := false
%%%

*When.* Processing inputs whose depth or length can be large, or considering replacing a simple recursive definition with a hand-written optimized version.

Lean's performance tutorial explains accumulator-based tail recursion and the stack cost of pending recursive work. Core also supplies efficient runtime implementations for many familiar operations. For example, the pinned `List.foldr` runtime replacement uses an array-based implementation; its simple logical recursion is not the whole native cost model.\[^tail-recursion\]\[^list-impl\]

Prefer a standard fold or loop for an ordinary linear reduction:

```lean
import Init

/-- A left-to-right word sum using the library fold. -/
def sumWords (xs : List UInt64) : UInt64 :=
  xs.foldl (fun total x => total + x) 0
```

When custom recursion is necessary, place the evolving result in an accumulator so the recursive call has no remaining combination step:

```lean
import Init

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

Inspect native behavior before rewriting a library function solely because its logical definition looks non-tail-recursive. Prefer the existing library result and its equations when they fit. Lean is strict: an accumulator is not automatically a delayed chain of unevaluated arithmetic, but the accumulator's representation and the operation applied to it still matter.

*Limits.* A tail-recursive traversal can still allocate a large result or retain substantial input. A termination proof supplies no stack-size or wall-clock bound. Tree traversals, balanced divide-and-conquer algorithms, and short structural proofs need not all be converted into accumulator loops. A replacement that changes traversal or arithmetic order needs the corresponding semantic justification.

# 7.11 Match associative containers to the query and avoid duplicate lookup
%%%
tag := "711-match-associative-containers-to-the-query-and-avoid-duplicate-lookup"
number := false
%%%

*When.* Repeated membership tests, indexing by keys, grouping, caches, or ordered retrieval make a linear sequence scan inappropriate.

Std's hash maps use an array of buckets and separate chaining; their documentation recommends linear use to avoid copies. Std's tree maps use self-balancing size-bounded trees and support order-dependent queries. Their comparator laws and the equality/hash behavior of hash maps determine key identity.\[^dhashmap\]\[^dtree-map\]

Begin with a hash map or hash set for substantial repeated key lookup when ordering is unnecessary. Use a tree map or tree set when sorted operations or an ordered key interface matters. Use an array for a genuinely dense, bounded index domain. Do not replace a tiny list by a hash table simply because hash tables have favorable average lookup behavior.

Hashing, equality, and comparison can themselves be expensive. An expected constant number of bucket operations is not constant-time processing of an arbitrarily large string key. Poor hash distributions can worsen lookup substantially. Persistent versions also change allocation costs: a hash table's flat bucket array and a tree's shared paths behave differently. Tree-map documentation still recommends linear use where possible; “persistent structure” does not mean copying is free.\[^dhashmap\]\[^dtree-map\]

Ask for the result once instead of using `contains` followed by another lookup:

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

The second API combines the lookup and conditional insertion; its pinned documentation explicitly describes the potential saving over separate operations.\[^hashmap\]

*Limits.* These functions define concrete absent-key policies; preserve the policy required by the application. Do not assume hash iteration order is a stable serialization format. Match equality and hashing coherently, and use the laws required by the proofs about your map. A cache additionally needs a valid key, bounded or intentional retention, and an invalidation policy appropriate to what it stores.

# 7.12 Keep proofs and exploit established bounds instead of removing safety
%%%
tag := "712-keep-proofs-and-exploit-established-bounds-instead-of-removing-safety"
number := false
%%%

*When.* A runtime value has already been validated, an array index comes with a bound, or a proposal to optimize suggests deleting proof-bearing wrappers.

Proofs are erased from executable code. Public array operations can use proof arguments to justify access without a runtime bounds check; `Array.set`, for example, explicitly documents this behavior. The proof is not an instruction to recompute its proposition at runtime.\[^erasure\]\[^array-set\]

Validate at the boundary that needs a decision, then pass the evidence or refined value to downstream code:

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

The second definition performs the comparison because its result depends on whether the raw index is valid. Passing `h` to the array operation is different from performing another comparison. The first definition requires its caller to establish the bound; it does not claim that arbitrary input was validated for free.

Keep intrinsic invariants in admitted types. Reuse them rather than revalidating an already admitted value at every internal call. Supply an existing bound to safe indexing instead of choosing a panic-based operation merely because it looks lower-level. The `!` in an API name is not an optimization guarantee.

*Limits.* Proof erasure does not erase a runtime branch that computes `Decidable` data, a validation scan, or ordinary data stored alongside a proof. Nor does every wrapper or typeclass dictionary disappear automatically. Classical reasoning in an erased correctness proof is separate from using classical choice to produce runtime data; the latter does not become executable merely because a proof is erased. Preserve the foundation and executable-witness distinctions in {ref "38-delivering-executable-witnesses-with-required-evidence"}[§3.8].

# 7.13 Keep useful abstraction; specialize or inline only at relevant boundaries
%%%
tag := "713-keep-useful-abstraction-specialize-or-inline-only-at-relevant-boundaries"
number := false
%%%

*When.* A frequently executed small wrapper, higher-order loop, or generic arithmetic interface prevents useful optimization, and the cost matters enough to inspect.

The compiler supports ordinary and stronger inlining controls. `@[specialize]` creates variants for static parameters and can avoid repeatedly allocating or calling closures; by default it considers suitable function and instance parameters. These mechanisms target a specific boundary rather than changing a program's mathematical type.\[^inline\]\[^specialize\]

A small wrapper may be an appropriate inlining boundary:

```lean
import Init

/-- One concrete word operation, small enough to expose at a hot call site. -/
@[inline] def mixWord (acc word : UInt64) : UInt64 :=
  acc * 33 + word
```

For a custom recursive combinator whose predicate remains fixed through the traversal, specialization can expose that predicate in a generated variant:

```lean
import Init

/-- Sum accepted words; specialization may exploit the fixed predicate. -/
@[specialize] def sumAccepted (accept : UInt64 → Bool)
    (xs : List UInt64) (acc : UInt64) : UInt64 :=
  match xs with
  | [] => acc
  | x :: rest =>
      sumAccepted accept rest (if accept x then acc + x else acc)
```

These examples demonstrate placement, not a measured need for either annotation. A standard fold may already provide the appropriate optimized implementation.

First write clear generic code and reuse the library. Add an annotation when exposing a small operation or a stable callback addresses an identifiable hot-path cost. Prefer a local change over making an entire library concrete. Excessive inlining and specialization can duplicate bodies, increase native compilation time and code size, and trade call overhead for instruction-cache pressure. Treat those as tradeoffs to check, not as a reason to ban higher-order functions or typeclasses.

*Proof-oriented alternatives.* When a convenient logical reference and an efficient implementation differ, a proved `@[csimp]` equality can connect them for compilation without changing kernel reduction. The pinned attribute requires its supported constant-equality form. It is not an automatic proof that an arbitrary runtime replacement is correct, nor a guarantee of faster kernel replay.\[^csimp\] Prefer existing proof-backed library replacements before authoring another implementation. Ordinary application code should not reach for unsafe primitives or unproved replacements as its first performance technique.

The repository's `Economy.closedSumWithProof` in {repo "audit/Audit/Economy.lean"}[Audit.Economy] returns the computed closed form with the exact contract `2 * s = n * (n + 1)`. It reuses the universal sum proof; runtime data uses `closedSum`, and the proof is erased. This is checked functional evidence, not a measured speedup or a machine-arithmetic cost bound.

# 7.14 Batch bulk output and stream inputs when whole-input retention is unnecessary
%%%
tag := "714-batch-bulk-output-and-stream-inputs-when-whole-input-retention-is-unnecessary"
number := false
%%%

*When.* Processing files, emitting many records, or handling enough data that formatting, small writes, or whole-input materialization dominates the useful work.

`IO.FS.Stream` has byte-oriented `read`/`write` and text-oriented operations. Physical output can be buffered, and flushing is explicit. The pinned source also supplies whole-stream convenience operations; choosing such an operation means choosing to retain its whole result.\[^io\]

Work with byte chunks for binary data and decode at a deliberate text boundary. Process input incrementally when the result does not require the complete input in memory. Avoid printing or pretty-printing inside a numeric inner loop unless that output is the workload being measured. Batch many small logical records into suitable chunks, but flush when an interactive protocol or visibility requirement needs it. One high-level output call is not necessarily one operating-system call, so do not claim syscall counts from source-level call counts alone.

This bounded-number-of-lines batcher emits input lines in order, with a newline after each:

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

The proof parameter states the intended configuration domain; it is not a runtime test. A caller can choose a modest batch size from the workload rather than follow a universal magic number. The function does not explicitly flush after each batch, and IO failures propagate normally.

*Limits.* This bounds the number of lines accumulated between writes, not their byte size; a single line can be arbitrarily large. It also receives an already materialized input array, so it is not a whole-process bounded-memory claim. A production byte-budgeted or streaming interface needs its own chunk and oversized-record policy. Arbitrary byte chunks can split a UTF-8 encoding; incremental text decoding must retain the necessary decoder state rather than assume every chunk is independently valid text.

# 7.15 Parallelize coarse independent work, not individual cheap operations
%%%
tag := "715-parallelize-coarse-independent-work-not-individual-cheap-operations"
number := false
%%%

*When.* Independent computations are expensive enough to amortize task scheduling and there are available hardware and memory resources.

`Task.spawn` launches evaluation and `Task.get` waits for a result. Ordinary-priority tasks use the runtime's worker pool. Values shared across threads can require the runtime's multi-threaded reference-counting treatment.\[^tasks\]\[^multithreading\]\[^reference-counting\]

Expose independent work before waiting:

```lean
import Init

/-- Expose two independent computations; task scheduling determines overlap. -/
def workPair (work : Array UInt64 → UInt64)
    (left right : Array UInt64) : UInt64 × UInt64 :=
  let pending := Task.spawn (fun _ => work left)
  let rightResult := work right
  (pending.get, rightResult)
```

The function exposes one parallel opportunity. It does not prove a speedup or force a particular schedule. Immediately spawning and waiting before starting any other work would provide no such overlap opportunity.

Divide a substantial workload into a bounded number of useful chunks. Avoid a task per scalar, per tiny predicate, or per short line. Include task creation, synchronization, reference-counting overhead, and simultaneously live working sets in the cost model. Prefer independent inputs or read-only sharing to concurrent updates of one evolving buffer. Avoid creating far more outstanding tasks than the workload and memory budget can use.

*Limits.* Input-size thresholds and worker counts are workload decisions, not universal constants. Pure tasks and effectful tasks have different APIs and failure/lifetime considerations. Changing a sequential floating-point reduction into a parallel tree can change rounding. Side-effect ordering, cancellation, and concurrency correctness remain separate obligations; parallelism is not a default improvement to every loop.

# 7.16 Apply the same economy to proofs, builds, and metaprograms
%%%
tag := "716-apply-the-same-economy-to-proofs-builds-and-metaprograms"
number := false
%%%

## Reuse proofs instead of repeatedly replaying large computations
%%%
tag := "reuse-proofs-instead-of-repeatedly-replaying-large-computations"
number := false
%%%

*When.* Elaboration, tactic search, proof terms, or kernel checking—not the final executable—dominates development time.

Prefer a reusable theorem or structural argument when it replaces a large repeated reduction. For a familiar list equation, use the existing result:

```lean
import Init.Data.List.Lemmas

/-- Reuse the universal theorem instead of expanding a particular long list. -/
example (xs : List Nat) : xs.reverse.reverse = xs :=
  List.reverse_reverse xs
```

The example reuses Core's `List.reverse_reverse`.\[^list-lemmas\] The tradeoff is explained in {ref "325-proof-economy-four-cost-domains-and-one-trust-question"}[§3.2.5]: a small term can still require expensive kernel reduction. `simp only`, named rewrite lemmas, explicit types, and decomposed helper lemmas can narrow expensive search when the goal needs them; they are not mandatory replacements for every convenient use of automation. Raising a heartbeat or recursion-depth limit changes a budget, not the underlying algorithm. Compiler-trusting proof production such as `native_decide` is not a trust-preserving shortcut for a positive proof surface. Native metaprograms that return ordinary kernel-checked proof terms retain the ordinary proof boundary.\[^list-basic\]\[^decide\]

## Profile the elaboration phase you actually need to improve
%%%
tag := "profile-the-elaboration-phase-you-actually-need-to-improve"
number := false
%%%

Lean provides `trace.profiler`, a threshold, and optional profile-file output. On the pin, the ordinary threshold is in milliseconds unless heartbeat-based profiling is selected.\[^trace\]

For an existing module, replace the path in this command with its actual source path:

```sh
lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=20 Path/Module.lean
```

This is an elaboration diagnostic, not a native application benchmark. Use its result to locate expensive declarations or tactic work, then inspect the argument, search, or generated term responsible. Do not infer kernel-checking time solely from the visible duration of a tactic command.

## Use incremental builds appropriately; precompile expensive imported metaprograms selectively
%%%
tag := "use-incremental-builds-appropriately-precompile-expensive-imported-metaprograms-selectively"
number := false
%%%

Lake's `precompileModules` option defaults to false for a library. Enabling it builds shared libraries loaded on import and can accelerate imported metaprograms. The manual also identifies the additional compilation cost.\[^precompile\]\[^compilation\]

Reuse valid build artifacts during normal development instead of repeatedly cleaning the entire dependency tree. Factor modules along real interfaces so a local change need not force unrelated work, without creating dozens of artificial files or making import minimality a universal rule. For a library whose imported tactics or metaprograms perform significant recurring computation, consider enabling `precompileModules` in that library's Lake configuration and compare total build-plus-use cost. Do not enable it everywhere by reflex.

For example, a TOML library entry may opt in explicitly:

```toml
[[lean_lib]]
name = "MyTactics"
precompileModules = true
```

This is an entry to add to an actual package, not a complete package configuration or a claim that its source exists. It affects imported runtime code; it does not make the kernel execute compiled code when checking a proof. The fresh-source and kernel-admission evidence required by {ref "83-clean-elaboration-and-diagnostics"}[§8.3] remains separate from efficient incremental development.

## Use expression visitors and cache only computations whose context is represented
%%%
tag := "use-expression-visitors-and-cache-only-computations-whose-context-is-represented"
number := false
%%%

*When.* A tactic, elaborator, analyzer, or transformation traverses Lean expressions repeatedly.

Lean provides `Expr.find?` for searching and `Expr.replace` for rewriting. The pinned native replacement visitor memoizes results for shared expression nodes; `replaceNoCache` is a separate API. Reimplementing traversal is therefore not automatically simpler or faster.\[^find-expr\]\[^replace-expr\]\[^replace-runtime\]

```lean
import Lean.Util.FindExpr

/-- Search the expression syntax for a reference to a specified constant. -/
def containsConstant (expression : Lean.Expr) (target : Lean.Name) : Bool :=
  (expression.find? (fun subexpression =>
    match subexpression with
    | .const name _ => name == target
    | _ => false)).isSome
```

This is a syntactic search, not a test of definitional equality or a scan of every dependency of the named constants. Use an existing visitor with the right semantics before constructing another traversal. For heavily shared expression graphs, a naive tree walk can repeat work on the same subterm many times.

Cache genuinely repeated expensive analyses, not every cheap lookup. A result depending on the environment, local context, metavariable assignments, or transparency mode is not safely keyed by an expression alone unless those contextual inputs are fixed or represented. Limit cache lifetime so retained expressions and environments do not become a memory problem. Reuse a loaded environment or an unchanged analysis prefix across a batch when valid, rather than rebuilding it per element. These are context-validity and workload deductions, not claims that `Expr.find?` itself implements arbitrary contextual caching.

# 7.17 Measure remaining tradeoffs without turning every edit into a benchmark project
%%%
tag := "717-measure-remaining-tradeoffs-without-turning-every-edit-into-a-benchmark-project"
number := false
%%%

The preceding practices often follow directly from the algorithm or representation. Avoiding a provably unnecessary traversal does not require a benchmark campaign. Measurement becomes useful when several reasonable choices remain and their costs affect a real decision: reserving capacity versus an extra pass, generic versus packed storage, one implementation versus another, or sequential versus parallel work.

*Measurement procedure.* State the decision criterion, relevant time or memory metric, and a bounded run/resource budget before measuring. State the cost being compared, use the same required output semantics, and exercise representative input sizes and shapes. Build the chosen target before runtime measurements. Supply runtime input and consume the result so the workload is not merely an unused pure expression or an easily precomputed constant. Separate input construction, formatting, and output when they are not part of the question; include them when end-to-end behavior is the question. Within that budget, use repetitions to identify material variation and report unresolved uncertainty; examine peak retained memory when relevant to the decision. Report the toolchain, build mode, input, hardware context, and limitations rather than presenting one timing as a universal law.\[^lake-config\]\[^trace\]

## Check ownership in the benchmark itself
%%%
tag := "check-ownership-in-the-benchmark-itself"
number := false
%%%

A benchmark that keeps the original array to run several variants can accidentally make every variant operate on a shared array, even if production code consumes the input. Conversely, a benchmark that constructs a fresh unique value each time can hide the copying cost of production snapshots. Make the aliasing and lifetime pattern representative; the two cases answer different questions.

The runtime's `dbgTraceIfShared` diagnostic can help investigate unexpected sharing, and compiler IR traces can show reference-counting and generated-code decisions. The reference-counting documentation warns that `#eval` can give misleading sharing observations; use the appropriate compiled context. These are targeted diagnostics, not calls to leave in a timed inner loop or production implementation.\[^reference-counting\]

For native sampling, a build with optimization and suitable debug information can help identify hot paths; the pinned `relWithDebInfo` configuration supports that combination. Inspect actual generated code when a decision depends on a particular unboxing, specialization, or reuse outcome. Most everyday code does not need instruction-level inspection.\[^lake-config\]

## Keep the evidence categories separate
%%%
tag := "keep-the-evidence-categories-separate"
number := false
%%%

A proof establishes its formal proposition. An API/source explanation establishes the documented or inspected implementation mechanism. An operation-count argument establishes a cost in that stated model. A benchmark observes a particular execution. None should silently stand in for the others. In particular, no timing proves semantic equivalence, no foundation label proves memory efficiency, and no absence of a benchmark makes a simple algebraic cost argument invalid. Preserve the exact contracts and remaining native-runtime assumptions while improving performance.

# Summary
%%%
tag := "7-summary"
number := false
%%%

Competent everyday Lean performance work begins with representation, ownership, and avoiding unnecessary work. Use compiled release execution for the corresponding runtime question; keep evolving containers linear where their APIs can reuse storage; use safe nested-update operations; select collections and numeric representations for the actual semantics; avoid needless materialization; and account for the lifetime of views and cached data. Proofs and pure functions are compatible with these practices.

Inlining, specialization, precompilation, batching thresholds, and parallelism are conditional tools, not universal annotations or mandatory rewrites. Apply the clear algorithmic and representation rules first. Measure when the remaining tradeoff matters, and preserve correctness and evidence boundaries throughout.

# Authoritative references
%%%
tag := "authoritative-references"
number := false
%%%

The links below are the source of truth for the stated mechanisms at their identified scope. Pinned source retains the historical `v4.33.1` source snapshot; declarations or sections to inspect are named so readers need not rely on an unversioned search result. The moving manuals and tutorial are explanatory supplements.

\[^lake-config\]: Lean/Lake, [pinned `Lake/Config/LeanConfig.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/lake/Lake/Config/LeanConfig.lean): `BuildType`, `BuildType.leancArgs`, and `LeanConfig.buildType`; release/debug flags, defaults, and overrides.

\[^lake-toml\]: Lean/Lake, [pinned `Lake/Load/Toml.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/lake/Lake/Load/Toml.lean): `BuildType.decodeToml` and generated configuration decoders; TOML build-type and target configuration handling.

\[^compilation\]: Lean Language Reference, [Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/), especially compilation and interpretation. Moving documentation; distinguishes native execution, interpretation, and the cost/benefit of precompiling imported code.

\[^reference-counting\]: Lean Language Reference, [Reference Counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/): reuse, sharing, borrowed parameters, `dbgTraceIfShared`, and IR diagnostics. Moving documentation; the pinned container implementations provide the corresponding concrete examples.

\[^arrays\]: Lean Language Reference *4.33.0*, [Arrays](https://lean-lang.org/doc/reference/4.33.0/Basic-Types/Arrays/): runtime representation, sharing, size/capacity, growth, conversions, and subarrays. Versioned explanatory source, not the chapter's exact compiler pin.

\[^array-basic\]: Lean, [pinned `Init/Data/Array/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/Array/Basic.lean): `modifyMUnsafe`, `modifyM`, `modify`, `forIn`, and fold implementations; safe public APIs and optimized runtime paths.

\[^st\]: Lean, [pinned `Init/System/ST.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/System/ST.lean): public `Ref.modify`/`modifyGet` and their `Prim.Ref` runtime replacements. The internal unsafe implementation is evidence about the public API, not code applications should copy.

\[^io\]: Lean, [pinned `Init/System/IO.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/System/IO.lean): `IO.Ref`, `IO.FS.Stream`, buffering/flush documentation, and whole-stream convenience operations.

\[^list-basic\]: Lean, [pinned `Init/Data/List/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/List/Basic.lean): public list operations, fold equations, and traversal/search interfaces; inspect the corresponding runtime implementations where replaced.

\[^list-impl\]: Lean, [pinned `Init/Data/List/Impl.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/List/Impl.lean): tail-recursive implementations, including `filterMapTR` and `foldrTR`, and their compiler-simplification equalities.

\[^range\]: Lean, [pinned `Init/Data/Range/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/Range/Basic.lean): `Std.Legacy.Range`, `forIn'`, and the `[:stop]` compatibility notation used by the examples. This chapter does not require choosing that range spelling over a newer supported range API.

\[^boxing\]: Lean Language Reference, [Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/): concrete scalar representations, polymorphic boxing, tagged immediates, and generic arrays. Moving explanatory documentation.

\[^runtime-header\]: Lean, [pinned runtime header `include/lean/lean.h`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/include/lean/lean.h): generic array slots, byte/float scalar-array layout, small-natural arithmetic paths, and cached string length. These are runtime implementation facts, not guarantees for every future backend.

\[^uint\]: Lean, [pinned `Init/Data/UInt/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/UInt/Basic.lean): machine-word operations and their logical representations; [pinned `BasicAux.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/UInt/BasicAux.lean) supplies `UInt64.ofNat`, `Nat.toUInt64`, and related conversions. Keep width and overflow semantics explicit.

\[^byte-arrays\]: Lean Language Reference, [Byte Arrays](https://lean-lang.org/doc/reference/latest/Basic-Types/Byte-Arrays/), and Lean's [pinned `Init/Data/ByteArray/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/ByteArray/Basic.lean): compact byte representation, generic-array conversion costs, copy/append, and direct traversal.

\[^float-array\]: Lean, [pinned `Init/Data/FloatArray/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/FloatArray/Basic.lean): runtime-overridden constructor/projection, capacity, push, direct `forIn`, and folds. The runtime header above identifies its double-element storage.

\[^string-runtime\]: Lean, [pinned `runtime/object.cpp`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/runtime/object.cpp): `mk_capacity`, `lean_string_push`, and `lean_string_append`; capacity growth and exclusive/shared append paths.

\[^string-take\]: Lean, [pinned `Init/Data/String/TakeDrop.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/String/TakeDrop.lean): `String.take`/`drop` and related slice-producing operations; counts are Unicode code points.

\[^string-basic\]: Lean, [pinned `Init/Data/String/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/String/Basic.lean): `Slice.copy`, extraction, slice positions, and operations retaining the same underlying string.

\[^string-iterator\]: Lean, [pinned `Init/Data/String/Iterator.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/String/Iterator.lean): migration guidance from the outgoing legacy iterator to `String.Pos`.

\[^iterators\]: Lean Language Reference, [Iterators](https://lean-lang.org/doc/reference/latest/Iterators/): producer, transformer, and consumer interfaces. Moving documentation; no version-specific iterator pipeline is assumed by this chapter's examples.

\[^tail-recursion\]: _Functional Programming in Lean_, [Tail Recursion](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Tail-Recursion/): stack behavior and accumulator transformations. Official tutorial, not a version-pinned API reference.

\[^dhashmap\]: Lean/Std, [pinned `Std/Data/DHashMap/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Std/Data/DHashMap/Basic.lean): bucket-array/separate-chaining representation, resizing, key assumptions, and explicit guidance to use the map linearly.

\[^dtree-map\]: Lean/Std, [pinned `Std/Data/DTreeMap/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Std/Data/DTreeMap/Basic.lean), together with [the nondependent `TreeMap` interface](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Std/Data/TreeMap/Basic.lean): size-bounded trees, ordered queries, comparator laws, and linear-use guidance.

\[^hashmap\]: Lean/Std, [pinned `Std/Data/HashMap/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Std/Data/HashMap/Basic.lean): `getD`, optional lookup, and `getThenInsertIfNew?`; the combined-operation documentation explicitly compares separate lookup and insertion.

\[^erasure\]: Lean, [pinned `Lean/Compiler/LCNF/ToLCNF.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Compiler/LCNF/ToLCNF.lean): `visit` and `visitAppArg` erase proof terms after checking that their types are propositions; `visitLet` handles proof-valued bindings separately. The exact proof-versus-runtime-decision distinction is also developed in {ref "324-decidability-logical-vs-executable"}[§3.2.4].

\[^array-set\]: Lean, [pinned `Init/Data/Array/Set.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/Array/Set.lean): `Array.set` requires an index-bound proof and documents no runtime bounds check; distinct operations supply checked or panic-based boundary behavior.

\[^inline\]: Lean, [pinned `Lean/Compiler/InlineAttrs.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Compiler/InlineAttrs.lean): the differing meanings of `inline`, `noinline`, `always_inline`, and `macro_inline`.

\[^specialize\]: Lean, [pinned `Lean/Compiler/Specialize.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Compiler/Specialize.lean): specialization of static parameters, defaults for function/instance parameters, and closure-related motivation.

\[^csimp\]: Lean, [pinned `Lean/Compiler/CSimpAttr.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Compiler/CSimpAttr.lean): supported constant-equality replacement and the distinction between compilation and type-theoretic meaning.

\[^tasks\]: Lean, [pinned `Init/Core.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Core.lean): `Task`, `Task.get`, priorities, and `Task.spawn`; pure task semantics and the runtime-overridden representation.

\[^multithreading\]: Lean Language Reference, [Multi-Threaded Execution](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Multi-Threaded-Execution/): runtime task manager and links to the concurrent-programming interfaces. Moving explanatory documentation.

\[^decide\]: Lean, [pinned `Lean/Elab/Tactic/Decide.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Elab/Tactic/Decide.lean) and [native-proof infrastructure](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Meta/Native.lean): elaborator reduction, kernel checking, and native proof evaluation are distinct paths with different trust implications.

\[^trace\]: Lean, [pinned `Lean/Util/Trace.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Util/Trace.lean): `trace.profiler`, `trace.profiler.threshold`, heartbeat mode, and profile output. Diagnostic settings do not supply a native-application benchmark.

\[^precompile\]: Lean/Lake, [pinned `Lake/Config/LeanLibConfig.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/lake/Lake/Config/LeanLibConfig.lean): `precompileModules` default and shared-library loading for imported metaprograms.

\[^find-expr\]: Lean, [pinned `Lean/Util/FindExpr.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Util/FindExpr.lean): `Expr.find?`, `occurs`, and the separately scoped `findExt?` traversal.

\[^replace-expr\]: Lean, [pinned `Lean/Util/ReplaceExpr.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Lean/Util/ReplaceExpr.lean): `Expr.replace` and the explicitly uncached alternative `replaceNoCache`.

\[^replace-runtime\]: Lean, [pinned `kernel/replace_fn.cpp`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/kernel/replace_fn.cpp): `lean_replace_expr` and memoization for shared nodes. This is evidence for this visitor, not a universal cache-validity result for arbitrary metaprograms.

\[^list-lemmas\]: Lean, [pinned `Init/Data/List/Lemmas.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Data/List/Lemmas.lean): `List.reverse_reverse`, with its explicit list argument, and the surrounding reusable list equations.

\[^prelude\]: Lean, [pinned `Init/Prelude.lean`](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/Init/Prelude.lean): `Option.getD` documents its macro-inlined conditional default evaluation; the `List` documentation also distinguishes linked traversal and tail sharing from array update behavior.
