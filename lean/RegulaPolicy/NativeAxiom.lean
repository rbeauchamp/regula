module

public import RegulaPolicy.Foundation
public import Lean.PrivateName
import all Init.Meta.Defs
import all Lean.PrivateName

/-! # Generated native-proof axiom names

On the pinned Lean 4.34.0, every proof by native evaluation goes through
`Lean.Meta.nativeEqTrue tacticName e` (`Lean/Meta/Native.lean`). After compiling and running `e`,
it adds an axiom `e = true` named `mkAuxDeclName (`_native ++ tacticName ++ `ax)`, and
`DeclNameGenerator.mkUniqueName` (`Lean/CoreM.lean`) turns that infix into
`namePrefix ++ infix` with each generator index appended by `Name.appendIndexAfter`, made private
to the module (`mkPrivateName`) while a `module` file elaborates without exporting.

The pinned sources (`src/lean`: `Init`, `Std`, `Lean` and `Lake`) call `nativeEqTrue` at exactly
two sites, which pass exactly three tactic names (`NativeTactic`), and every caller chain ends in
one of the eight tactic elaborators `NativeEvaluator` lists:
* `elabNativeDecideCore` (`Lean/Elab/Tactic/Decide.lean:59`), called only by `evalDecideCore`
  (`:82`), which is called only by `evalDecide` (`:186`, passing `decide`, reaching the call
  only with `+native`) and `evalNativeDecide` (`:190`, passing `native_decide`).
* `LratCert.toReflectionProof` (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39`, passing
  `bv_decide`), called only by `lratBitblaster` (`:100`) and `lratChecker` (`:115`).
  `lratBitblaster` is called only by `bvUnsat` (`Lean/Meta/Tactic/BVDecide/Main.lean:26`),
  through `bvDecide'` and `bvDecide` (`:42`, `:55`); `bvDecide` is called by
  `BVDecide.evalBvDecide` (`Lean/Elab/Tactic/BVDecide.lean:199`), `BVTrace.evalBvTrace` (`:161`)
  and `Grind.evalBvDecide` (`Lean/Elab/Tactic/Grind/BVDecide.lean:36`). `lratChecker` is called
  only by `BVCheck.bvCheck` (`Lean/Elab/Tactic/BVDecide.lean:122`), through `BVCheck.evalBvCheck`
  (`:124`). `BVTrace.evalBvTrace` is called by `BVDecide.evalBvTraceTactic` (`:213`) and
  `Grind.evalBvTrace` (`Lean/Elab/Tactic/Grind/BVDecide.lean:47`); `BVCheck.evalBvCheck` by
  `BVDecide.evalBvCheckTactic` (`Lean/Elab/Tactic/BVDecide.lean:233`) and `Grind.evalBvCheck`
  (`Lean/Elab/Tactic/Grind/BVDecide.lean:65`).

No term, command, conversion or `do`-element elaborator reaches either site. Five of the eight
elaborators are registered in Lean's tactic table (`builtin_tactic`) and three in `grind`'s
interactive-mode table (`builtin_grind_tactic`, `grindTacElabAttribute`,
`Lean/Elab/Tactic/Grind/Basic.lean:116`), which a `by` block enters only through `grind =>`
(`evalGrind`, `Lean/Elab/Tactic/Grind/Main.lean:342`) or `sym =>` (`evalSym`, `:351`). The only
toolchain macro that expands to one of these tactics is `trivial`, to `decide` without `+native`
(`Init/Tactics.lean:1494`), which adds no axiom.

`nativeAxiomOrigin?` recognizes exactly the names that scheme generates for those tactics, and
`compilerTrustingAxiomName` is the single name-level compiler-trust classification.
`nativeAxiomOrigin?_sound` and `nativeAxiomOrigin?_nativeAxiomName` prove the two inclusions; the
second assumes `RuntimeStringAppend`, because `Name.appendIndexAfter` appends with the logically
opaque `String.Internal.append`. `generatedPrefix_iff` proves that the names recognized under a
prefix related to a declaration by `GeneratedPrefix` are exactly those the generator gives that
declaration's native axioms in its own module, in either privacy mode. A recognized name is not
an authorization: the generated-role relation in `RoleSpecification` authenticates the actual
axiom. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- A `tacticName` the pinned toolchain passes to `Lean.Meta.nativeEqTrue`: the family of axiom
names one or more tactic evaluators (`NativeEvaluator`) generate. -/
inductive NativeTactic where
  /-- `native_decide`: `evalDecideCore `native_decide`. -/
  | nativeDecide
  /-- `decide +native`: `evalDecideCore `decide` with `native` set. -/
  | decideNative
  /-- `bv_decide`: `LratCert.toReflectionProof`, whichever `bv_decide` family tactic reached
  it. -/
  | bvDecide
  deriving Repr, DecidableEq

namespace NativeTactic

/-- Every native tactic, in declaration order. -/
def all : List NativeTactic := [.nativeDecide, .decideNative, .bvDecide]

/-- The one-component `tacticName` the pinned elaborator passes to `nativeEqTrue`. -/
def component : NativeTactic → String
  | .nativeDecide => "native_decide"
  | .decideNative => "decide"
  | .bvDecide => "bv_decide"

/-- The `tacticName` argument itself. -/
def tacticName (t : NativeTactic) : Name := .str .anonymous t.component

/-- The tactic whose `tacticName` is the one-component name `component`. -/
def ofComponent? (component : String) : Option NativeTactic :=
  all.find? (·.component == component)

/-- `ofComponent?` inverts `component`. -/
theorem ofComponent?_component (t : NativeTactic) : ofComponent? t.component = some t := by
  cases t <;> rfl

/-- The infixes of the auxiliary definitions the same tactic run adds and its axiom's statement
mentions: `bv_decide`'s reflected expression and certificate (`TacticContext.new` in
`Lean/Meta/Tactic/BVDecide/TacticContext.lean`). -/
def auxiliaryInfixes : NativeTactic → List String
  | .nativeDecide | .decideNative => []
  | .bvDecide => ["_expr_def", "_cert_def"]

end NativeTactic

/-- A tactic elaborator of the pinned toolchain that reaches a `nativeEqTrue` call site: all eight
such elaborators, registered for their syntax kind by `builtin_tactic` or, in `grind =>` and
`sym =>` mode, by `builtin_grind_tactic`. -/
inductive NativeEvaluator where
  /-- `native_decide`: `evalNativeDecide` (`Lean/Elab/Tactic/Decide.lean:190`). -/
  | nativeDecide
  /-- `decide +native`: `evalDecide` (`Lean/Elab/Tactic/Decide.lean:186`). -/
  | decideNative
  /-- `bv_decide`: `BVDecide.evalBvDecide` (`Lean/Elab/Tactic/BVDecide.lean:190`), through
  `bvDecide` and `lratBitblaster`. -/
  | bvDecide
  /-- `bv_decide?`: `BVDecide.evalBvTraceTactic` (`Lean/Elab/Tactic/BVDecide.lean:204`), through
  `BVTrace.evalBvTrace`, `bvDecide` and `lratBitblaster`. -/
  | bvTrace
  /-- `bv_check "file.lrat"`: `BVDecide.evalBvCheckTactic` (`Lean/Elab/Tactic/BVDecide.lean:225`),
  through `BVCheck.evalBvCheck` and `lratChecker`, with the certificate read from the file. -/
  | bvCheck
  /-- `bv_decide` in `grind =>` or `sym =>` mode: `Grind.evalBvDecide`
  (`Lean/Elab/Tactic/Grind/BVDecide.lean:28`), through `bvDecide` and `lratBitblaster`. -/
  | grindBvDecide
  /-- `bv_decide?` in that mode: `Grind.evalBvTrace` (`Lean/Elab/Tactic/Grind/BVDecide.lean:40`),
  through `BVTrace.evalBvTrace`, `bvDecide` and `lratBitblaster`. -/
  | grindBvTrace
  /-- `bv_check "file.lrat"` in that mode: `Grind.evalBvCheck`
  (`Lean/Elab/Tactic/Grind/BVDecide.lean:58`), through `BVCheck.evalBvCheck` and `lratChecker`. -/
  | grindBvCheck
  deriving Repr, DecidableEq

namespace NativeEvaluator

/-- Every native evaluator, in declaration order. -/
def all : List NativeEvaluator :=
  [.nativeDecide, .decideNative, .bvDecide, .bvTrace, .bvCheck, .grindBvDecide, .grindBvTrace,
    .grindBvCheck]

/-- The finite list is complete. -/
theorem mem_all (e : NativeEvaluator) : e ∈ all := by
  cases e <;> simp [all]

/-- An existential over the evaluators is decided by checking each one. -/
instance decidableExists (P : NativeEvaluator → Prop) [DecidablePred P] : Decidable (∃ e, P e) :=
  decidable_of_iff (∃ e ∈ all, P e) ⟨fun ⟨e, _, h⟩ => ⟨e, h⟩, fun ⟨e, h⟩ => ⟨e, mem_all e, h⟩⟩

/-- The `tacticName` this evaluator's call reaches `nativeEqTrue` with. -/
def family : NativeEvaluator → NativeTactic
  | .nativeDecide => .nativeDecide
  | .decideNative => .decideNative
  | .bvDecide | .bvTrace | .bvCheck | .grindBvDecide | .grindBvTrace | .grindBvCheck => .bvDecide

/-- Whether the elaborator is registered in `grind`'s interactive-mode table rather than Lean's
tactic table. -/
def grindMode : NativeEvaluator → Bool
  | .grindBvDecide | .grindBvTrace | .grindBvCheck => true
  | .nativeDecide | .decideNative | .bvDecide | .bvTrace | .bvCheck => false

/-- The elaborator's declaration name; the grind-mode elaborators are private to their module. -/
def elaborator : NativeEvaluator → Name
  | .nativeDecide => `Lean.Elab.Tactic.evalNativeDecide
  | .decideNative => `Lean.Elab.Tactic.evalDecide
  | .bvDecide => `Lean.Elab.Tactic.BVDecide.evalBvDecide
  | .bvTrace => `Lean.Elab.Tactic.BVDecide.evalBvTraceTactic
  | .bvCheck => `Lean.Elab.Tactic.BVDecide.evalBvCheckTactic
  | .grindBvDecide =>
      Lean.mkPrivateNameCore `Lean.Elab.Tactic.Grind.BVDecide `Lean.Elab.Tactic.Grind.evalBvDecide
  | .grindBvTrace =>
      Lean.mkPrivateNameCore `Lean.Elab.Tactic.Grind.BVDecide `Lean.Elab.Tactic.Grind.evalBvTrace
  | .grindBvCheck =>
      Lean.mkPrivateNameCore `Lean.Elab.Tactic.Grind.BVDecide `Lean.Elab.Tactic.Grind.evalBvCheck

/-- The syntax kind that elaborator is registered for. -/
def syntaxKind : NativeEvaluator → Name
  | .nativeDecide => `Lean.Parser.Tactic.nativeDecide
  | .decideNative => `Lean.Parser.Tactic.decide
  | .bvDecide => `Lean.Parser.Tactic.bvDecide
  | .bvTrace => `Lean.Parser.Tactic.bvTrace
  | .bvCheck => `Lean.Parser.Tactic.bvCheck
  | .grindBvDecide => `Lean.Parser.Tactic.Grind.bvDecide
  | .grindBvTrace => `Lean.Parser.Tactic.Grind.bvTrace
  | .grindBvCheck => `Lean.Parser.Tactic.Grind.bvCheck

end NativeEvaluator

/-- The name `mkAuxDeclName kind` gives under the name prefix `parent` with generator indices
`idxs`, before module privacy: `DeclNameGenerator.mkUniqueName.curr` on `parent ++ kind`. -/
def generatedName (parent kind : Name) (idxs : List Nat) : Name :=
  idxs.foldr (fun i n => n.appendIndexAfter i) (parent ++ kind)

/-- The name `nativeEqTrue` gives the axiom of tactic `t`: infix `_native ++ tacticName ++ ax`. -/
def nativeAxiomName (parent : Name) (t : NativeTactic) (idxs : List Nat) : Name :=
  generatedName parent (`_native ++ t.tacticName ++ `ax) idxs

/-- The generator states the recognizer covers: a declaration prefix without macro scopes, and
Lean's nonempty index list, each index at least 1 (`DeclNameGenerator` starts at 1 and only
increments). An anonymous or hygienic prefix has no ordinary owning declaration. -/
def NativeGenerated (parent : Name) (idxs : List Nat) : Prop :=
  parent ≠ .anonymous ∧ parent.hasMacroScopes = false ∧ idxs ≠ [] ∧ ∀ i ∈ idxs, 0 < i

instance (parent : Name) (idxs : List Nat) : Decidable (NativeGenerated parent idxs) := by
  unfold NativeGenerated; infer_instance

/-- The characters after `prefix`, when `chars` starts with it. -/
def stripPrefix : List Char → List Char → Option (List Char)
  | [], chars => some chars
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then stripPrefix ps cs else none

/-- Scan `_d…_d…` into its digit groups, the most recent group first. -/
def scanGroups : List Char → List (List Char) → Option (List (List Char))
  | [], groups => some groups
  | '_' :: rest, groups => scanGroups rest ([] :: groups)
  | c :: rest, group :: groups =>
      if c.isDigit then scanGroups rest ((group ++ [c]) :: groups) else none
  | _ :: _, [] => none

/-- The generator indices of a last name component `base_i…_i₁`, outermost index first: the
candidate list the recognizers check by regenerating the name. -/
def generatedIndices? (base suffix : String) : Option (List Nat) := do
  let rest ← stripPrefix base.toList suffix.toList
  (scanGroups rest []).map (·.map (Nat.ofDigitChars 10 · 0))

/-- The owning prefix and tactic of a name `nativeEqTrue`'s scheme generates for a native tactic,
recovered by parsing and then regenerating the name with Lean's own functions; otherwise
`none`. -/
def nativeAxiomOrigin? (n : Name) : Option (Name × NativeTactic) :=
  match n with
  | .str (.str (.str parent "_native") component) suffix => do
      let t ← NativeTactic.ofComponent? component
      let idxs ← generatedIndices? "ax" suffix
      if NativeGenerated parent idxs ∧ nativeAxiomName parent t idxs = n then
        some (parent, t)
      else none
  | _ => none

/-- The declaration prefix a generated native-proof axiom name belongs to. -/
def nativeParent? (n : Name) : Option Name := (nativeAxiomOrigin? n).map (·.1)

/-- The prefix of a name `mkAuxDeclName` generates for the one-component infix `kind`, checked by
regenerating it. Used to name a native tactic's auxiliary definitions independently of their
generator indices. -/
def generatedAuxParent? (kind : String) (n : Name) : Option Name :=
  match n with
  | .str parent suffix => do
      let idxs ← generatedIndices? kind suffix
      if NativeGenerated parent idxs ∧ generatedName parent (.str .anonymous kind) idxs = n then
        some parent
      else none
  | _ => none

/-- The last step of `DeclNameGenerator.mkUniqueName.curr` in module `m`: while a `module` file
elaborates without exporting (`hidden`), a name that is not already private becomes
`mkPrivateName env n = mkPrivateNameCore m (privateToUserName n)` (`Lean/Modifiers.lean`), with
`env.mainModule = m`; otherwise the name is unchanged. -/
def modulePrivacy (m : Name) (hidden : Bool) (n : Name) : Name :=
  if hidden && !Lean.isPrivateName n then Lean.mkPrivateNameCore m (Lean.privateToUserName n)
  else n

/-- `pfx` is the prefix Lean's generator gives the generated names of declaration `parent` of
module `m`: `parent` itself, or, for a public `parent` whose proof elaborates without exporting,
its private form in its own module, whose `privateToUserName` is `parent`. -/
def GeneratedPrefix (m parent pfx : Name) : Prop :=
  pfx = parent ∨ (Lean.isPrivateName parent = false ∧ pfx = Lean.mkPrivateNameCore m parent)

instance (m parent pfx : Name) : Decidable (GeneratedPrefix m parent pfx) := by
  unfold GeneratedPrefix; infer_instance

/-- Name-level compiler trust: one of Lean's three compiler axioms or a name the `nativeEqTrue`
scheme generates for a native tactic. The execution probe classifies by this definition; the
declaration policy additionally authenticates the generated axiom itself. -/
def compilerTrustingAxiomName (n : Name) : Bool :=
  builtinCompilerAxiom n || (nativeAxiomOrigin? n).isSome

/-- `n` is a name the `nativeEqTrue` scheme generates for a native tactic. -/
def GeneratedNativeAxiom (n : Name) : Prop :=
  ∃ parent t idxs, NativeGenerated parent idxs ∧ n = nativeAxiomName parent t idxs

/-- The trusted runtime behavior of Lean's extern `lean_string_append`: the logically opaque
`String.Internal.append` that `Name.appendIndexAfter` uses is concatenation. A hypothesis, never
an axiom: a kernel proof cannot evaluate a generated name without it. -/
def RuntimeStringAppend : Prop := ∀ a b : String, String.Internal.append a b = a ++ b

/-! ## Soundness: a recognized name is generated -/

/-- A recognized name is the scheme's name for exactly the recovered prefix and tactic. -/
theorem nativeAxiomOrigin?_sound {n parent : Name} {t : NativeTactic}
    (h : nativeAxiomOrigin? n = some (parent, t)) :
    ∃ idxs, NativeGenerated parent idxs ∧ n = nativeAxiomName parent t idxs := by
  unfold nativeAxiomOrigin? at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨t', _, idxs, _, h⟩ := h
    split at h
    · rename_i hg
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨idxs, hg.1, hg.2.symm⟩
    · simp at h
  · simp at h

/-- A recognized name has the three-component native tail. -/
theorem nativeAxiomOrigin?_shape {n parent : Name} {t : NativeTactic}
    (h : nativeAxiomOrigin? n = some (parent, t)) :
    ∃ component suffix, n = .str (.str (.str parent "_native") component) suffix := by
  unfold nativeAxiomOrigin? at h
  split at h
  · rename_i parent' component suffix
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨component, suffix, rfl⟩
    · simp at h
  · simp at h

/-! ## Completeness: every generated name is recognized -/

/-- The suffix string the indices produce after `ax`. -/
def indexSuffix (idxs : List Nat) : String :=
  idxs.foldr (fun i s => s ++ "_" ++ toString i) "ax"

/-- The `_d…` characters the indices append after `ax`, innermost index first. -/
def indexChars (idxs : List Nat) : List Char :=
  idxs.reverse.flatMap fun i => '_' :: Nat.toDigits 10 i

/-- Stripping a list from its own extension leaves the rest. -/
theorem stripPrefix_append (p rest : List Char) : stripPrefix p (p ++ rest) = some rest := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [stripPrefix, ih]

/-- A run of digits extends the current group. -/
theorem scanGroups_digits (ds rest group : List Char) (groups : List (List Char))
    (h : ∀ c ∈ ds, c.isDigit = true) :
    scanGroups (ds ++ rest) (group :: groups) = scanGroups rest ((group ++ ds) :: groups) := by
  induction ds generalizing group with
  | nil => simp
  | cons c ds ih =>
    have hc : c.isDigit = true := h c (by simp)
    have hu : c ≠ '_' := by rintro rfl; simp [Char.isDigit] at hc
    rw [List.cons_append, scanGroups.eq_3 _ _ _ _ hu]
    simp only [hc, ↓reduceIte]
    rw [ih _ (fun c hc => h c (by simp [hc]))]
    simp

/-- Rendered index groups scan back to their digit lists, most recent first. -/
theorem scanGroups_flatMap (l : List Nat) (rest : List Char) (groups : List (List Char)) :
    scanGroups ((l.flatMap fun i => '_' :: Nat.toDigits 10 i) ++ rest) groups =
      scanGroups rest ((l.reverse.map (Nat.toDigits 10)) ++ groups) := by
  induction l generalizing groups with
  | nil => simp
  | cons i l ih =>
    rw [List.flatMap_cons, List.append_assoc, List.cons_append, scanGroups.eq_2,
      scanGroups_digits _ _ _ _
        (fun _ hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc), ih]
    simp

/-- The characters of `indexSuffix`. -/
theorem toList_indexSuffix (idxs : List Nat) :
    (indexSuffix idxs).toList = 'a' :: 'x' :: indexChars idxs := by
  induction idxs with
  | nil => rfl
  | cons i idxs ih =>
    simp only [indexSuffix, List.foldr_cons] at ih ⊢
    rw [String.toList_append, String.toList_append, ih]
    simp [indexChars, Nat.toString_eq_repr, Nat.toList_repr]

/-- The indices are recovered from the suffix they generate. -/
theorem generatedIndices?_indexSuffix (idxs : List Nat) :
    generatedIndices? "ax" (indexSuffix idxs) = some idxs := by
  have hs : stripPrefix "ax".toList (indexSuffix idxs).toList = some (indexChars idxs) := by
    rw [toList_indexSuffix]
    exact stripPrefix_append ['a', 'x'] _
  have := scanGroups_flatMap idxs.reverse [] []
  simp only [List.append_nil, List.reverse_reverse] at this
  simp only [generatedIndices?, hs, Option.bind_eq_bind, Option.bind_some, indexChars, this,
    scanGroups.eq_1, Option.map_some, List.map_map]
  simp [Function.comp_def, Nat.ofDigitChars_ten_toDigits]

/-- A generated suffix is never the macro-scope marker `_hyg`. -/
theorem indexSuffix_ne_hyg (idxs : List Nat) : (indexSuffix idxs == "_hyg") = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg String.toList h
  rw [toList_indexSuffix] at this
  simp at this

/-- Under `RuntimeStringAppend`, the scheme's name has the three-component native tail with the
index suffix `ax_…`. -/
theorem nativeAxiomName_eq (hAppend : RuntimeStringAppend) (parent : Name) (t : NativeTactic)
    (idxs : List Nat) (hp : parent.hasMacroScopes = false) :
    nativeAxiomName parent t idxs =
      .str (.str (.str parent "_native") t.component) (indexSuffix idxs) := by
  induction idxs with
  | nil =>
    cases t <;>
      simp [nativeAxiomName, generatedName, NativeTactic.tacticName, NativeTactic.component,
        indexSuffix, HAppend.hAppend, Append.append, Name.append, hp] <;> rfl
  | cons i idxs ih =>
    have append : ∀ a b : String, String.Internal.append a b = a ++ b := hAppend
    simp only [nativeAxiomName, generatedName, List.foldr_cons] at ih ⊢
    rw [ih]
    simp only [Name.appendIndexAfter, Name.modifyBase, Name.hasMacroScopes, indexSuffix_ne_hyg,
      Bool.false_eq_true, ↓reduceIte, Name.mkStr, append]
    rfl

/-- Every name the scheme generates for a native tactic is recognized, with its own prefix and
tactic. -/
theorem nativeAxiomOrigin?_nativeAxiomName (hAppend : RuntimeStringAppend) {parent : Name}
    {t : NativeTactic} {idxs : List Nat} (h : NativeGenerated parent idxs) :
    nativeAxiomOrigin? (nativeAxiomName parent t idxs) = some (parent, t) := by
  have hn := nativeAxiomName_eq hAppend parent t idxs h.2.1
  unfold nativeAxiomOrigin?
  generalize hN : nativeAxiomName parent t idxs = N
  rw [hn] at hN
  subst hN
  simp only [NativeTactic.ofComponent?_component, generatedIndices?_indexSuffix,
    Option.bind_eq_bind, Option.bind_some, hn, h, and_self, ↓reduceIte]

/-- Recognition is exactly the generated set. -/
theorem nativeAxiomOrigin?_isSome_iff (hAppend : RuntimeStringAppend) (n : Name) :
    (nativeAxiomOrigin? n).isSome = true ↔ GeneratedNativeAxiom n := by
  constructor
  · intro h
    obtain ⟨⟨parent, t⟩, ho⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨idxs, hg, rfl⟩ := nativeAxiomOrigin?_sound ho
    exact ⟨parent, t, idxs, hg, rfl⟩
  · rintro ⟨parent, t, idxs, hg, rfl⟩
    rw [nativeAxiomOrigin?_nativeAxiomName hAppend hg]
    rfl

/-- Every name classified compiler-trusting is one of Lean's three compiler axioms or generated
by the `nativeEqTrue` scheme for a native tactic. -/
theorem compilerTrustingAxiomName_sound {n : Name} (h : compilerTrustingAxiomName n = true) :
    builtinCompilerAxiom n = true ∨ GeneratedNativeAxiom n := by
  unfold compilerTrustingAxiomName at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl h
  · obtain ⟨⟨parent, t⟩, ho⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨idxs, hg, rfl⟩ := nativeAxiomOrigin?_sound ho
    exact Or.inr ⟨parent, t, idxs, hg, rfl⟩

/-- Every name the `nativeEqTrue` scheme generates for a native tactic, and each of Lean's three
compiler axioms, classifies as compiler-trusting, and no other name does. -/
theorem compilerTrustingAxiomName_iff (hAppend : RuntimeStringAppend) (n : Name) :
    compilerTrustingAxiomName n = true ↔
      builtinCompilerAxiom n = true ∨ GeneratedNativeAxiom n := by
  refine ⟨compilerTrustingAxiomName_sound, ?_⟩
  rintro (h | h)
  · simp [compilerTrustingAxiomName, h]
  · simp [compilerTrustingAxiomName, (nativeAxiomOrigin?_isSome_iff hAppend n).mpr h]

/-! ## Module privacy: the prefix of a declaration's generated names -/

/-- Appending names without macro scopes adds none. -/
theorem appendCore_hasMacroScopes {a b : Name} (ha : a.hasMacroScopes = false)
    (hb : b.hasMacroScopes = false) : (a.appendCore b).hasMacroScopes = false := by
  induction b with
  | anonymous => exact ha
  | str p s _ => exact hb
  | num p d ih => exact ih hb

/-- The private prefix `_private.m.0` of a module without macro scopes has none. -/
theorem privatePrefix_hasMacroScopes {m : Name} (hm : m.hasMacroScopes = false) :
    (Name.mkNum (Lean.privateHeader ++ m) 0).hasMacroScopes = false := by
  change (Name.append Lean.privateHeader m).hasMacroScopes = false
  unfold Name.append
  rw [hm]
  exact appendCore_hasMacroScopes rfl hm

/-- Without macro scopes, `mkPrivateNameCore` appends the private prefix structurally. -/
theorem mkPrivateNameCore_eq {m n : Name} (hm : m.hasMacroScopes = false)
    (hn : n.hasMacroScopes = false) :
    Lean.mkPrivateNameCore m n = (Name.mkNum (Lean.privateHeader ++ m) 0).appendCore n := by
  change Name.append _ n = _
  unfold Name.append
  rw [privatePrefix_hasMacroScopes hm, hn]

/-- A generated name is private exactly when its prefix is. -/
theorem isPrivateName_nativeTail (parent : Name) (component suffix : String) :
    Lean.isPrivateName (.str (.str (.str parent "_native") component) suffix) =
      Lean.isPrivateName parent := by
  simp [Lean.isPrivateName, Lean.privateHeader, BEq.beq, Name.beq]

/-- A generated name's private form is the generated name of the private prefix. -/
theorem modulePrivacy_nativeAxiomName (hAppend : RuntimeStringAppend) {m parent : Name}
    (hm : m.hasMacroScopes = false) (hs : parent.hasMacroScopes = false) (hidden : Bool)
    (t : NativeTactic) (idxs : List Nat) :
    modulePrivacy m hidden (nativeAxiomName parent t idxs) =
      nativeAxiomName (modulePrivacy m hidden parent) t idxs := by
  have hP := appendCore_hasMacroScopes (privatePrefix_hasMacroScopes hm) hs
  rw [nativeAxiomName_eq hAppend parent t idxs hs]
  unfold modulePrivacy
  rw [isPrivateName_nativeTail]
  by_cases hv : (hidden && !Lean.isPrivateName parent) = true
  · simp only [hv, ↓reduceIte, Lean.privateToUserName]
    have hnp : Lean.isPrivateName parent = false := by simp_all
    simp only [isPrivateName_nativeTail, hnp, Bool.false_eq_true, ↓reduceIte]
    rw [mkPrivateNameCore_eq hm (by simp [Name.hasMacroScopes, indexSuffix_ne_hyg]),
      mkPrivateNameCore_eq hm hs, nativeAxiomName_eq hAppend _ t idxs hP]
    rfl
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    rw [nativeAxiomName_eq hAppend parent t idxs hs]

/-- The private form of an ordinary declaration name is again an ordinary generated prefix. -/
theorem nativeGenerated_modulePrivacy {m parent : Name} {idxs : List Nat}
    (hm : m.hasMacroScopes = false) (h : NativeGenerated parent idxs) (hidden : Bool) :
    NativeGenerated (modulePrivacy m hidden parent) idxs := by
  unfold modulePrivacy
  split
  · rename_i hv
    have hnp : Lean.isPrivateName parent = false := by simp_all
    simp only [Lean.privateToUserName, hnp, Bool.false_eq_true, ↓reduceIte]
    rw [mkPrivateNameCore_eq hm h.2.1]
    refine ⟨?_, appendCore_hasMacroScopes (privatePrefix_hasMacroScopes hm) h.2.1, h.2.2⟩
    cases parent with
    | anonymous => exact absurd rfl h.1
    | str p s => simp [Name.appendCore]
    | num p d => simp [Name.appendCore]
  · exact h

/-- Soundness and completeness of the prefix relation: for an ordinary declaration `parent` of
module `m`, the names the recognizer assigns to `parent` through `GeneratedPrefix` are exactly
those `DeclNameGenerator.mkUniqueName.curr` gives the native axioms of its proofs, in either
privacy mode. -/
theorem generatedPrefix_iff (hAppend : RuntimeStringAppend) {m parent : Name}
    (hm : m.hasMacroScopes = false) (hp : parent ≠ .anonymous)
    (hs : parent.hasMacroScopes = false) (n : Name) (t : NativeTactic) :
    (∃ pfx, nativeAxiomOrigin? n = some (pfx, t) ∧ GeneratedPrefix m parent pfx) ↔
      ∃ hidden idxs, idxs ≠ [] ∧ (∀ i ∈ idxs, 0 < i) ∧
        n = modulePrivacy m hidden (nativeAxiomName parent t idxs) := by
  constructor
  · rintro ⟨pfx, ho, hpfx⟩
    obtain ⟨idxs, hg, rfl⟩ := nativeAxiomOrigin?_sound ho
    rcases hpfx with rfl | ⟨hnp, rfl⟩
    · exact ⟨false, idxs, hg.2.2.1, hg.2.2.2, by simp [modulePrivacy]⟩
    · refine ⟨true, idxs, hg.2.2.1, hg.2.2.2, ?_⟩
      rw [modulePrivacy_nativeAxiomName hAppend hm hs]
      simp [modulePrivacy, hnp, Lean.privateToUserName]
  · rintro ⟨hidden, idxs, hne, hpos, rfl⟩
    have hg : NativeGenerated parent idxs := ⟨hp, hs, hne, hpos⟩
    refine ⟨modulePrivacy m hidden parent, ?_, ?_⟩
    · rw [modulePrivacy_nativeAxiomName hAppend hm hs]
      exact nativeAxiomOrigin?_nativeAxiomName hAppend (nativeGenerated_modulePrivacy hm hg hidden)
    · unfold modulePrivacy GeneratedPrefix
      split
      · rename_i hv
        have hnp : Lean.isPrivateName parent = false := by simp_all
        simp [hnp, Lean.privateToUserName]
      · exact Or.inl rfl

end RegulaPolicy
