module

public import RegulaPolicy.Foundation
import all Init.Meta.Defs

/-! # Generated native-proof axiom names

On the pinned Lean 4.34.0, every proof by native evaluation goes through
`Lean.Meta.nativeEqTrue tacticName e` (`Lean/Meta/Native.lean`). After compiling and running `e`,
it adds an axiom `e = true` named `mkAuxDeclName (`_native ++ tacticName ++ `ax)`, and
`DeclNameGenerator.mkUniqueName` (`Lean/CoreM.lean`) turns that infix into
`namePrefix ++ infix` with each generator index appended by `Name.appendIndexAfter`. The
toolchain's tactics pass exactly three tactic names: `native_decide` and `decide +native` through
`evalDecideCore` (`Lean/Elab/Tactic/Decide.lean`), and `bv_decide` through
`LratCert.toReflectionProof` (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean`).

`nativeAxiomOrigin?` recognizes exactly the names that scheme generates for those tactics, and
`compilerTrustingAxiomName` is the single name-level compiler-trust classification.
`nativeAxiomOrigin?_sound` and `nativeAxiomOrigin?_nativeAxiomName` prove the two inclusions; the
second assumes `RuntimeStringAppend`, because `Name.appendIndexAfter` appends with the logically
opaque `String.Internal.append`. A recognized name is not an authorization: the generated-role
relation in `RoleSpecification` authenticates the actual axiom. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- A tactic of the pinned toolchain whose elaborator adds its axiom through
`Lean.Meta.nativeEqTrue`. Each constructor passes a distinct `tacticName`. -/
inductive NativeTactic where
  /-- `native_decide`: `evalNativeDecide` runs `evalDecideCore `native_decide`. -/
  | nativeDecide
  /-- `decide +native`: `evalDecide` runs `evalDecideCore `decide` with `native` set. -/
  | decideNative
  /-- `bv_decide`: `evalBvDecide` reaches `LratCert.toReflectionProof`, which passes
  `bv_decide`. -/
  | bvDecide
  deriving Repr, DecidableEq

namespace NativeTactic

/-- Every native tactic, in declaration order. -/
def all : List NativeTactic := [.nativeDecide, .decideNative, .bvDecide]

/-- The finite list is complete. -/
theorem mem_all (t : NativeTactic) : t ∈ all := by
  cases t <;> simp [all]

/-- An existential over the three tactics is decided by checking each one. -/
instance decidableExists (P : NativeTactic → Prop) [DecidablePred P] : Decidable (∃ t, P t) :=
  decidable_of_iff (∃ t ∈ all, P t) ⟨fun ⟨t, _, h⟩ => ⟨t, h⟩, fun ⟨t, h⟩ => ⟨t, mem_all t, h⟩⟩

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

/-- Lean's tactic elaborator that calls `nativeEqTrue` with this tactic's name. -/
def elaborator : NativeTactic → Name
  | .nativeDecide => `Lean.Elab.Tactic.evalNativeDecide
  | .decideNative => `Lean.Elab.Tactic.evalDecide
  | .bvDecide => `Lean.Elab.Tactic.BVDecide.evalBvDecide

/-- The syntax kind that elaborator is registered for. -/
def syntaxKind : NativeTactic → Name
  | .nativeDecide => `Lean.Parser.Tactic.nativeDecide
  | .decideNative => `Lean.Parser.Tactic.decide
  | .bvDecide => `Lean.Parser.Tactic.bvDecide

/-- The infixes of the auxiliary definitions the same tactic run adds and its axiom's statement
mentions: `bv_decide`'s reflected expression and certificate (`TacticContext.new` in
`Lean/Meta/Tactic/BVDecide/TacticContext.lean`). -/
def auxiliaryInfixes : NativeTactic → List String
  | .nativeDecide | .decideNative => []
  | .bvDecide => ["_expr_def", "_cert_def"]

end NativeTactic

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

end RegulaPolicy
