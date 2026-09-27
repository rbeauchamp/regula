import Lean
import Regula.Collect
import Regula.Diagnostic
import RegulaCore.Screening
import Regula.Screen.Jev
import Regula.Screen.Questions

/-! # Claim reading and screening

Reading a claim from a loaded environment and screening it.

A claim's docstring is found by Lean's `findDocString?`; its clauses, explanation and any
discharge references come from the proved `RegulaPolicy.Screening` definitions. A clause that
ends with ``(discharged by `Name`)`` is formally discharged when `Name` is a theorem of the
loaded environment of type `S → P`, whose universe parameters are among the claim's, where
`S` is definitionally equal to the claim's statement by Lean's kernel definitional-equality
check (level parameters compared by name) and `P` does not depend on the hypothesis, whose
proof the kernel re-checks against that type here, and whose transitive
axioms lie within the Standard-Logical foundation (`propext`, `Quot.sound`,
`Classical.choice`). Then `Name` applied to the claim proves `P`, and only whether `P` states
the English clause is judged. The re-check covers only the discharge's own proof term; the
declarations it uses are trusted as admitted by the build of their imported `.olean` files and
are not re-checked here, so a dependency built under `debug.skipKernelTC` is not caught by the
screen (only Regula's fresh acceptance of a claimed surface re-admits it). A marker
that fails any of these conditions, or a clause that contains `(discharged by` but does not end
with a well-formed reference, leaves that clause a refused discharge, with the reason:
it is neither checked nor judged, and its claim escalates to review. It never downgrades to a
judged clause, and every other clause and claim is still screened. -/

namespace Regula.Screen

open Lean Meta
open RegulaPolicy.Screening
open Regula.Checker.Screening
open Questions

/-- A checked discharge: `proof` proves the claim implies `formal`, under exactly `axioms`. -/
structure Discharge where
  proof : Name
  formal : String
  axioms : List Name

/-- Axioms a discharge may use: the Standard-Logical foundation (standard §4.5). A project
axiom, `sorryAx`, or a compiler-trusting axiom (`Lean.ofReduceBool`, `Lean.trustCompiler`)
refuses the discharge. -/
def dischargeAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The outcome of checking one discharge reference. -/
inductive DischargeCheck where
  | admitted (d : Discharge)
  | refused (proof : Name) (reason : String)

/-- One claim as read from its environment. -/
structure ClaimInput where
  name : Name
  text : ClaimText
  /-- Per clause: no discharge marker, or the outcome of checking its reference. -/
  discharges : List (Option DischargeCheck)

/-- The claim's statement: a theorem's type, the body of a definition whose type is `Prop`
(calibration corpus items are such definitions), the proposition itself for a parameterless
`Prop`-valued inductive such as a structure of required contracts, otherwise the declaration's
type. -/
def statementExpr (info : ConstantInfo) : Expr :=
  match info with
  | .defnInfo d => if d.type.isProp then d.value else d.type
  | .inductInfo i =>
    if i.type.isProp && i.numParams == 0 then mkConst i.name (i.levelParams.map mkLevelParam)
    else i.type
  | _ => info.type

def pretty (e : Expr) : MetaM String := do
  return toString (← ppExpr e)

/-- The fields of a parameterless `Prop`-valued structure, in the shape of its Lean declaration
under `header`. The structure means exactly the conjunction of these field propositions. -/
def structureFields? (name : Name) (header : String) : MetaM (Option String) := do
  let some (.inductInfo i) := (← getEnv).find? name | return none
  unless i.type.isProp && i.numParams == 0 do return none
  let [ctor] := i.ctors | return none
  let some (.ctorInfo c) := (← getEnv).find? ctor | return none
  forallTelescope c.type fun fields _ => do
    let mut body : Format := .nil
    for field in fields do
      let decl ← field.fvarId!.getDecl
      body := body ++ .line ++ f!"{decl.userName} : {← ppExpr decl.type}"
    return some (toString (f!"structure {header} : Prop where" ++ .nest 2 body))

/-- The statement text sent for judgment: `statementExpr` pretty-printed, except that a
statement which is a parameterless `Prop`-valued structure also carries that structure's field
propositions, since its bare name states nothing. The claim's own name is never sent, so a
structure claim is rendered under the neutral name `Claim`. -/
def statementText (info : ConstantInfo) : MetaM String := do
  let statement := statementExpr info
  if let .const name _ := statement then
    if name == info.name then
      if let some fields ← structureFields? name "Claim" then return fields
    else if let some fields ← structureFields? name name.toString then
      return s!"{← pretty statement}\n\nwhere\n\n{fields}"
  pretty statement

/-- Check a discharge reference against the claim's statement, whose universe parameters are
`claimLevels`. -/
def checkDischarge (claimLevels : List Name) (claim : Expr) (proof : Name) : MetaM Discharge := do
  let some info := (← getEnv).find? proof
    | throwError "discharge {proof} is not a declaration of the loaded environment"
  let .thmInfo thm := info | throwError "discharge {proof} is not a theorem"
  if let some u := thm.levelParams.find? (!claimLevels.contains ·) then
    throwError "discharge {proof}'s universe parameter {u} is not one of the claim's"
  let .forallE _ hypothesis formal _ := thm.type
    | throwError "discharge {proof} is not an implication from the claim"
  if formal.hasLooseBVars then throwError "discharge {proof}'s conclusion depends on its hypothesis"
  match Kernel.isDefEq (← getEnv) {} hypothesis claim with
  | .ok true => pure ()
  | .ok false => throwError "discharge {proof}'s hypothesis is not definitionally equal to the claim's statement"
  | .error _ => throwError "the kernel could not compare discharge {proof}'s hypothesis with the claim"
  let copy := `_intentScreen.recheck ++ proof
  if (← getEnv).contains copy then throwError "discharge {proof}'s re-check name {copy} is taken"
  match (← getEnv).toKernelEnv.addDeclCore 0 0 (.thmDecl { thm with name := copy, all := [copy] }) none with
  | .ok _ => pure ()
  | .error e => throwError "the kernel rejected discharge {proof}'s proof: {← (e.toMessageData {}).toString}"
  let axioms := (← collectAxioms proof).toList.mergeSort (·.toString ≤ ·.toString)
  if let some a := axioms.find? (!dischargeAxioms.contains ·) then
    throwError "discharge {proof} depends on {a}, outside the Standard-Logical foundation"
  return ⟨proof, ← pretty formal, axioms⟩

/-- Read one declaration's intent clauses, explanation, statement and discharges. -/
def readClaim (name : Name) : MetaM ClaimInput := do
  let some info := (← getEnv).find? name | throwError "unknown declaration {name}"
  let some doc ← findDocString? (← getEnv) name | throwError "{name} has no docstring"
  let raw := intentClauses doc
  if raw.isEmpty then throwError "{name} has no nonempty Intent section clauses (RG5003)"
  let statement := statementExpr info
  let mut clauses := #[]
  let mut discharges := #[]
  for clause in raw do
    match discharge? clause with
    | some (english, proof) =>
      clauses := clauses.push english
      let check ← try pure (DischargeCheck.admitted (← checkDischarge info.levelParams statement proof.toName))
        catch e => pure (.refused proof.toName (← e.toMessageData.toString))
      discharges := discharges.push (some check)
    | none =>
      match dischargeMarked? clause with
      | some (english, reference) =>
        clauses := clauses.push english
        discharges := discharges.push (some (.refused (.mkSimple reference)
          "malformed discharge marker: a marked clause must end with (discharged by `Name`), where Name is nonempty and contains no whitespace or backtick"))
      | none =>
        clauses := clauses.push clause
        discharges := discharges.push none
  return { name, text := ⟨clauses.toList, RegulaPolicy.Screening.explanation doc, ← statementText info⟩,
           discharges := discharges.toList }

/-- Where a claim's findings are reported: its Lean declaration range in its module's source,
found on Lake's `LEAN_SRC_PATH`; without a range or a source file, its module, as
`Regula.Findings.declarationLocation` falls back. A range the source does not admit is an error. -/
def claimLocation (name : Name) : MetaM Regula.Location := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? name | throwError "{name} has no owning module"
  let moduleName := env.header.modules[idx.toNat]!.module
  let ranges? ← findDeclarationRanges? name
  let path? ← (← getSrcSearchPath).findModuleWithExt "lean" moduleName
  match ranges?, path? with
  | some ranges, some path =>
    let snapshot : Regula.SourceSnapshot := ⟨path.toString, ← IO.FS.readFile path⟩
    match Regula.sourceFromReport snapshot (Regula.Collect.rangesReport ranges) with
    | .ok source => return .source source
    | .error e => throwError "{name}'s declaration range does not match {path}: {e}"
  | _, _ => return .module moduleName

/-- Run a `MetaM` reader over a loaded environment. -/
def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<intent-screen>", fileMap := default, options := {} }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- Screening configuration. -/
structure Config where
  model : PinnedModel
  cache : System.FilePath
  mode : StateMode
  policy : Policy

/-- Accumulated service usage of a run. `requests` counts every POST sent, retries included.
`inputTokens` is unknown once any billed response omitted its usage. -/
structure Usage where
  requests : Nat := 0
  cached : Nat := 0
  inputTokens : Option Nat := some 0

def Usage.add (u : Usage) (r : Jev.Response) : Usage :=
  { requests := u.requests + r.attempts, cached := u.cached + (if r.cached then 1 else 0)
    inputTokens := if r.cached then u.inputTokens else do pure ((← u.inputTokens) + (← r.inputTokens)) }

/-- The billed input tokens, or `unknown`. -/
def Usage.tokensText (u : Usage) : String :=
  match u.inputTokens with
  | some n => toString n
  | none => "unknown"

def noulOf (r : Jev.Response) (id : String) : IO Probability := do
  match r.answers.lookup id with
  | some (.noul p) => return p
  | _ => throw <| IO.userError s!"no Noul answer for {id}"

/-- Support and confidence of the strength Choice. -/
def strengthOf (r : Jev.Response) : IO (Decimal × Decimal) := do
  match r.answers.lookup "strength" with
  | some (.choice ps confidence) =>
    let get (o : String) : IO Decimal := match ps.lookup o with
      | some p => pure p.val
      | none => throw <| IO.userError s!"strength answer lacks option {o}"
    return (strengthSupport (← get "equivalent") (← get "stronger"), confidence.val)
  | _ => throw <| IO.userError "no Choice answer for strength"

/-- Screen one claim: one request for the claim's judgments and one per discharged clause. -/
def screenClaim (cfg : Config) (input : ClaimInput) : StateT Usage IO ClaimScreen := do
  let questions := claimQuestions cfg.mode input.text fun i => (input.discharges[i]?.bind id).isSome
  let response ← Jev.ask cfg.cache cfg.model (state cfg.mode input.text) questions
  modify (·.add response)
  let judged (judgment : Judgment) (subject id : String) (support : Decimal)
      (confidence : Option Decimal) (digest : String) : Judged :=
    { judgment, subject, model := cfg.model, support, confidence, inputsDigest := digest
      question := questionText ((questions.lookup id).getD .null) }
  let mut clauses := #[]
  for ((clause, discharge), i) in (input.text.clauses.zip input.discharges).zipIdx do
    match discharge with
    | none =>
      let p ← noulOf response s!"coverage_{i}"
      clauses := clauses.push (clause, .judged (judged .coverage clause s!"coverage_{i}" p.val none response.digest))
    | some (.refused proof reason) => clauses := clauses.push (clause, .refused proof reason)
    | some (.admitted d) =>
      let q := [("correspondence", Questions.correspondence)]
      let r ← Jev.ask cfg.cache cfg.model (correspondenceState clause d.formal) q
      modify (·.add r)
      let p ← noulOf r "correspondence"
      clauses := clauses.push (clause, .discharged d.proof d.formal d.axioms
        { judgment := .correspondence, subject := clause, model := cfg.model, support := p.val
          confidence := none, inputsDigest := r.digest, question := questionText Questions.correspondence })
  let (support, confidence) ← strengthOf response
  let targeted ← targetedJudgments.mapM fun (id, j) => do
    let p ← noulOf response id
    pure (judged j "claim" id p.val none response.digest)
  return { claim := input.name, clauses := clauses.toList
           strength := judged .strength "claim" "strength" support (some confidence) response.digest
           targeted }

end Regula.Screen
