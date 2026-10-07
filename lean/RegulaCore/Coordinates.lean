import RegulaCore.Source
import Regula.Contract
import Regula.Decision

/-! # Transcript-coordinate admission

Transcript-coordinate admission: the check `Policy.admitScope` runs before inventory
admission. `CoordinateContract` names its obligations in traversal order and requires
refusal with the first unmet one; `checked_coordinates` proves it about the executed
`coordinateCheck` for every UTF-16 column function. The contract concerns the supplied
transcript bytes, coordinates and declaration ranges; it does not authenticate how a worker
acquired them. -/

namespace Regula.Checker.Frontend

open Lean hiding Command Declaration
open RegulaPolicy (Declaration)
open RegulaPolicy.Frontend (Command Transcript)

/-- An ordered check: the condition it requires and the refusal reported when it fails. -/
abbrev Obligation := Prop × String

/-- `e` is the refusal of the first unmet obligation. -/
def FirstUnmet : List Obligation → String → Prop
  | [], _ => False
  | o :: rest, e => (¬o.1 ∧ o.2 = e) ∨ (o.1 ∧ FirstUnmet rest e)

/-- `run` refuses exactly with the refusal of the first unmet obligation. -/
def Decides (run : Except String Unit) (obligations : List Obligation) : Prop :=
  ∀ e, run = .error e ↔ FirstUnmet obligations e

theorem firstUnmet_append (o₁ o₂ : List Obligation) (e : String) :
    FirstUnmet (o₁ ++ o₂) e ↔ FirstUnmet o₁ e ∨ ((∀ o ∈ o₁, o.1) ∧ FirstUnmet o₂ e) := by
  induction o₁ with
  | nil => simp [FirstUnmet]
  | cons o rest ih => by_cases h : o.1 <;> simp [FirstUnmet, h, ih]

theorem all_iff_not_firstUnmet (obligations : List Obligation) :
    (∀ o ∈ obligations, o.1) ↔ ∀ e, ¬FirstUnmet obligations e := by
  induction obligations with
  | nil => simp [FirstUnmet]
  | cons o rest ih =>
    constructor
    · intro hall e hf
      rcases hf with ⟨hn, _⟩ | ⟨_, hr⟩
      · exact hn (hall o List.mem_cons_self)
      · exact ih.mp (fun x hx => hall x (List.mem_cons_of_mem o hx)) e hr
    · intro hno x hx
      by_cases ho : o.1
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ho
        · exact ih.mpr (fun e hr => hno e (Or.inr ⟨ho, hr⟩)) x hx
      · exact (hno o.2 (Or.inl ⟨ho, rfl⟩)).elim

/-- A deciding check succeeds exactly when every obligation holds. -/
theorem Decides.ok_iff {run : Except String Unit} {obligations : List Obligation}
    (h : Decides run obligations) : run = .ok () ↔ ∀ o ∈ obligations, o.1 := by
  rw [all_iff_not_firstUnmet]
  cases run with
  | error e => exact ⟨fun hr => (by cases hr), fun hno => (hno e ((h e).mp rfl)).elim⟩
  | ok u => exact ⟨fun _ e he => (by cases (h e).mpr he), fun _ => rfl⟩

theorem decides_pure : Decides (pure ()) [] := fun e => by
  simp [FirstUnmet, pure, Except.pure]

theorem decides_guard (b : Bool) (p : Prop) (hp : b = true ↔ p) (msg : String) :
    Decides (unless b do throw msg) [(p, msg)] := fun e => by
  cases b <;> simp [← hp, FirstUnmet, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

theorem Decides.bind {x y : Except String Unit} {o₁ o₂ : List Obligation}
    (hx : Decides x o₁) (hy : Decides y o₂) : Decides (x >>= fun _ => y) (o₁ ++ o₂) := by
  intro e
  rw [firstUnmet_append]
  cases x with
  | error e' =>
    have hf := (hx e').mp rfl
    have hn : ¬∀ o ∈ o₁, o.1 := fun hall => (all_iff_not_firstUnmet o₁).mp hall e' hf
    simp only [Bind.bind, Except.bind, hn, false_and, or_false]
    exact hx e
  | ok u =>
    have hall := hx.ok_iff.mp rfl
    have hn : ¬FirstUnmet o₁ e := fun h => by cases (hx e).mpr h
    change y = .error e ↔ _
    rw [hy e]
    exact ⟨fun h => Or.inr ⟨hall, h⟩, fun h => h.elim (fun h => (hn h).elim) And.right⟩

theorem decides_forM {α : Type} (l : List α) (f : α → Except String Unit)
    (obligations : α → List Obligation) (h : ∀ x ∈ l, Decides (f x) (obligations x)) :
    Decides (l.forM f) (l.flatMap obligations) := by
  induction l with
  | nil => exact decides_pure
  | cons x rest ih =>
    rw [show (x :: rest).forM f = (f x >>= fun _ => rest.forM f) from rfl, List.flatMap_cons]
    exact (h x List.mem_cons_self).bind (ih fun y hy => h y (List.mem_cons_of_mem x hy))

theorem decides_forM_map {α : Type} (l : List α) (f : α → Except String Unit)
    (obligation : α → Obligation) (h : ∀ x ∈ l, Decides (f x) [obligation x]) :
    Decides (l.forM f) (l.map obligation) := by
  rw [List.map_eq_flatMap]
  exact decides_forM l f (fun x => [obligation x]) h

/-- A declaration's reported ranges agree with `snapshot` and name an admissible
source candidate. -/
def RangesConvert (column : Utf16Column) (snapshot : SourceSnapshot)
    (ranges : RegulaPolicy.Ranges) : Prop :=
  ReportedAgrees column snapshot.source.toFileMap ranges.range ∧
    ReportedAgrees column snapshot.source.toFileMap ranges.selectionRange ∧
    (reportedCandidate snapshot ranges).Valid

/-- The source snapshot a transcript records. -/
def snapshotOf (transcript : Transcript) : SourceSnapshot :=
  ⟨transcript.source, transcript.sourceContent⟩

/-- Required coordinate agreement: every command's `added` names are exactly its
`addedDeclarations` names, and the ranges of every declaration of the transcript's module
convert against its snapshot. -/
def CoordinatesAgree (column : Utf16Column) (declarations : Array Declaration)
    (transcript : Transcript) : Prop :=
  (∀ command ∈ transcript.commands,
    command.added = command.addedDeclarations.map (·.name)) ∧
  ∀ declaration ∈ declarations, declaration.module = transcript.module →
    ∀ ranges ∈ declaration.ranges, RangesConvert column (snapshotOf transcript) ranges

/-- One command's obligation: its declaration inventory. -/
def commandObligations (command : Command) : List Obligation :=
  [(command.added = command.addedDeclarations.map (·.name),
      "transcript declaration inventory mismatch")]

/-- One declaration's reported-range obligations: full range, selection range, then
source-candidate admission. -/
def reportObligations (column : Utf16Column) (snapshot : SourceSnapshot)
    (ranges : RegulaPolicy.Ranges) : List Obligation :=
  [(ReportedAgrees column snapshot.source.toFileMap ranges.range,
      "reported source coordinates disagree with the snapshot"),
    (ReportedAgrees column snapshot.source.toFileMap ranges.selectionRange,
      "reported source coordinates disagree with the snapshot"),
    ((reportedCandidate snapshot ranges).Valid, "invalid source coordinates")]

/-- Traversal order: every command's obligations in transcript order, then the
reported-range obligations of each same-module declaration in inventory order. -/
def coordinateObligations (column : Utf16Column) (declarations : Array Declaration)
    (transcript : Transcript) : List Obligation :=
  transcript.commands.toList.flatMap commandObligations ++
    declarations.toList.flatMap fun declaration =>
      if declaration.module = transcript.module then
        declaration.ranges.toList.flatMap (reportObligations column (snapshotOf transcript))
      else []

/-- Required coordinate check, for every UTF-16 column function: success exactly when
`CoordinatesAgree`, and refusal exactly with the first unmet obligation of
`coordinateObligations`. -/
def CoordinateContract
    (check : Utf16Column → Array Declaration → Transcript → Except String Unit) : Prop :=
  ∀ column declarations transcript,
    (check column declarations transcript = .ok () ↔
      CoordinatesAgree column declarations transcript) ∧
    Decides (check column declarations transcript)
      (coordinateObligations column declarations transcript)

/-- Checks that a command's `added` names equal the names of its `addedDeclarations`, in order. -/
def commandInventory (command : Command) : Except String Unit :=
  unless command.added == command.addedDeclarations.map (·.name) do
    throw "transcript declaration inventory mismatch"

/-- Recheck source coordinates against exact transcript bytes using Lean's `FileMap`. -/
@[regula_decision]
def coordinateCheck (column : Utf16Column) (declarations : Array Declaration)
    (transcript : Transcript) : Except String Unit := do
  transcript.commands.toList.forM commandInventory
  declarations.toList.forM fun declaration =>
    if declaration.module == transcript.module then
      declaration.ranges.toList.forM fun ranges =>
        (sourceFromReportWith column ⟨transcript.source, transcript.sourceContent⟩ ranges).map
          fun _ => ()
    else pure ()

theorem commandInventory_decides (command : Command) :
    Decides (commandInventory command) (commandObligations command) :=
  decides_guard (command.added == command.addedDeclarations.map (·.name))
    (command.added = command.addedDeclarations.map (·.name)) (by simp)
    "transcript declaration inventory mismatch"

theorem sourceFromReportWith_decides (column : Utf16Column) (snapshot : SourceSnapshot)
    (ranges : RegulaPolicy.Ranges) :
    Decides ((sourceFromReportWith column snapshot ranges).map fun _ => ())
      (reportObligations column snapshot ranges) := by
  intro e
  simp only [sourceFromReportWith, reportedRange_eq, reportObligations]
  by_cases h1 : ReportedAgrees column snapshot.source.toFileMap ranges.range <;>
  by_cases h2 : ReportedAgrees column snapshot.source.toFileMap ranges.selectionRange <;>
  by_cases h3 : (reportedCandidate snapshot ranges).Valid <;>
  simp_all [FirstUnmet, admitSource, reportedCandidate, Except.map, Bind.bind, Except.bind]

theorem coordinateCheck_decides (column : Utf16Column) (declarations : Array Declaration)
    (transcript : Transcript) :
    Decides (coordinateCheck column declarations transcript)
      (coordinateObligations column declarations transcript) := by
  refine (decides_forM _ _ _ fun command _ =>
    commandInventory_decides command).bind (decides_forM _ _ _ fun declaration _ => ?_)
  by_cases hm : declaration.module = transcript.module
  · simp only [beq_iff_eq, hm, ↓reduceIte]
    exact decides_forM _ _ _ fun ranges _ => sourceFromReportWith_decides column _ ranges
  · simp only [beq_iff_eq, hm, ↓reduceIte]
    exact decides_pure

theorem coordinateObligations_hold (column : Utf16Column) (declarations : Array Declaration)
    (transcript : Transcript) :
    (∀ o ∈ coordinateObligations column declarations transcript, o.1) ↔
      CoordinatesAgree column declarations transcript := by
  have ite_nil : ∀ (c : Prop) [Decidable c] (l : List Obligation),
      (∀ o ∈ (if c then l else []), o.1) ↔ (c → ∀ o ∈ l, o.1) := by
    intro c _ l
    by_cases hc : c <;> simp [hc]
  simp only [coordinateObligations, commandObligations, reportObligations,
    CoordinatesAgree, RangesConvert, ite_nil, List.forall_mem_append, List.forall_mem_flatMap,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, Array.mem_toList_iff, Option.mem_toList, Option.mem_def]

/-- Registers `CoordinateContract` about the executed coordinate check. -/
theorem checked_coordinates : Regula.ExecutableContract coordinateCheck CoordinateContract :=
  ⟨fun column declarations transcript =>
    ⟨(coordinateCheck_decides column declarations transcript).ok_iff.trans
        (coordinateObligations_hold column declarations transcript),
      coordinateCheck_decides column declarations transcript⟩⟩

/-- `coordinateCheck` accepts exactly the declarations and transcript whose coordinates agree
under the column function (`CoordinateContract`'s first clause): it accepts a transcript with no
command and no declaration, and refuses a command whose recorded names differ from its recorded
declarations. `checked_coordinates` registers the larger requirement, which also fixes the first
unmet obligation; this registration states the accepted set as a two-way decision. The column
function is an argument: that it is Lean's own UTF-16 conversion is the adapter's. -/
theorem checked_coordinateCheck : Regula.ExecutableContract coordinateCheck (fun check =>
    Regula.Decides (· = .ok ())
      (fun input : (Utf16Column × Array Declaration) × Transcript =>
        CoordinatesAgree input.1.1 input.1.2 input.2)
      (Function.uncurry (Function.uncurry check))) :=
  let transcript (commands : Array Command) : Transcript :=
    ⟨`Module, "", 0, "", "", "", #[], commands, #[], #[]⟩
  ⟨.of_iff (fun input => (checked_coordinates.evidence input.1.1 input.1.2 input.2).1)
    ⟨((fun _ _ => 0, #[]), transcript #[]),
      (checked_coordinates.evidence _ _ _).1.mpr ⟨by simp [transcript], by simp⟩⟩
    ⟨((fun _ _ => 0, #[]), transcript #[⟨#[`added], #[], false⟩]), fun accepted => by
      have agree := ((checked_coordinates.evidence _ _ _).1.mp accepted).1
        ⟨#[`added], #[], false⟩ (by simp [transcript])
      simp at agree⟩⟩

end Regula.Checker.Frontend
