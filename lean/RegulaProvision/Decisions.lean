import RegulaProvision
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of local provisioning

The decision kind of each pure decision `RegulaProvision` runs, with its `@[regula_decision]`
registration. The provisioning program imports only the toolchain, because `scripts/provision.sh`
runs it with `lean --run` before the package is built. This second module of its library imports
it together with the two checker interfaces, and nothing the program runs imports this module.
Each kind restates a theorem of the program about the same definition, or for `component?`
follows from its definition, and adds the witnesses a kind requires. -/
namespace RegulaProvision

/-- One path component that is not hidden and has no separator, as a proposition stated with
Lean's own `String` functions: the text is not empty, it does not start with a period, and each
of its characters is a letter, a digit, `-`, `_` or `.`. `isComponent` decides it
(`isComponent_iff`). -/
def IsComponent (text : String) : Prop :=
  text.isEmpty = false ∧ text.startsWith "." = false ∧
    text.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') = true

/-- The executed test accepts exactly the path components. -/
theorem isComponent_iff (text : String) : isComponent text = true ↔ IsComponent text := by
  simp [isComponent, IsComponent, and_assoc]

/-- `component?` accepts exactly a path component (`IsComponent`): it accepts `a` and refuses the
empty text. That the admitted component is that text is in its definition, not in the kind. -/
theorem checked_component : Regula.ExecutableContract component?
    (Regula.Decides (·.isSome = true) IsComponent) :=
  have admitted (text : String) : (component? text).isSome = true ↔ IsComponent text := by
    rw [← isComponent_iff]
    by_cases passes : isComponent text = true <;> simp [component?, passes]
  ⟨.of_iff admitted
    ⟨"a", (admitted "a").mpr ((isComponent_iff "a").mp (by simp [isComponent]))⟩
    ⟨"", fun accepted =>
      absurd ((isComponent_iff "").mpr ((admitted "").mp accepted)) (by decide)⟩⟩

/-- What receipt admission establishes about the exact stable store and compatible pins. -/
def Admitted (receipt : Receipt) (mathlibRev githash : String) (pins : Array Pin) : Prop :=
  receipt.mathlibRev = mathlibRev ∧ receipt.leanGithash = githash ∧
    receipt.artifactPolicy = 0 ∧ receipt.source = "" ∧
    ∀ pin ∈ pins, ∀ held ∈ receipt.packages, held.name = pin.name → held.rev = pin.rev

/-- Admission is sound for its requested revisions and accepts a matching stable receipt. -/
theorem checked_admits : Regula.ExecutableContract @admits
    (fun (admission : Receipt → String → String → Array Pin → Bool) =>
    Regula.DecidesSoundly (· = true)
      (fun input : ((Receipt × String) × String) × Array Pin =>
        Admitted input.1.1.1 input.1.1.2 input.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry admission)))) :=
  ⟨{ sound := fun input accepted =>
       admits_sound input.1.1.1 input.1.1.2 input.1.2 input.2 accepted
     accepted := ⟨((({ schemaVersion := receiptSchema, mathlibRev := "", leanGithash := "", leanVersion := "", packages := #[] }, ""), ""), #[]),
       by simp [Function.uncurry, admits, receiptSchema]⟩ }⟩

/-- `mathlibStep` keeps the path exactly when it already links the shared checkout
(`mathlibStep_keep_iff`): it keeps a link to the target and does not keep an absent path. -/
theorem checked_mathlibStep : Regula.ExecutableContract mathlibStep (fun step =>
    Regula.Decides (· = Step.keep)
      (fun input : String × Observed => input.2 = .link input.1)
      (Function.uncurry step)) :=
  ⟨.of_iff (fun input => mathlibStep_keep_iff input.1 input.2)
    ⟨("", .link ""), (mathlibStep_keep_iff _ _).mpr rfl⟩
    ⟨("", .absent), fun accepted => nomatch (mathlibStep_keep_iff "" .absent).mp accepted⟩⟩

/-- `cloneStep` replaces only a link or a clean Git checkout (`cloneStep_replace`), and it
replaces a link. That it replaces every link and clean checkout is not claimed: a clean checkout
at the pinned revision is kept. -/
theorem checked_cloneStep : Regula.ExecutableContract cloneStep (fun step =>
    Regula.DecidesSoundly (· = Step.replace)
      (fun input : String × Observed =>
        (∃ resolved, input.2 = .link resolved) ∨ ∃ head, input.2 = .directory (some head) true)
      (Function.uncurry step)) :=
  ⟨{ sound := fun input replaced => cloneStep_replace input.1 input.2 replaced
     accepted := ⟨("", .link ""), rfl⟩ }⟩

/-- `found` identifies a directory as shared or being removed only when its receipt names it
(`found_identified`), and it identifies the directory named by a receipt's key. That it
identifies every directory a receipt names is not claimed. -/
theorem checked_found : Regula.ExecutableContract found (fun identify =>
    Regula.DecidesSoundly (· ≠ Found.foreign)
      (fun input : String × Option Receipt =>
        ∃ receipt, input.2 = some receipt ∧
          (input.1 = receipt.key ∨ input.1.startsWith (removingPrefix receipt.key) = true))
      (Function.uncurry identify)) :=
  ⟨{ sound := fun input identified => found_identified input.1 input.2 identified
     accepted := by
       let receipt : Receipt :=
         { schemaVersion := receiptSchema, mathlibRev := "", leanGithash := "", leanVersion := ""
           packages := #[] }
       exact ⟨(receipt.key, some receipt), by simp [Function.uncurry, found]⟩ }⟩

/-- `prunes` removes only a directory that is not the current one and that no registered copy
still links (`prunes_sound`), and it removes another directory with no registered copy. That it
removes every such directory is not claimed. -/
theorem checked_prunes : Regula.ExecutableContract prunes (fun removes =>
    Regula.DecidesSoundly (· = true)
      (fun input : (String × String) × Array (String × Bool) =>
        input.1.2 ≠ input.1.1 ∧ ∀ copy ∈ input.2, copy.2 = false)
      (Function.uncurry (Function.uncurry removes))) :=
  ⟨{ sound := fun input removed => prunes_sound input.1.1 input.1.2 input.2 removed
     accepted := ⟨(("current", "other"), #[]), by simp [Function.uncurry, prunes]⟩ }⟩

/-- The integration preflight accepts equal selectors and refuses different ones. -/
theorem checked_mathlibApplies : Regula.ExecutableContract mathlibApplies (fun applies =>
    Regula.Decides (· = true) (fun input : String × String => input.1 = input.2)
      (Function.uncurry applies)) :=
  ⟨.of_iff (fun input => mathlibApplies_iff input.1 input.2)
    ⟨("", ""), (mathlibApplies_iff _ _).mpr rfl⟩
    ⟨("a", "b"), fun accepted => by
      have same := (mathlibApplies_iff "a" "b").mp accepted
      simp at same⟩⟩

/-- `retires` removes exactly a registered link that still links its shared directory, is the
copy's retired link and is not the link the run provisions (`retires_iff`): it removes such a
link and keeps the link the run provisions. -/
theorem checked_retires : Regula.ExecutableContract retires (fun removes =>
    Regula.Decides (· = true)
      (fun input : ((String × String) × String) × Bool =>
        input.2 = true ∧ input.1.2 = input.1.1.2 ∧ input.1.2 ≠ input.1.1.1)
      (Function.uncurry (Function.uncurry (Function.uncurry removes)))) :=
  ⟨.of_iff (fun input => retires_iff input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨((("new", "old"), "old"), true),
      (retires_iff "new" "old" "old" true).mpr ⟨rfl, rfl, by decide⟩⟩
    ⟨((("new", "new"), "new"), true), fun accepted =>
      ((retires_iff "new" "new" "new" true).mp accepted).2.2 rfl⟩⟩

attribute [regula_decision]
  component? admits mathlibStep cloneStep found prunes retires mathlibApplies

end RegulaProvision
