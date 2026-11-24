module

public section

namespace Regula

universe u v w

structure ExecutableContract {α : Type u} (implementation : α)
    (condition : α → Prop) : Prop where
  evidence : condition implementation

@[expose, inline] def ExecutableContract.run {α : Type u} {implementation : α}
    {condition : α → Prop} (_ : ExecutableContract implementation condition) : α :=
  implementation

theorem ExecutableContract.run_eq {α : Type u} {implementation : α}
    {condition : α → Prop} (contract : ExecutableContract implementation condition) :
    contract.run = implementation := rfl

structure DecidesSoundly {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  sound : ∀ x, accepts (f x) → spec x
  accepted : ∃ x, accepts (f x)

structure DecidesCompletely {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  complete : ∀ x, spec x → accepts (f x)
  refused : ∃ x, ¬ accepts (f x)

structure Decides {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop
    extends DecidesSoundly accepts spec f, DecidesCompletely accepts spec f

structure DecisionEquivalence {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  iff : ∀ x, accepts (f x) ↔ spec x

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop} {f : α → ρ}

theorem Decides.iff (decides : Decides accepts spec f) (x : α) : accepts (f x) ↔ spec x :=
  ⟨decides.sound x, decides.complete x⟩

theorem Decides.of_iff (iff : ∀ x, accepts (f x) ↔ spec x) (accepted : ∃ x, accepts (f x))
    (refused : ∃ x, ¬ accepts (f x)) : Decides accepts spec f :=
  { sound := fun x => (iff x).mp, accepted, complete := fun x => (iff x).mpr, refused }

theorem Decides.toEquivalence (decides : Decides accepts spec f) :
    DecisionEquivalence accepts spec f :=
  ⟨decides.iff⟩

theorem DecisionEquivalence.sound (law : DecisionEquivalence accepts spec f) (x : α) :
    accepts (f x) → spec x :=
  (law.iff x).mp

theorem DecisionEquivalence.complete (law : DecisionEquivalence accepts spec f) (x : α) :
    spec x → accepts (f x) :=
  (law.iff x).mpr

theorem DecisionEquivalence.toSoundly (law : DecisionEquivalence accepts spec f)
    (accepted : ∃ x, accepts (f x)) : DecidesSoundly accepts spec f :=
  { sound := law.sound, accepted }

theorem DecisionEquivalence.toCompletely (law : DecisionEquivalence accepts spec f)
    (refused : ∃ x, ¬ accepts (f x)) : DecidesCompletely accepts spec f :=
  { complete := law.complete, refused }

theorem DecisionEquivalence.of_empty (empty : α → False) :
    DecisionEquivalence accepts spec f ∧ ¬ (∃ x, accepts (f x)) ∧ ¬ ∃ x, ¬ accepts (f x) :=
  ⟨⟨fun x => (empty x).elim⟩, fun ⟨x, _⟩ => empty x, fun ⟨x, _⟩ => empty x⟩

theorem Decides.of_roundtrip {β : Type u} {σ : Sort v} {write : β → σ} {parse : σ → Option β}
    (roundtrip : ∀ x, parse (write x) = some x)
    (canonical : ∀ s x, parse s = some x → write x = s)
    (value : β) {unwritten : σ} (refuses : parse unwritten = none) :
    Decides (·.isSome = true) (fun s => ∃ x, s = write x) parse :=
  { sound := fun s accepted => by
      cases h : parse s with
      | some x => exact ⟨x, (canonical s x h).symm⟩
      | none => rw [h] at accepted; exact absurd accepted Bool.false_ne_true
    accepted := ⟨write value, by rw [roundtrip]; rfl⟩
    complete := fun s ⟨x, written⟩ => by rw [written, roundtrip]; rfl
    refused := ⟨unwritten, by rw [refuses]; exact Bool.false_ne_true⟩ }

theorem DecidesSoundly.satisfiable (decides : DecidesSoundly accepts spec f) : ∃ x, spec x :=
  decides.accepted.elim fun x h => ⟨x, decides.sound x h⟩

theorem DecidesCompletely.refutable (decides : DecidesCompletely accepts spec f) :
    ∃ x, ¬ spec x :=
  decides.refused.elim fun x h => ⟨x, fun holds => h (decides.complete x holds)⟩

theorem DecidesSoundly.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x)) :
    ¬ DecidesSoundly accepts spec f :=
  fun decides => decides.accepted.elim refuses

theorem DecidesCompletely.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x))
    (satisfiable : ∃ x, spec x) : ¬ DecidesCompletely accepts spec f :=
  fun decides => satisfiable.elim fun x holds => refuses x (decides.complete x holds)

theorem DecidesCompletely.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x)) :
    ¬ DecidesCompletely accepts spec f :=
  fun decides => decides.refused.elim fun x h => h (acceptsAll x)

theorem DecidesSoundly.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x))
    (refutable : ∃ x, ¬ spec x) : ¬ DecidesSoundly accepts spec f :=
  fun decides => refutable.elim fun x fails => fails (decides.sound x (acceptsAll x))

end

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}

theorem Decides.not_of_constant (result : ρ) : ¬ Decides accepts spec (fun _ : α => result) :=
  fun decides => decides.accepted.elim fun _ accepted =>
    decides.refused.elim fun _ refused => refused accepted

theorem DecisionEquivalence.of_constant (result : ρ) :
    DecisionEquivalence accepts (fun _ : α => accepts result) (fun _ : α => result) :=
  ⟨fun _ => Iff.rfl⟩

theorem DecidesSoundly.spec_of_constant {result : ρ}
    (decides : DecidesSoundly accepts spec (fun _ : α => result)) (x : α) : spec x :=
  decides.accepted.elim fun _ accepted => decides.sound x accepted

theorem DecidesCompletely.not_spec_of_constant {result : ρ}
    (decides : DecidesCompletely accepts spec (fun _ : α => result)) (x : α) : ¬ spec x :=
  fun holds => decides.refused.elim fun _ refused => refused (decides.complete x holds)

end

section
variable {σ : Sort w} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {f : α → ρ} {fields : σ → α}

theorem DecidesSoundly.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesSoundly accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesSoundly accepts spec f :=
  { sound := fun x accepted => (covers x).elim fun s same =>
      same ▸ decides.sound s (same ▸ accepted)
    accepted := decides.accepted.elim fun s accepted => ⟨fields s, accepted⟩ }

theorem DecidesCompletely.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesCompletely accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesCompletely accepts spec f :=
  { complete := fun x holds => (covers x).elim fun s same =>
      same ▸ decides.complete s (same ▸ holds)
    refused := decides.refused.elim fun s refused => ⟨fields s, refused⟩ }

theorem Decides.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : Decides accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    Decides accepts spec f :=
  { toDecidesSoundly := .of_packing covers decides.toDecidesSoundly
    toDecidesCompletely := .of_packing covers decides.toDecidesCompletely }

end

theorem uncurry_eq_fields {α : Type u} {β : Type v} {φ : Sort w} (f : α → β → φ) :
    Function.uncurry f = fun p => f p.1 p.2 := rfl

theorem packing_uncurry_covers {σ : Type u} {α : Type v} {β : Type w} {fields : σ → α}
    (covers : ∀ x, ∃ s, fields s = x) : ∀ p : α × β, ∃ q : σ × β, (fields q.1, q.2) = p :=
  fun p => (covers p.1).elim fun s packed => ⟨(s, p.2), by rw [packed]⟩

section
variable {α : Sort u} {β : Sort w} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {g : α → β → ρ}

theorem DecidesSoundly.iff_slice (b : β) :
    DecidesSoundly (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesSoundly accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.sound, decides.accepted⟩,
    fun decides => ⟨decides.sound, decides.accepted⟩⟩

theorem DecidesCompletely.iff_slice (b : β) :
    DecidesCompletely (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesCompletely accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.complete, decides.refused⟩,
    fun decides => ⟨decides.complete, decides.refused⟩⟩

theorem Decides.iff_slice (b : β) :
    Decides (fun h : β → ρ => accepts (h b)) spec g ↔ Decides accepts spec (fun x => g x b) :=
  ⟨fun decides =>
      { toDecidesSoundly := (DecidesSoundly.iff_slice b).mp decides.toDecidesSoundly
        toDecidesCompletely := (DecidesCompletely.iff_slice b).mp decides.toDecidesCompletely },
    fun decides =>
      { toDecidesSoundly := (DecidesSoundly.iff_slice b).mpr decides.toDecidesSoundly
        toDecidesCompletely := (DecidesCompletely.iff_slice b).mpr decides.toDecidesCompletely }⟩

end

namespace Dependent

def isSome {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x)) (x : α) : Bool :=
  (f x).isSome

def isOk {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : Bool :=
  (f x).isOk

theorem isSome_eq_true_iff {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x))
    (x : α) : isSome f x = true ↔ ∃ value, f x = some value := by
  unfold isSome
  cases f x with
  | none => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | some value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

theorem isOk_eq_true_iff {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : isOk f x = true ↔ ∃ value, f x = .ok value := by
  unfold isOk
  cases f x with
  | error _ => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | ok value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

end Dependent

section
attribute [local simp] Except.toBool.eq_1 Except.toBool.eq_2 Function.uncurry.eq_1
  Dependent.isSome.eq_1 ExecutableContract.run.eq_1
end

end Regula
