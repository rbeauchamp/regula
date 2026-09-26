/-
External-consumer control (AC-08): a small fixture that only imports the
published `Audit` library and reasons about its declarations. The public
checker classifies the declarations introduced here and reports the exact
foundation labels — without adopting any general software process.

`#print axioms` confirms what the checker reports:
`Glossary.decay_monotone` depends on `propext`, `Classical.choice`, and
`Quot.sound` (Standard-Logical), because it is stated over `ℝ`.
-/
import Audit

theorem ext_decay_later_le (v : Glossary.DecayingValue) (h : v.decayRate < 0)
    (t₁ t₂ : Glossary.Time) (ht : t₁ ≤ t₂) : v.valueAt t₂ ≤ v.valueAt t₁ :=
  Glossary.decay_monotone v h t₁ t₂ ht

theorem ext_real_le_refl (x : ℝ) : x ≤ x := le_refl x
