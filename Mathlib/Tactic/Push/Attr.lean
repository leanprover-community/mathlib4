import Mathlib.Tactic.PushNeg

namespace Mathlib.Tactic.Push

variable (p q : Prop) {α : Sort*} {β : Type*} (s : α → Prop)

attribute [push] not_not not_or Classical.not_imp not_le not_lt
  not_finite_iff_infinite not_infinite_iff_finite Set.not_infinite

@[push] theorem not_iff : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

@[push] theorem not_nonempty_eq (s : Set β) : (¬s.Nonempty) ↔ (s = ∅) := by
  have A : ∀ (x : β), ¬(x ∈ (∅ : Set β)) := fun x ↦ id
  simp only [Set.Nonempty, not_exists]
  exact ⟨fun h ↦ Set.ext (fun x ↦ by simp only [h x, false_iff, A]), fun h ↦ by rwa [h]⟩

@[push] theorem ne_empty_eq_nonempty (s : Set β) : (s ≠ ∅) = s.Nonempty := by
  rw [ne_eq, ← not_nonempty_eq s, not_not]

@[push] theorem empty_ne_eq_nonempty (s : Set β) : (∅ ≠ s) = s.Nonempty := by
  rw [ne_comm, ne_empty_eq_nonempty]

@[push] theorem Set.not_finite_eq_infinite (s : Set β) : (¬Set.Finite s) ↔ Set.Infinite s := by rfl

end Mathlib.Tactic.Push
