import Mathlib.Tactic.Simproc.ExistsAndEq

universe u
variable (α : Type u) (p q : α → Prop)

example (a : α) (hp : p a) (hq : q a) : ∃ b : α, (p b ∧ b = a) ∧ q b := by
  simp only [existsAndEq, and_true]
  guard_target = p a ∧ q a
  exact ⟨hp, hq⟩

example (a : α) : ∃ b : α, b = a := by
  simp only [existsAndEq]

example (a : α) (hp : p a) (hq : q a) : (∃ b : α, p b ∧ (∃ c : α, b = a ∧ q c)) := by
  simp only [exists_and_left, existsAndEq, hp, true_and]
  guard_target = ∃ x, q x
  exact ⟨a, hq⟩
