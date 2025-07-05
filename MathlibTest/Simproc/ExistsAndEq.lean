import Mathlib.Tactic.Simproc.ExistsAndEq

universe u
variable (α : Type u) (p q : α → Prop)

example (a : α) (hp : p a) (hq : q a) : ∃ b : α, (p b ∧ b = a) ∧ q b := by
  simp only [existsAndEq]
  guard_target = (p a ∧ True) ∧ q a
  exact ⟨⟨hp, trivial⟩, hq⟩

example (a : α) : ∃ b : α, b = a := by
  simp only [existsAndEq]

/--
error: simp made no progress
-/
#guard_msgs in
example (f : α → α) : ∃ a : α, a = f a := by
  simp only [existsAndEq]
  sorry

open Lean Meta Simp

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
example (a : α) (hp : p a) (hq : q a) : (∃ b : α, p b ∧ (∃ c : α, b = a ∧ q c)) := by
  -- the simproc doesn't handle nested `Exists`
  simp -failIfUnchanged only [existsAndEq]
  guard_target = ∃ b : α, p b ∧ (∃ c : α, b = a ∧ q c)
  simp only [exists_and_left]
  guard_target = ∃ b, p b ∧ b = a ∧ ∃ x, q x
  -- but can clean up the rest
  simp only [existsAndEq]
  guard_target = p a ∧ True ∧ ∃ x, q x
  exact ⟨hp, trivial, a, hq⟩
