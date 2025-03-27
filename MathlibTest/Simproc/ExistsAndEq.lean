import Mathlib.Tactic.Simproc.ExistsAndEq
import Mathlib.Tactic.Simproc.ExistsAndEqNested
-- import Mathlib.Algebra.Group.Even

universe u
variable (α : Type u) (p q : α → Prop)

example (a : α) (hp : p a) (hq : q a) : ∃ b : α, (p b ∧ b = a) ∧ q b := by
  simp only [existsAndEq]
  guard_target = (p a ∧ True) ∧ q a
  exact ⟨⟨hp, trivial⟩, hq⟩

example (a : α) : ∃ b : α, b = a := by
  simp only [existsAndEq]

open Lean Meta Simp

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

example {α β : Type} (f : β → α) {p q : β → Prop} :
    (∃ y b, p b ∧ f b = y ∧ q b) ↔ ∃ b, p b ∧ q b := by
  simp only [existsAndEqNested, true_and]

example {α β : Type} (f : β → α) {p q : β → Prop} :
    (∃ x b, p b ∧ (∃ c, f c = x) ∧ (∃ d, q d ∧ f d = x) ∧ q b) =
    ∃ b c, p b ∧ f c = f c ∧ (∃ d, q d ∧ f d = f c) ∧ q b := by
  simp only [existsAndEqNested]

example {α β : Type} (f : β → α) {p : α → Prop} :
    (∃ a, p a ∧ ∃ b, a = f b) ↔ ∃ b, p (f b) := by
  simp only [existsAndEqNested, and_true]

-- example : ∃ n : ℕ, Even n := by
--   unfold Even
  -- simp

example {α : Type} : ∃ a : α, ∃ (b : α → α), b a = a := by
  simp
