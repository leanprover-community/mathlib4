import Mathlib.Tactic.Simproc.ExistsAndEq
import Mathlib.Tactic.Simproc.ExistsAndEqNested

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

/--
error: simp made no progress
-/
#guard_msgs in
example {α : Type} : ∃ a : α, ∃ (b : α → α), b a = a := by
  simp only [existsAndEqNested]

-- lemmas like `Subtype.exists` and `Prod.exists` prevent `existsAndEqNested`
-- from working as a post simproc, so it is a pre simproc.
/--
error: unsolved goals
α : Type u
p q : α → Prop
X Y : Type
P Q : X × Y → Prop
a : X × Y
⊢ (∃ a_1 b, (P (a_1, b) ∧ (a_1, b) = a) ∧ Q (a_1, b)) ↔ P a ∧ Q a
-/
#guard_msgs in
example {X Y : Type} (P Q : X × Y → Prop) (a : X × Y) :
    (∃ b : (X × Y), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp only [Prod.exists, existsAndEqNested]

example {X Y : Type} (P Q : X × Y → Prop) (a : X × Y) :
    (∃ b : (X × Y), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp
