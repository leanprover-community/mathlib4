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

example {α β : Type} (f : β → α) {p q : β → Prop} :
    (∃ y b, p b ∧ f b = y ∧ q b) ↔ ∃ b, p b ∧ q b := by
  simp only [existsAndEq, true_and]

example {α β : Type} (f : β → α) {p q : β → Prop} :
    (∃ x b, p b ∧ (∃ c, f c = x) ∧ (∃ d, q d ∧ f d = x) ∧ q b) =
    ∃ b c, p b ∧ f c = f c ∧ (∃ d, q d ∧ f d = f c) ∧ q b := by
  simp only [existsAndEq]

example {α β : Type} (f : β → α) {p : α → Prop} :
    (∃ a, p a ∧ ∃ b, a = f b) ↔ ∃ b, p (f b) := by
  simp only [existsAndEq, and_true]

/--
error: simp made no progress
-/
#guard_msgs in
example {α : Type} : ∃ a : α, ∃ (b : α → α), b a = a := by
  simp only [existsAndEq]

-- lemmas like `Subtype.exists` and `Prod.exists` prevent `existsAndEq`
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
  simp only [Prod.exists, existsAndEq]

example {X Y : Type} (P Q : X × Y → Prop) (a : X × Y) :
    (∃ b : (X × Y), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp
