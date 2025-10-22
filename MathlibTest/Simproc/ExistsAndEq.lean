import Mathlib.Tactic.Simproc.ExistsAndEq

universe u v

variable (α : Type u) (β : Type v)

example (P Q : α → Prop) (a : α) (hp : P a) (hq : Q a) :
    ∃ b : α, (P b ∧ b = a) ∧ Q b := by
  simp only [existsAndEq]
  guard_target = (P a ∧ True) ∧ Q a
  exact ⟨⟨hp, trivial⟩, hq⟩

example (a : α) : ∃ b : α, b = a := by
  simp only [existsAndEq]

/--
error: `simp` made no progress
-/
#guard_msgs in
example (f : α → α) : ∃ a : α, a = f a := by
  simp only [existsAndEq]

/--
error: `simp` made no progress
-/
#guard_msgs in
example {β : α → Type v} (a : α) :
    ∃ x, ∃ y : β x, x = a := by
  simp only [existsAndEq]

example (f : β → α) {P Q : β → Prop} :
    (∃ y b, P b ∧ f b = y ∧ Q b) ↔ ∃ b, P b ∧ Q b := by
  simp only [existsAndEq, true_and]

example (f : β → α) {P Q : β → Prop} :
    (∃ x b, P b ∧ (∃ c, f c = x) ∧ (∃ d, Q d ∧ f d = x) ∧ Q b) =
    ∃ b c, P b ∧ f c = f c ∧ (∃ d, Q d ∧ f d = f c) ∧ Q b := by
  simp only [existsAndEq]

example (f : β → α) {P : α → Prop} :
    (∃ a, P a ∧ ∃ b, a = f b) ↔ ∃ b, P (f b) := by
  simp only [existsAndEq, and_true]

-- The simproc should not trigger on `a = a'` when `a'` depends on `a`
/--
error: `simp` made no progress
-/
#guard_msgs in
example {α : Type} : ∃ a : α, ∃ b : α → α, b a = a := by
  simp only [existsAndEq]

-- lemmas like `Subtype.exists` and `Prod.exists` prevent `existsAndEq`
-- from working as a post simproc, so it is a pre simproc.
/--
error: unsolved goals
α : Type u
β : Type v
P Q : α × β → Prop
a : α × β
⊢ (∃ a_1 b, (P (a_1, b) ∧ (a_1, b) = a) ∧ Q (a_1, b)) ↔ P a ∧ Q a
-/
#guard_msgs in
set_option linter.unusedSimpArgs false in
example (P Q : α × β → Prop) (a : α × β) :
    (∃ b : (α × β), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp only [Prod.exists, existsAndEq]

example (P Q : α × β → Prop) (a : α × β) :
    (∃ b : (α × β), (P b ∧ b = a) ∧ Q b) ↔ P a ∧ Q a := by
  simp
