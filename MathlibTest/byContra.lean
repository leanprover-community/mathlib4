-- tests for by_contra! tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Rename
import Mathlib.Tactic.Set
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

example (a b : ℕ) (foo : False) : a < b := by
  by_contra!
  guard_hyp this : b ≤ a
  exact foo

example (a b : ℕ) (h : False) : a < b := by
  by_contra! foo
  revert foo; change b ≤ a → False; intro;
  exact h

example (a b : ℕ) (h : False) : a < b := by
  by_contra! foo : ¬ a < b -- can avoid push_neg
  guard_hyp foo : ¬ a < b
  exact h

example : 1 < 2 := by
  by_contra!
  guard_hyp this : 2 ≤ 1
  contradiction

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ p := by
  by_contra! foo : ¬ ¬ ¬ p -- normalises to ¬ p, as does ¬ (goal).
  guard_hyp foo : ¬ ¬ ¬ p
  exact bar

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ p := by
  by_contra! : ¬ ¬ ¬ p
  guard_hyp this : ¬ ¬ ¬ p
  exact bar

/--
error: Type mismatch
  h✝
has type
  b ≤ a
but is expected to have type
  a ≤ b
---
error: unsolved goals
a b : ℕ
this : a ≤ b
⊢ False
-/
#guard_msgs in
example (a b : ℕ) : a < b := by
  by_contra! : a ≤ b

example (P Q : Prop) (h' : False) : P ∧ Q := by
  fail_if_success by_contra! +fdsewfjdsk h
  by_contra! +distrib h
  guard_hyp h : ¬P ∨ ¬Q
  exact h'

section order

variable {α} [LinearOrder α] [One α] [Mul α]

example (x : α) (f : False) : x ≤ 1 := by
  set a := x * x
  by_contra! h
  guard_hyp h : 1 < x
  assumption

example (x : α) (f : False) : x ≤ 1 := by
  let _a := x * x
  by_contra! h
  guard_hyp h : 1 < x
  assumption

example (x : α) (f : False) : x ≤ 1 := by
  set a := x * x
  have : a ≤ a := le_rfl
  by_contra! h
  guard_hyp h : 1 < x
  assumption

end order

example (n : ℕ) (h : n ≠ 0) : n ≠ 0 := by
  by_contra! rfl
  simp only [Ne, not_true_eq_false] at h

example (p q : Prop) (hnp : ¬ p) : ¬ p ∨ ¬ q := by
  by_contra! ⟨hp, _⟩
  exact hnp hp

example (p q : Prop) (hnp : ¬ p) (hnq : ¬ q) : ¬ (p ∨ q) := by
  by_contra! hp | hq
  · exact hnp hp
  · exact hnq hq
