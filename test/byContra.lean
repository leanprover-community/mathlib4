-- tests for byContra' tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Rename
import Mathlib.Data.Nat.Basic

example (a b : ℕ) (foo : False)  : a < b := by
  by_contra'
  guard_hyp this : b ≤ a
  exact foo

example (a b : ℕ) (h : False) : a < b := by
  by_contra' foo
  revert foo; change b ≤ a → False; intro;
  exact h

example (a b : ℕ) (h : False) : a < b := by
  by_contra' foo : ¬ a < b -- can avoid push_neg
  guard_hyp foo : ¬ a < b
  exact h

example : 1 < 2 := by
  by_contra'
  guard_hyp this : 2 ≤ 1
  contradiction

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ P := by
  by_contra' foo : ¬ ¬ ¬ P -- normalises to ¬ P, as does ¬ (goal).
  guard_hyp foo : ¬ ¬ ¬ P
  exact bar

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ P := by
  by_contra' : ¬ ¬ ¬ P
  guard_hyp this : ¬ ¬ ¬ P
  exact bar
