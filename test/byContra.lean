-- tests for byContra' tactic
import Mathlib.Tactic.ByContra

macro_rules
  | `(tactic| push_neg) => `(tactic| simp only [not_not])
  | `(tactic| push_neg at $e) => `(tactic| simp only [not_not, not_lt] at $e)

example (a b : ℕ) (foo : False)  : a < b := by
  by_contra';
--  guard_hyp this : b ≤ a; -- doesn't work for some reason? `this`?
  revert this; change b ≤ a → False; intro;
  exact foo

example (a b : ℕ) (h : False) : a < b := by
  by_contra' foo;
--  guard_hyp foo : b ≤ a; -- throws an error for some reason?
  revert foo; change b ≤ a → False; intro;
  exact h

  example (a b : ℕ) (h : False) : a < b := by
    by_contra' foo : ¬ a < b

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ P := by
  by_contra' foo : ¬ ¬ ¬ P; -- normalises to ¬ P, as does ¬ (goal).
  exact bar

example : 1 < 2 := by
  by_contra' : ¬ 2 < 1
