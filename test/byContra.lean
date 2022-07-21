-- tests for byContra' tactic
import Mathlib.Tactic.ByContra

-- Basic implementation of `push_neg` to make it look like the tactic's working
macro_rules
  | `(tactic| push_neg) => `(tactic| simp only [not_not, not_lt])
  | `(tactic| push_neg at $e) => `(tactic| simp only [not_not, not_lt] at $e)

example (a b : ℕ) (foo : False)  : a < b := by
  by_contra';
--  guard_hyp this : b ≤ a; -- doesn't work for some reason? `this`?
  revert this; change b ≤ a → False; intro;
  exact foo

example (a b : ℕ) (h : False) : a < b := by
  by_contra' foo;
  revert foo; change b ≤ a → False; intro;
  exact h

  example (a b : ℕ) (h : False) : a < b := by
    by_contra' foo : ¬ a < b
    revert foo; change ¬ a < b → False; intro;
    exact h;

example : 1 < 2 := by
  by_contra'

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ P := by
  by_contra' foo : ¬ ¬ ¬ P; -- normalises to ¬ P, as does ¬ (goal).
  exact bar
