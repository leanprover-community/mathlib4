-- tests for byContra' tactic
import Mathlib.Tactic.ByContra

-- Basic implementation of `push_neg` to make it look like the tactic's working
-- This needs to be removed when `push_neg` is actually implemented.
macro_rules
  | `(tactic| push_neg) => `(tactic| simp only [not_not, not_lt])
  | `(tactic| push_neg at $e) => `(tactic| simp only [not_not, not_lt] at $e)

example (a b : ℕ) (foo : False)  : a < b := by
  by_contra';
--  guard_hyp this : b ≤ a; -- doesn't work for some reason?
  revert this; change b ≤ a → False; intro; -- evidence it worked
  exact foo

example (a b : ℕ) (h : False) : a < b := by
  by_contra' foo;
  revert foo; change b ≤ a → False; intro;
  exact h

  example (a b : ℕ) (h : False) : a < b := by
    by_contra' foo : ¬ a < b -- can avoid push_neg
    revert foo; change ¬ a < b → False; intro;
    exact h;

example : 1 < 2 := by
  by_contra'

example (p : Prop) (bar : False) : ¬ ¬ ¬ ¬ ¬ ¬ P := by
  by_contra' foo : ¬ ¬ ¬ P; -- normalises to ¬ P, as does ¬ (goal).
  exact bar
