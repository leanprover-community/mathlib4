import Mathlib

open Real

--lemma sign_mul_abs
example (x : ℝ) : sign x * |x| = x := by
  unfold sign
  split_ifs with h h
  . suffices |x| = -x by linarith
    simp
    linarith
  . simp
    linarith
  . simp
    linarith

--lemma sign_mul
example (x y : ℝ) : (x * y).sign = x.sign * y.sign := by
  sorry
