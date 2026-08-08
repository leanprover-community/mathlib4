import Mathlib.Analysis.Polynomial.Sturm

open Polynomial

/-- info: Polynomial.sturmVariations (ps : List ℝ[X]) (x : ℝ) : ℕ -/
#guard_msgs in
#check Polynomial.sturmVariations

/-- info: Polynomial.IsQuasiSturmSequence (ps : List ℝ[X]) : Prop -/
#guard_msgs in
#check Polynomial.IsQuasiSturmSequence

/-- info: Polynomial.IsSturmSequence (p : ℝ[X]) (ps : List ℝ[X]) : Prop -/
#guard_msgs in
#check Polynomial.IsSturmSequence

/--
info: Polynomial.IsSturmSequence.count_roots_between {p : ℝ[X]} {ps : List ℝ[X]} (hss : p.IsSturmSequence ps) (hpne : p ≠ 0)
  (a b : ℝ) : a ≤ b → ↑(sturmVariations ps a) - ↑(sturmVariations ps b) = ↑{x | a < x ∧ x ≤ b ∧ eval x p = 0}.ncard
-/
#guard_msgs in
#check Polynomial.IsSturmSequence.count_roots_between

example (x : ℝ) : Polynomial.sturmVariations [] x = 0 := by simp

example (p : ℝ[X]) (x : ℝ) : Polynomial.sturmVariations [p] x = 0 := by simp
