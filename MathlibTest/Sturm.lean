import Mathlib.Analysis.Polynomial.Sturm

open Polynomial

#check Polynomial.sturmVariations
#check Polynomial.IsQuasiSturmSequence
#check Polynomial.IsSturmSequence
#check Polynomial.IsSturmSequence.count_roots_between

example (x : ℝ) : Polynomial.sturmVariations [] x = 0 := by simp

example (p : ℝ[X]) (x : ℝ) : Polynomial.sturmVariations [p] x = 0 := by simp
