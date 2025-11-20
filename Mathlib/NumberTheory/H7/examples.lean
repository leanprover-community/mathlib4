import Mathlib.Data.Real.Irrational
import Mathlib.NumberTheory.H7.h7faster

open Polynomial BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex AnalyticAt

lemma sqrt2sqrt_is_transcendental : Transcendental ℚ ((√2 : ℂ)^ (√2 : ℂ)) := by
  apply GelfondSchneiderSetup.gelfondSchneider √2 √2
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · refine IsAlgebraic.of_aeval ?_ (fun H ↦ ?_) ?_ ?_
    · exact Polynomial.X ^ 2 - Polynomial.C 1
    · have : ((((Polynomial.X ^ 2 - Polynomial.C 1) : ℚ[X])).natDegree : ℕ) = 2 := by {
        refine (degree_eq_iff_natDegree_eq_of_pos ?_).mp ?_
        · simp only [Nat.ofNat_pos]
        · rw [Polynomial.degree_sub_C]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
      }
      have HC : 2 ≠ 0 := by {simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]}
      apply HC
      rw [← this, ← H]
    · simp only [map_one, Nat.ofNat_pos, leadingCoeff_X_pow_sub_one,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · simp only [map_one, map_sub, map_pow, aeval_X]
      norm_cast
      rw [Real.sq_sqrt (x:=2)]
      · ring_nf
        exact isAlgebraic_one
      · positivity
  · simp only [ne_eq, ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
    not_false_eq_true, ofReal_eq_one, Real.sqrt_eq_one, OfNat.ofNat_ne_one, and_self]
  · have :=  irrational_sqrt_two
    unfold Irrational at this
    simp only [Set.mem_range, not_exists] at this
    intros i j
    let x : ℚ := (i : ℚ)/ (j : ℚ)
    intros H
    have := this x
    unfold x at this
    apply this
    symm
    norm_num
    norm_cast at H
    rw [H]
    simp_all only [Rat.cast_inj, forall_eq]
