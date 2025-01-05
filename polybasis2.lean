import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent

-- variable (R : Type*) [CommRing R]

-- open Polynomial (X C)
--
-- noncomputable def XX : ℕ → ℤ[X]
--   | 0 => 1
--   | n + 1 => (X - C (n : ℤ) : ℤ[X]) * XX n
--
-- lemma deggg (n : ℕ) : Polynomial.degree (XX n) = n := by
--   induction n with
--   | zero =>
--     simp only [XX, Polynomial.degree_one, CharP.cast_eq_zero]
--   | succ n h =>
--     simp only [XX, h]
--     suffices (X - C (n : ℤ)).degree = 1 from by
--       rw [Polynomial.degree_mul, h, this]
--       simp only [Nat.cast_add, Nat.cast_one, add_comm]
--     conv_lhs =>
--       equals ((C (1 : ℤ)) * X + C (-(n : ℤ))).degree =>
--         congr
--         simp only [map_natCast, eq_intCast, Int.cast_one, one_mul, Int.cast_neg, Int.cast_natCast]
--         ring
--     simp only [Polynomial.degree_linear, ne_eq, one_ne_zero, not_false_eq_true]
--
-- lemma asdf : ∀ (n : ℕ), (X^n : ℤ[X]) ∈ Submodule.span ℤ[X] {XX k | k ∈ Finset.range (n + 1)} := by
--     intro n
--     induction n with
--     | zero => simp only [zero_add, Finset.range_one, Finset.mem_singleton, exists_eq_left, XX,
--       Set.setOf_eq_eq_singleton', Ideal.submodule_span_eq, Ideal.span_singleton_one, pow_zero,
--       Submodule.mem_top]
--     | succ n h =>
--       simp [XX] at *
--       sorry
--

open BigOperators
open Set (mem_univ univ)
open scoped Nat Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]

open Polynomial (X C)

noncomputable def XX (f : ℕ → R) (n : ℕ) := ∏ k ∈ Finset.range n, (X - C (f k))

lemma XX_inductive {f : ℕ → R} {n : ℕ} : XX f (n + 1) = (X - C (f n)) * XX f n := by
  rw [XX, Finset.prod_range_succ_comm, ←XX]

lemma XX_deg {f : ℕ → R} {n : ℕ} : (XX f n).degree = n := by
  induction n with
  | zero =>
    simp only [XX, Finset.range_zero, Finset.prod_empty, Polynomial.degree_one, CharP.cast_eq_zero]
  | succ n h =>
    rw [XX] at *
    conv_lhs =>
      congr
      equals (X - C (f n)) * (∏ k ∈ Finset.range n, (X - C (f k))) =>
        exact Finset.prod_range_succ_comm (fun x ↦ X - C (f x)) n
    rw [Polynomial.degree_mul, h]
    simp only [Polynomial.degree_X_sub_C, add_comm, Nat.cast_add, Nat.cast_one]

lemma XX_leading_coeff {f : ℕ → R} {n : ℕ} : (XX f n).leadingCoeff = 1 := by
  induction n with
    | zero =>
      simp only [XX, Finset.range_zero, Finset.prod_empty, Polynomial.monic_one,
        Polynomial.Monic.leadingCoeff]
    | succ n h =>
      rw [XX_inductive, Polynomial.leadingCoeff_mul, h]
      simp only [Polynomial.leadingCoeff_X_sub_C, mul_one]

lemma XX_span {f : ℕ → R} {n : ℕ} : X ^ n ∈ Submodule.span R {XX f k | k ≤ n} := by
  induction n using Nat.strongRec with
  | ind N h =>
    have : (X ^ N - XX f N).degree < ↑N := by
      have h0 : (XX f N).degree = ((X : R[X])^N).degree := by
        simp only [XX_deg, Polynomial.degree_pow, Polynomial.degree_X, nsmul_eq_mul, mul_one]
      have h1' : ((X : R[X]) ^ N) ≠ 0 := by
        simp only [ne_eq, pow_eq_zero_iff', Polynomial.X_ne_zero, false_and, not_false_eq_true]
      have h1 : XX f N ≠ 0 := by
        cases' N with n
        · simp only [XX, Finset.range_zero, Finset.prod_empty, ne_eq, one_ne_zero,
          not_false_eq_true]
        · have : 0 < (XX f (n + 1)).degree := by
            simp only [XX_deg, Nat.cast_add, Nat.cast_one]
            exact Nat.cast_add_one_pos n
          exact Polynomial.ne_zero_of_degree_gt (n := 0) this
      have h2 : (XX f N).leadingCoeff = ((X : R[X]) ^ N).leadingCoeff := by
        simp only [Polynomial.monic_X_pow, Polynomial.Monic.leadingCoeff, XX_leading_coeff]
      have h3 := Polynomial.degree_sub_lt h0.symm h1' h2.symm
      have h4 : (X ^ N - XX f N).degree < ↑N := by
        simp only [Polynomial.degree_pow, Polynomial.degree_X, nsmul_eq_mul, mul_one] at h3
        exact h3
      exact h4
    sorry -- Got that we have cancelled the top term after subtracting X^N

    -- simp only [nonpos_iff_eq_zero, XX, exists_eq_left, Finset.range_zero, Finset.prod_empty,
    -- Set.setOf_eq_eq_singleton', Ideal.submodule_span_eq, Ideal.span_singleton_one, pow_zero,
    -- Submodule.mem_top]

lemma XX_linear_indept {f : ℕ → R} {n : ℕ} : LinearIndependent R (XX f) := by sorry
  -- unfold LinearIndependent
  -- rw [Function.Injective]
  -- intro g1 g2 h
  -- ext x
  -- induction x using Nat.strongRec with
  -- | ind N h2 =>
  --   have := Polynomial.coeff_inj.mpr h
  --


