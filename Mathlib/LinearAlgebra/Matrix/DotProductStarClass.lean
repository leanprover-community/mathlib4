/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Data.IsROrC.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Types with Star Inner Product such that (star v) ⬝ᵥ v = 0 ↔ v = 0

This file defines DotProductInnerProductSpace in which the star operation on a vector makes the star
dotProduct (in 1st arg) is zero if and only if the vector is zero. This makes star operation for
matrices of the same underlying type kernel preserving for linear maps.
-/

open BigOperators Matrix

class DotProductInnerProductSpace (n K) [Fintype n][Ring K][StarRing K] : Prop where
  dotProduct_star_self_eq_zero_iff (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔ v = 0

variable {n : Type _}[Fintype n]

lemma dotProduct_self_star_eq_zero  (v : n → K) [Ring K] [StarRing K]
    [DotProductInnerProductSpace n K] : Matrix.dotProduct v (star v) = 0 ↔ v = 0 := by
  simpa only [star_star, star_eq_zero] using
    DotProductInnerProductSpace.dotProduct_star_self_eq_zero_iff (star v)


instance IsROrC.toStarDotProduct [IsROrC K] : DotProductInnerProductSpace n K where
  dotProduct_star_self_eq_zero_iff := by
    intro v
    rw [dotProduct, IsROrC.ext_iff]
    simp_rw [Function.funext_iff, IsROrC.zero_re', map_zero, Pi.star_apply, IsROrC.star_def,
      IsROrC.conj_mul, map_sum, IsROrC.ofReal_re, IsROrC.ofReal_im, IsROrC.re_to_real,
      IsROrC.im_to_real, Finset.sum_const_zero, and_true, Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg] <;>
    simp only [Finset.mem_univ, forall_true_left, map_eq_zero, implies_true, imp_self,
      IsROrC.normSq_nonneg]

instance Real.toStarDotProduct : DotProductInnerProductSpace n ℝ where
  dotProduct_star_self_eq_zero_iff := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff] <;>
    simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply, imp_self,
      mul_self_nonneg, implies_true]

instance Complex.toStarDotProduct : DotProductInnerProductSpace n ℂ where
  dotProduct_star_self_eq_zero_iff := by
    intro v
    simp_rw [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ext_iff, Complex.im_sum, Complex.zero_im, Complex.ofReal_im, Finset.sum_const_zero,
      and_true, Complex.zero_re, Complex.re_sum, Complex.ofReal_re, Function.funext_iff,
      Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg] <;>
    simp only [Finset.mem_univ, map_eq_zero, forall_true_left, imp_self]
    exact (fun _ => Complex.normSq_nonneg _)


instance Rat.toStarDotProduct : DotProductInnerProductSpace n ℚ where
  dotProduct_star_self_eq_zero_iff := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff] <;>
    simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply,
      mul_self_nonneg, implies_true, imp_self]

instance StarOrderedRing.toStarDotProduct [Field K] [PartialOrder K] [StarOrderedRing K] :
    DotProductInnerProductSpace n K where
  dotProduct_star_self_eq_zero_iff := by
    intro v
    rw [dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff] <;>
    simp only [Finset.mem_univ, Pi.star_apply, forall_true_left, star_mul_self_nonneg, implies_true,
      mul_eq_zero, Pi.zero_apply, star_eq_zero, or_self, imp_self]
