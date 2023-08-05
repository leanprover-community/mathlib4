/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.IsROrC.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Fields with Star Inner Product (dotProduct or vector Product) as Norm

This file defines the class type `StarDotProductSpace` i.e. fields with star operation compatible
with field operations (StarRing) such that the stared vector product (in 1st argument) is zero only
if the vector is zero.
-/

open BigOperators Matrix

class StarDotProductSpace (n K) [Fintype n][Ring K][StarRing K] : Prop where
  dotProduct_star_self_eq_zero (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔ v = 0

variable {n : Type _}[Fintype n]

lemma dotProduct_self_star_eq_zero  (v : n → K) [Ring K] [StarRing K]
    [StarDotProductSpace n K] : Matrix.dotProduct v (star v) = 0 ↔ v = 0 := by
  simpa only [star_star, star_eq_zero] using
    StarDotProductSpace.dotProduct_star_self_eq_zero (star v)


section IsROrCFields

variable {K: Type _} [IsROrC K]

open IsROrC

def instStarDotProduct_IsROrC [IsROrC K] : StarDotProductSpace n K where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [dotProduct, IsROrC.ext_iff, IsROrC.ext_iff, Function.funext_iff]
    simp_rw [zero_re', map_zero, Pi.star_apply, star_def, IsROrC.conj_mul, map_sum,
      ofReal_re, ofReal_im, re_to_real, im_to_real, Finset.sum_const_zero, and_true, Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg] <;>
    simp only [Finset.mem_univ, map_eq_zero, forall_true_left, normSq_nonneg, implies_true]

end IsROrCFields


def instStarDotProduct_R : StarDotProductSpace n ℝ where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff]
    all_goals ( simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply,
      mul_self_nonneg, implies_true] )

open Complex
def instStarDotProduct_C : StarDotProductSpace n ℂ where
  dotProduct_star_self_eq_zero := by
    intro v
    simp_rw [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ext_iff, Complex.im_sum, zero_im, ofReal_im, Finset.sum_const_zero, and_true,
      zero_re, re_sum, ofReal_re]
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    simp only [Finset.mem_univ, map_eq_zero, forall_true_left]
    refine ⟨Function.funext_iff.2, Function.funext_iff.1⟩
    simp only [Finset.mem_univ, forall_true_left, normSq_nonneg, implies_true]

instance instQStar : Star ℚ where
  star := fun x => x

instance instTrivialQStar : TrivialStar ℚ where
  star_trivial := by
    intro x;
    unfold star instQStar
    simp only [Rat.cast_eq_id, id_eq]

instance instQStarRing : StarRing ℚ where
  star_mul := fun r s ↦ mul_comm r s
  star_add := by simp;
  star_involutive := star_trivial

instance instStarDotProduct_Q : StarDotProductSpace n ℚ where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [star_trivial, dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff] <;>
    simp only [Finset.mem_univ, mul_eq_zero, or_self, forall_true_left, Pi.zero_apply,
      mul_self_nonneg, implies_true]

variable {K : Type _}

instance instStarDotProduct_starOrderedRing [Field K] [PartialOrder K] [StarOrderedRing K] :
    StarDotProductSpace n K where
  dotProduct_star_self_eq_zero := by
    intro v
    rw [dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Function.funext_iff] <;>
    simp only [Finset.mem_univ, Pi.star_apply, forall_true_left, star_mul_self_nonneg, implies_true,
      mul_eq_zero, Pi.zero_apply, star_eq_zero, or_self]
