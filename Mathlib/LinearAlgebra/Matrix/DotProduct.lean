/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Algebra.Star.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.IsROrC.Basic

#align_import linear_algebra.matrix.dot_product from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Dot product of two vectors

This file contains some results on the map `Matrix.dotProduct`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `Matrix.dotProduct_stdBasis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `Matrix.dotProduct_eq_zero_iff`: if `v`'s' dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix, reindex

-/


universe v w

variable {R : Type v} {n : Type w}

namespace Matrix

section Semiring

variable [Semiring R] [Fintype n]

@[simp]
theorem dotProduct_stdBasis_eq_mul [DecidableEq n] (v : n → R) (c : R) (i : n) :
    dotProduct v (LinearMap.stdBasis R (fun _ => R) i c) = v i * c := by
  rw [dotProduct, Finset.sum_eq_single i, LinearMap.stdBasis_same]
  exact fun _ _ hb => by rw [LinearMap.stdBasis_ne _ _ _ _ hb, MulZeroClass.mul_zero]
  exact fun hi => False.elim (hi <| Finset.mem_univ _)
#align matrix.dot_product_std_basis_eq_mul Matrix.dotProduct_stdBasis_eq_mul

-- @[simp] -- Porting note: simp can prove this
theorem dotProduct_stdBasis_one [DecidableEq n] (v : n → R) (i : n) :
    dotProduct v (LinearMap.stdBasis R (fun _ => R) i 1) = v i := by
  rw [dotProduct_stdBasis_eq_mul, mul_one]
#align matrix.dot_product_std_basis_one Matrix.dotProduct_stdBasis_one

theorem dotProduct_eq (v w : n → R) (h : ∀ u, dotProduct v u = dotProduct w u) : v = w := by
  funext x
  classical rw [← dotProduct_stdBasis_one v x, ← dotProduct_stdBasis_one w x, h]
#align matrix.dot_product_eq Matrix.dotProduct_eq

theorem dotProduct_eq_iff {v w : n → R} : (∀ u, dotProduct v u = dotProduct w u) ↔ v = w :=
  ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩
#align matrix.dot_product_eq_iff Matrix.dotProduct_eq_iff

theorem dotProduct_eq_zero (v : n → R) (h : ∀ w, dotProduct v w = 0) : v = 0 :=
  dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm
#align matrix.dot_product_eq_zero Matrix.dotProduct_eq_zero

theorem dotProduct_eq_zero_iff {v : n → R} : (∀ w, dotProduct v w = 0) ↔ v = 0 :=
  ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩
#align matrix.dot_product_eq_zero_iff Matrix.dotProduct_eq_zero_iff

end Semiring

section Self

variable [Fintype n]

@[simp]
theorem dotProduct_self_eq_zero [LinearOrderedRing R] {v : n → R} : dotProduct v v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans <| by
    simp [Function.funext_iff]
#align matrix.dot_product_self_eq_zero Matrix.dotProduct_self_eq_zero

/-- Note that this applies to `ℂ` via `Complex.strictOrderedCommRing`. -/
@[simp]
theorem dotProduct_star_self_eq_zero [PartialOrder R] [NonUnitalRing R] [StarOrderedRing R]
    [NoZeroDivisors R] {v : n → R} : dotProduct (star v) v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (@star_mul_self_nonneg _ _ _ _ (v i) : _)).trans <|
    by simp [Function.funext_iff, mul_eq_zero]
#align matrix.dot_product_star_self_eq_zero Matrix.dotProduct_star_self_eq_zero

/-- Note that this applies to `ℂ` via `Complex.strictOrderedCommRing`. -/
@[simp]
theorem dotProduct_self_star_eq_zero [PartialOrder R] [NonUnitalRing R] [StarOrderedRing R]
    [NoZeroDivisors R] {v : n → R} : dotProduct v (star v) = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (@star_mul_self_nonneg' _ _ _ _ (v i) : _)).trans <|
    by simp [Function.funext_iff, mul_eq_zero]
#align matrix.dot_product_self_star_eq_zero Matrix.dotProduct_self_star_eq_zero

end Self

section IsROrCFields
variable [Fintype n]
variable {K: Type}[IsROrC K]

lemma dot_product_star_self_eq_zero_iff_R_or_C
    (v : n → K) : Matrix.dotProduct (star v) v = 0 ↔  v = 0 := by
  simp_rw [Matrix.dotProduct, Pi.star_apply, ← starRingEnd_apply, IsROrC.conj_mul]
  rw [IsROrC.ext_iff]
  simp only [IsROrC.re_sum, IsROrC.ofReal_re, map_zero, IsROrC.im_sum, IsROrC.ofReal_im,
    Finset.sum_const_zero, and_true]
  constructor
  · intro hr
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hr
    · simp only [Finset.mem_univ, map_eq_zero, forall_true_left] at hr
      funext i
      exact hr i
    · simp only [Finset.mem_univ, forall_true_left]
      intro
      apply IsROrC.normSq_nonneg
  · intro h
    rw [h]
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
end IsROrCFields

end Matrix
