/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Algebra.Star.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.StdBasis

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


variable {m n p R : Type*}

namespace Matrix

section Semiring

variable [Semiring R] [Fintype n]

@[simp]
theorem dotProduct_stdBasis_eq_mul [DecidableEq n] (v : n → R) (c : R) (i : n) :
    dotProduct v (LinearMap.stdBasis R (fun _ => R) i c) = v i * c := by
  rw [dotProduct, Finset.sum_eq_single i, LinearMap.stdBasis_same]
  -- ⊢ ∀ (b : n), b ∈ Finset.univ → b ≠ i → v b * ↑(LinearMap.stdBasis R (fun x =>  …
  exact fun _ _ hb => by rw [LinearMap.stdBasis_ne _ _ _ _ hb, mul_zero]
  -- ⊢ ¬i ∈ Finset.univ → v i * ↑(LinearMap.stdBasis R (fun x => R) i) c i = 0
  exact fun hi => False.elim (hi <| Finset.mem_univ _)
  -- 🎉 no goals
#align matrix.dot_product_std_basis_eq_mul Matrix.dotProduct_stdBasis_eq_mul

-- @[simp] -- Porting note: simp can prove this
theorem dotProduct_stdBasis_one [DecidableEq n] (v : n → R) (i : n) :
    dotProduct v (LinearMap.stdBasis R (fun _ => R) i 1) = v i := by
  rw [dotProduct_stdBasis_eq_mul, mul_one]
  -- 🎉 no goals
#align matrix.dot_product_std_basis_one Matrix.dotProduct_stdBasis_one

theorem dotProduct_eq (v w : n → R) (h : ∀ u, dotProduct v u = dotProduct w u) : v = w := by
  funext x
  -- ⊢ v x = w x
  classical rw [← dotProduct_stdBasis_one v x, ← dotProduct_stdBasis_one w x, h]
  -- 🎉 no goals
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

variable [Fintype m] [Fintype n] [Fintype p]

@[simp]
theorem dotProduct_self_eq_zero [LinearOrderedRing R] {v : n → R} : dotProduct v v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans <| by
    simp [Function.funext_iff]
    -- 🎉 no goals
#align matrix.dot_product_self_eq_zero Matrix.dotProduct_self_eq_zero

section StarOrderedRing

variable [PartialOrder R] [NonUnitalRing R] [StarOrderedRing R] [NoZeroDivisors R]

/-- Note that this applies to `ℂ` via `Complex.strictOrderedCommRing`. -/
@[simp]
theorem dotProduct_star_self_eq_zero {v : n → R} : dotProduct (star v) v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (@star_mul_self_nonneg _ _ _ _ (v i) : _)).trans <|
    by simp [Function.funext_iff, mul_eq_zero]
       -- 🎉 no goals
#align matrix.dot_product_star_self_eq_zero Matrix.dotProduct_star_self_eq_zero

/-- Note that this applies to `ℂ` via `Complex.strictOrderedCommRing`. -/
@[simp]
theorem dotProduct_self_star_eq_zero {v : n → R} : dotProduct v (star v) = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (@star_mul_self_nonneg' _ _ _ _ (v i) : _)).trans <|
    by simp [Function.funext_iff, mul_eq_zero]
       -- 🎉 no goals
#align matrix.dot_product_self_star_eq_zero Matrix.dotProduct_self_star_eq_zero

@[simp]
lemma conjTranspose_mul_self_eq_zero {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]
lemma self_mul_conjTranspose_eq_zero {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

lemma conjTranspose_mul_self_mul_eq_zero (A : Matrix m n R) (B : Matrix n p R) :
    (Aᴴ * A) * B = 0 ↔ A * B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  -- ⊢ A * B = 0
  apply_fun (Bᴴ * ·) at h
  -- ⊢ A * B = 0
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h

lemma self_mul_conjTranspose_mul_eq_zero (A : Matrix m n R) (B : Matrix m p R) :
    (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _
  -- 🎉 no goals

lemma mul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (B : Matrix p m R) :
    B * (A * Aᴴ) = 0 ↔ B * A = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    self_mul_conjTranspose_mul_eq_zero, ← conjTranspose_mul, conjTranspose_eq_zero]

lemma mul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (B : Matrix p n R) :
    B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0 := by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _
  -- 🎉 no goals

lemma conjTranspose_mul_self_mulVec_eq_zero (A : Matrix m n R) (v : n → R) :
    (Aᴴ * A).mulVec v = 0 ↔ A.mulVec v = 0 := by
  simpa only [← Matrix.col_mulVec, col_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (col v)

lemma self_mul_conjTranspose_mulVec_eq_zero (A : Matrix m n R) (v : m → R) :
    (A * Aᴴ).mulVec v = 0 ↔ Aᴴ.mulVec v = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _
  -- 🎉 no goals

lemma vecMul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (v : n → R) :
    vecMul v (Aᴴ * A) = 0 ↔ vecMul v Aᴴ = 0 := by
  simpa only [← Matrix.row_vecMul, row_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (row v)

lemma vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m → R) :
    vecMul v (A * Aᴴ) = 0 ↔ vecMul v A = 0 := by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _
  -- 🎉 no goals

end StarOrderedRing

end Self

end Matrix
