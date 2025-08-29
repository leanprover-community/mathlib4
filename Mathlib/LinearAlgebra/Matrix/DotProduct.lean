/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Star.Pi
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Dot product of two vectors

This file contains some results on the map `dotProduct`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `dotProduct_stdBasis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `dotProduct_eq_zero_iff`: if `v`'s dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix

-/


variable {m n p R : Type*}

section Semiring

variable [Semiring R] [Fintype n]

theorem dotProduct_eq (v w : n → R) (h : ∀ u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

theorem dotProduct_eq_iff {v w : n → R} : (∀ u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w :=
  ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

theorem dotProduct_eq_zero (v : n → R) (h : ∀ w, v ⬝ᵥ w = 0) : v = 0 :=
  dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

theorem dotProduct_eq_zero_iff {v : n → R} : (∀ w, v ⬝ᵥ w = 0) ↔ v = 0 :=
  ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

end Semiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

lemma dotProduct_nonneg_of_nonneg {v w : n → R} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

lemma dotProduct_le_dotProduct_of_nonneg_right {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    u ⬝ᵥ w ≤ v ⬝ᵥ w :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (huv i) (hw i)

lemma dotProduct_le_dotProduct_of_nonneg_left {u v w : n → R} (huv : u ≤ v) (hw : 0 ≤ w) :
    w ⬝ᵥ u ≤ w ⬝ᵥ v :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (huv i) (hw i))

end OrderedSemiring

section Self

variable [Fintype m] [Fintype n] [Fintype p]

@[simp]
theorem dotProduct_self_eq_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {v : n → R} :
    v ⬝ᵥ v = 0 ↔ v = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans <| by
    simp [funext_iff]

section StarOrderedRing

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_star_self_nonneg (v : n → R) : 0 ≤ star v ⬝ᵥ v :=
  Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_self_star_nonneg (v : n → R) : 0 ≤ v ⬝ᵥ star v :=
  Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

variable [NoZeroDivisors R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_star_self_eq_zero {v : n → R} : star v ⬝ᵥ v = 0 ↔ v = 0 :=
  (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans <|
    by simp [funext_iff, mul_eq_zero]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_self_star_eq_zero {v : n → R} : v ⬝ᵥ star v = 0 ↔ v = 0 :=
  (Fintype.sum_eq_zero_iff_of_nonneg fun _ => mul_star_self_nonneg _).trans <|
    by simp [funext_iff, mul_eq_zero]

namespace Matrix

@[simp]
lemma conjTranspose_mul_self_eq_zero {n} {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]
lemma self_mul_conjTranspose_eq_zero {m} {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

lemma conjTranspose_mul_self_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix n p R) :
    (Aᴴ * A) * B = 0 ↔ A * B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h

lemma self_mul_conjTranspose_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix m p R) :
    (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _

lemma mul_self_mul_conjTranspose_eq_zero {p} (A : Matrix m n R) (B : Matrix p m R) :
    B * (A * Aᴴ) = 0 ↔ B * A = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    self_mul_conjTranspose_mul_eq_zero, ← conjTranspose_mul, conjTranspose_eq_zero]

lemma mul_conjTranspose_mul_self_eq_zero {p} (A : Matrix m n R) (B : Matrix p n R) :
    B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0 := by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _

lemma conjTranspose_mul_self_mulVec_eq_zero (A : Matrix m n R) (v : n → R) :
    (Aᴴ * A) *ᵥ v = 0 ↔ A *ᵥ v = 0 := by
  simpa only [← Matrix.replicateCol_mulVec, replicateCol_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (replicateCol (Fin 1) v)

lemma self_mul_conjTranspose_mulVec_eq_zero (A : Matrix m n R) (v : m → R) :
    (A * Aᴴ) *ᵥ v = 0 ↔ Aᴴ *ᵥ v = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _

lemma vecMul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (v : n → R) :
    v ᵥ* (Aᴴ * A) = 0 ↔ v ᵥ* Aᴴ = 0 := by
  simpa only [← Matrix.replicateRow_vecMul, replicateRow_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (replicateRow (Fin 1) v)

lemma vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m → R) :
    v ᵥ* (A * Aᴴ) = 0 ↔ v ᵥ* A = 0 := by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_star_self_pos_iff {v : n → R} :
    0 < star v ⬝ᵥ v ↔ v ≠ 0 := by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
  refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans <| exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| isRegular_of_ne_zero ·)

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
theorem dotProduct_self_star_pos_iff {v : n → R} : 0 < dotProduct v (star v) ↔ v ≠ 0 := by
  simpa using dotProduct_star_self_pos_iff (v := star v)

end Matrix

end StarOrderedRing

end Self
