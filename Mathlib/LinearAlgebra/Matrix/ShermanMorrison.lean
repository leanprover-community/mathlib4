/-
Copyright (c) 2026 Alapan Chaudhuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alapan Chaudhuri
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Sherman-Morrison Formula

This file proves the Sherman-Morrison formula for matrix inverses under rank-1 updates.

## Main results

* `Matrix.inv_add_replicateCol_mul_replicateRow`: Sherman-Morrison in
  `replicateCol`/`replicateRow` form.
* `Matrix.inv_add_vecMulVec`: The Sherman-Morrison formula for `(A + vecMulVec u v)⁻¹`.
* `Matrix.inv_sub_vecMulVec`: The Sherman-Morrison formula for `(A - vecMulVec u v)⁻¹`.
* `Matrix.isUnit_det_add_vecMulVec`: Invertibility of `A + vecMulVec u v`.
* `Matrix.isUnit_det_sub_vecMulVec`: Invertibility of `A - vecMulVec u v`.

## References

* https://en.wikipedia.org/wiki/Sherman-Morrison_formula

## Tags

matrix inverse, rank-1 update, Sherman-Morrison, Woodbury
-/

@[expose] public section

variable {n : Type*} {α : Type*}

namespace Matrix

open scoped Matrix

section Field

variable [Fintype n] [DecidableEq n] [Field α]

/-- Sherman-Morrison formula in `replicateCol`/`replicateRow` form.

This is the Woodbury identity `add_mul_mul_inv_eq_sub` specialized to rank-1 updates. -/
theorem inv_add_replicateCol_mul_replicateRow (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + replicateCol Unit u * replicateRow Unit v)⁻¹ =
      A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ •
        (A⁻¹ * (replicateCol Unit u * replicateRow Unit v) * A⁻¹) := by
  have hA' : IsUnit A := A.isUnit_iff_isUnit_det.mpr hA
  have hAC : IsUnit (1 + replicateRow Unit v * A⁻¹ * replicateCol Unit u) := by
    exact (1 + replicateRow Unit v * A⁻¹ * replicateCol Unit u).isUnit_iff_isUnit_det.mpr <| by
      rw [det_unique, add_apply, one_apply_eq, ← replicateRow_vecMul]
      simp only [replicateRow_mul_replicateCol_apply, ← dotProduct_mulVec]
      exact hden.isUnit
  -- Apply Woodbury identity with C = 1
  have key := add_mul_mul_inv_eq_sub A (replicateCol Unit u) 1 (replicateRow Unit v)
    hA' isUnit_one (by simpa using hAC)
  simp only [Matrix.mul_one, inv_one] at key
  -- Regroup and convert 1×1 matrix inverse to scalar
  rw [key, ← Matrix.mul_assoc _ (replicateCol Unit u),
    Matrix.mul_assoc _ (replicateRow Unit v), Matrix.mul_assoc _ (replicateRow Unit v)]
  rw [← replicateCol_mulVec, ← replicateRow_vecMul, replicateRow_mul_replicateCol,
    smul_eq_mul_diagonal, inv_subsingleton (m := Unit)]
  simp only [Ring.inverse_eq_inv, ← dotProduct_mulVec, add_apply, one_apply_eq, of_apply]
  rw [← smul_eq_mul_diagonal, Matrix.smul_mul, smul_eq_mul_diagonal]

/-- The **Sherman-Morrison formula** for the inverse of a rank-1 update. -/
theorem inv_add_vecMulVec (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹ =
      A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) •
        vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  rw [vecMulVec_eq Unit, inv_add_replicateCol_mul_replicateRow A u v hA hden, one_div]
  congr 2
  -- Regroup: A⁻¹ * (U * V) * A⁻¹ → (A⁻¹ * U) * (V * A⁻¹)
  rw [Matrix.mul_assoc A⁻¹ _ A⁻¹, Matrix.mul_assoc (replicateCol Unit u) (replicateRow Unit v) A⁻¹,
      ← Matrix.mul_assoc A⁻¹ (replicateCol Unit u) (replicateRow Unit v * A⁻¹),
      ← replicateCol_mulVec, ← replicateRow_vecMul, ← vecMulVec_eq Unit]

/-- Variant of `inv_add_vecMulVec` with subtraction. -/
theorem inv_sub_vecMulVec (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 - v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A - vecMulVec u v)⁻¹ =
      A⁻¹ + (1 / (1 - v ⬝ᵥ (A⁻¹ *ᵥ u))) •
        vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  have h1 : A - vecMulVec u v = A + vecMulVec (-u) v := by
    rw [neg_vecMulVec, sub_eq_add_neg]
  have h2 : 1 + v ⬝ᵥ (A⁻¹ *ᵥ (-u)) = 1 - v ⬝ᵥ (A⁻¹ *ᵥ u) := by
    simp only [mulVec_neg, dotProduct_neg, sub_eq_add_neg]
  have hden' : 1 + v ⬝ᵥ (A⁻¹ *ᵥ (-u)) ≠ 0 := h2 ▸ hden
  rw [h1, inv_add_vecMulVec A (-u) v hA hden']
  simp only [mulVec_neg, neg_vecMulVec, one_div, dotProduct_neg, smul_neg,
    sub_eq_add_neg, neg_neg]

/-- Invertibility of a rank-1 update under the Sherman-Morrison hypotheses. -/
theorem isUnit_det_add_vecMulVec (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) : IsUnit (A + vecMulVec u v).det := by
  rw [vecMulVec_eq Unit]
  have h : (A + replicateCol Unit u * replicateRow Unit v).det =
      A.det * (1 + replicateRow Unit v * A⁻¹ * replicateCol Unit u).det :=
    det_add_replicateCol_mul_replicateRow hA u v
  rw [h]
  apply IsUnit.mul hA
  have heq : v ⬝ᵥ (A⁻¹ *ᵥ u) = (v ᵥ* A⁻¹) ⬝ᵥ u := dotProduct_mulVec v A⁻¹ u
  have hdet_eq : (1 + replicateRow Unit v * A⁻¹ * replicateCol Unit u).det =
      1 + u ⬝ᵥ (v ᵥ* A⁻¹) := by
    rw [det_unique]
    simp only [add_apply, one_apply_eq, mul_apply, replicateRow_apply, replicateCol_apply]
    congr 1
    simp only [dotProduct, vecMul]
    congr 1
    ext x
    ring
  rw [hdet_eq, dotProduct_comm, ← heq]
  exact hden.isUnit

/-- Invertibility of a rank-1 subtraction under the Sherman-Morrison hypotheses. -/
theorem isUnit_det_sub_vecMulVec (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 - v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) : IsUnit (A - vecMulVec u v).det := by
  have h1 : A - vecMulVec u v = A + vecMulVec (-u) v := by
    rw [neg_vecMulVec, sub_eq_add_neg]
  have h2 : 1 + v ⬝ᵥ (A⁻¹ *ᵥ (-u)) = 1 - v ⬝ᵥ (A⁻¹ *ᵥ u) := by
    simp only [mulVec_neg, dotProduct_neg, sub_eq_add_neg]
  rw [h1]
  exact isUnit_det_add_vecMulVec A (-u) v hA (h2 ▸ hden)

end Field

end Matrix
