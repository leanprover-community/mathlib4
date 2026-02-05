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

* `Matrix.inv_add_vecMulVec`: The Sherman-Morrison formula for `(A + vecMulVec u v)⁻¹`.
* `Matrix.isUnit_det_add_vecMulVec`: Invertibility of `A + vecMulVec u v`.

## References

* https://en.wikipedia.org/wiki/Sherman-Morrison_formula

## Tags

matrix inverse, rank-1 update, Sherman-Morrison, Woodbury
-/

@[expose] public section

variable {n : Type*} {α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype n] [CommRing α]

/-- Product of two outer products is a scalar multiple of an outer product. -/
theorem vecMulVec_mul_vecMulVec' (u v w x : n → α) :
    vecMulVec u v * vecMulVec w x = (v ⬝ᵥ w) • vecMulVec u x := by
  rw [vecMulVec_mul_vecMulVec]
  ext i j
  simp only [smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
  ring

end CommRing

section Field

variable [Fintype n] [DecidableEq n] [Field α]

/-- The **Sherman-Morrison formula** for the inverse of a rank-1 update. -/
theorem inv_add_vecMulVec (A : Matrix n n α) (u v : n → α) (hA : IsUnit A.det)
    (hden : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹ =
      A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) •
        vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  set R := A⁻¹ with hR
  set c := (1 + v ⬝ᵥ (R *ᵥ u))⁻¹ with hc
  set RHS := R - c • vecMulVec (R *ᵥ u) (v ᵥ* R) with hRHS
  have hc_eq : (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) = c := by simp only [one_div, hc, hR]
  rw [hc_eq, ← hRHS]
  apply inv_eq_left_inv
  have hRA : R * A = 1 := nonsing_inv_mul _ hA
  have hvRA : (v ᵥ* R) ᵥ* A = v := by rw [vecMul_vecMul, hRA, vecMul_one]
  have hdot_eq : (v ᵥ* R) ⬝ᵥ u = v ⬝ᵥ (R *ᵥ u) := by rw [← dotProduct_mulVec]
  have hcoeff : 1 - c - c * ((v ᵥ* R) ⬝ᵥ u) = 0 := by
    rw [hdot_eq]
    have h1 : c * (1 + v ⬝ᵥ (R *ᵥ u)) = 1 := inv_mul_cancel₀ hden
    calc 1 - c - c * (v ⬝ᵥ (R *ᵥ u))
        = 1 - c * (1 + v ⬝ᵥ (R *ᵥ u)) := by ring
      _ = 1 - 1 := by rw [h1]
      _ = 0 := by ring
  have step1 : RHS * (A + vecMulVec u v) =
      R * A + R * vecMulVec u v
      - c • (vecMulVec (R *ᵥ u) (v ᵥ* R) * A)
      - c • (vecMulVec (R *ᵥ u) (v ᵥ* R) * vecMulVec u v) := by
    simp only [hRHS, sub_mul, smul_mul_assoc, mul_add]
    abel
  have step2 : R * A + R * vecMulVec u v
      - c • (vecMulVec (R *ᵥ u) (v ᵥ* R) * A)
      - c • (vecMulVec (R *ᵥ u) (v ᵥ* R) * vecMulVec u v) =
      1 + vecMulVec (R *ᵥ u) v
      - c • vecMulVec (R *ᵥ u) v
      - c • (((v ᵥ* R) ⬝ᵥ u) • vecMulVec (R *ᵥ u) v) := by
    rw [hRA, mul_vecMulVec, vecMulVec_mul, hvRA, vecMulVec_mul_vecMulVec']
  have step3 : 1 + vecMulVec (R *ᵥ u) v
      - c • vecMulVec (R *ᵥ u) v
      - c • (((v ᵥ* R) ⬝ᵥ u) • vecMulVec (R *ᵥ u) v) =
      1 + (1 - c - c * ((v ᵥ* R) ⬝ᵥ u)) • vecMulVec (R *ᵥ u) v := by
    rw [smul_smul]
    ext i j
    simp only [add_apply, sub_apply, smul_apply, one_apply, smul_eq_mul]
    ring
  rw [step1, step2, step3, hcoeff, zero_smul, add_zero]

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
  simp only [mulVec_neg, neg_vecMulVec, one_div]
  ext i j
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, neg_apply]
  have hdot_neg : v ⬝ᵥ -(A⁻¹ *ᵥ u) = -(v ⬝ᵥ (A⁻¹ *ᵥ u)) :=
    dotProduct_neg v (A⁻¹ *ᵥ u)
  simp only [hdot_neg, mul_neg]
  ring

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

end Field

end Matrix
