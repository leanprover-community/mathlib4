/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Dare
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Polar decomposition of an invertible matrix

Every invertible matrix over `RCLike` scalars factors uniquely as `A = Q * P`
with `Q` unitary and `P` positive definite.

## Main definitions

* `Matrix.polarFactor`: the positive-definite factor `√(Aᴴ * A)`.
* `Matrix.polarUnitary`: the unitary factor `A * (√(Aᴴ * A))⁻¹`.

## Main results

* `Matrix.exists_polarDecomposition`: existence of the factorisation.
* `Matrix.eq_polarFactor_of_mul`, `Matrix.eq_polarUnitary_of_mul`: each factor
  is determined by the equation.
* `Matrix.existsUnique_polarDecomposition`: the two together.

## Implementation notes

The square root of `Aᴴ * A` is taken with the continuous functional calculus
(`CFC.sqrt`) rather than via the spectral theorem. The Loewner order and the
functional calculus on matrices are already available for `RCLike` scalars, so
the only property of the square root the construction uses is
`CFC.sqrt_mul_sqrt_self`, and uniqueness of the factorisation reduces to
`CFC.sqrt_unique`.

Note the order convention: this is the *left* polar decomposition `A = Q * P`
with `P = √(Aᴴ * A)`. The right-handed version `A = P' * Q` with
`P' = √(A * Aᴴ)` is not developed here.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The positive-definite factor -/

/-- The positive-definite factor of the polar decomposition of `A`, `√(Aᴴ * A)`. -/
noncomputable def polarFactor (A : Matrix n n 𝕜) : Matrix n n 𝕜 := CFC.sqrt (Aᴴ * A)

theorem polarFactor_posSemidef (A : Matrix n n 𝕜) : (polarFactor A).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

@[simp]
theorem polarFactor_mul_self (A : Matrix n n 𝕜) :
    polarFactor A * polarFactor A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg

theorem polarFactor_isHermitian (A : Matrix n n 𝕜) : (polarFactor A).IsHermitian :=
  (polarFactor_posSemidef A).isHermitian

section Invertible

variable {A : Matrix n n 𝕜} (hA : IsUnit A.det)
include hA

theorem det_polarFactor_ne_zero : (polarFactor A).det ≠ 0 := by
  intro h
  have hsq : (polarFactor A).det * (polarFactor A).det = (Aᴴ * A).det := by
    rw [← det_mul, polarFactor_mul_self]
  rw [h, mul_zero, det_mul, det_conjTranspose] at hsq
  exact hA.ne_zero (by simpa [star_eq_zero] using mul_eq_zero.mp hsq.symm)

theorem isUnit_det_polarFactor : IsUnit (polarFactor A).det :=
  isUnit_iff_ne_zero.mpr (det_polarFactor_ne_zero hA)

/-- If `A` is invertible then `polarFactor A` is positive definite, not merely
positive semidefinite. -/
theorem polarFactor_posDef : (polarFactor A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨polarFactor_isHermitian A, fun x hx => ?_⟩
  refine lt_of_le_of_ne ((polarFactor_posSemidef A).dotProduct_mulVec_nonneg x) ?_
  intro heq
  have hker : polarFactor A *ᵥ x = 0 :=
    ((polarFactor_posSemidef A).dotProduct_mulVec_zero_iff x).mp heq.symm
  refine hx ?_
  have hx0 := congrArg (fun v => (polarFactor A)⁻¹ *ᵥ v) hker
  simpa [mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_polarFactor hA)] using hx0

/-! ### The unitary factor -/

/-- The unitary factor of the polar decomposition of `A`, `A * (√(Aᴴ * A))⁻¹`. -/
noncomputable def polarUnitary (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  A * (polarFactor A)⁻¹

@[simp]
theorem polarUnitary_mul_polarFactor : polarUnitary A * polarFactor A = A := by
  rw [polarUnitary, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_polarFactor hA),
    Matrix.mul_one]

theorem polarUnitary_mem_unitaryGroup : polarUnitary A ∈ Matrix.unitaryGroup n 𝕜 := by
  have hinv : IsUnit (polarFactor A).det := isUnit_det_polarFactor hA
  have hinvHerm : ((polarFactor A)⁻¹)ᴴ = (polarFactor A)⁻¹ := by
    rw [conjTranspose_nonsing_inv, polarFactor_isHermitian A]
  rw [mem_unitaryGroup_iff']
  change (polarUnitary A)ᴴ * polarUnitary A = 1
  rw [polarUnitary, conjTranspose_mul, hinvHerm]
  calc (polarFactor A)⁻¹ * Aᴴ * (A * (polarFactor A)⁻¹)
      = (polarFactor A)⁻¹ * (Aᴴ * A) * (polarFactor A)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarFactor A)⁻¹ * (polarFactor A * polarFactor A) * (polarFactor A)⁻¹ := by
        rw [polarFactor_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hinv, Matrix.one_mul,
          mul_nonsing_inv _ hinv]

/-- **Polar decomposition.** An invertible matrix is a unitary matrix times a
positive-definite one. -/
theorem exists_polarDecomposition :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, ∃ P : Matrix n n 𝕜, P.PosDef ∧ A = Q * P :=
  ⟨polarUnitary A, polarUnitary_mem_unitaryGroup hA, polarFactor A,
    polarFactor_posDef hA, (polarUnitary_mul_polarFactor hA).symm⟩

/-! ### Uniqueness -/

omit hA in
/-- The positive-definite factor of a polar decomposition is `polarFactor`. -/
theorem eq_polarFactor_of_mul {Q P : Matrix n n 𝕜} (hQ : Q ∈ Matrix.unitaryGroup n 𝕜)
    (hP : P.PosDef) (hQP : A = Q * P) : P = polarFactor A := by
  refine (CFC.sqrt_unique ?_ hP.posSemidef.nonneg).symm
  have hQ' : Qᴴ * Q = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (mem_unitaryGroup_iff' (A := Q)).mp hQ
  calc P * P = Pᴴ * (Qᴴ * Q) * P := by rw [hQ', hP.isHermitian]; simp
    _ = (Q * P)ᴴ * (Q * P) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * A := by rw [← hQP]

/-- The unitary factor of a polar decomposition is `polarUnitary`. -/
theorem eq_polarUnitary_of_mul {Q P : Matrix n n 𝕜} (hQ : Q ∈ Matrix.unitaryGroup n 𝕜)
    (hP : P.PosDef) (hQP : A = Q * P) : Q = polarUnitary A := by
  have hPeq : P = polarFactor A := eq_polarFactor_of_mul hQ hP hQP
  have hinv : IsUnit (polarFactor A).det := isUnit_det_polarFactor hA
  have key : Q * polarFactor A = A := by rw [← hPeq, ← hQP]
  calc Q = Q * (polarFactor A * (polarFactor A)⁻¹) := by
        rw [mul_nonsing_inv _ hinv, Matrix.mul_one]
    _ = Q * polarFactor A * (polarFactor A)⁻¹ := by rw [Matrix.mul_assoc]
    _ = A * (polarFactor A)⁻¹ := by rw [key]
    _ = polarUnitary A := rfl

/-- **Polar decomposition, with uniqueness.** -/
theorem existsUnique_polarDecomposition :
    ∃! QP : Matrix n n 𝕜 × Matrix n n 𝕜,
      QP.1 ∈ Matrix.unitaryGroup n 𝕜 ∧ QP.2.PosDef ∧ A = QP.1 * QP.2 := by
  refine ⟨(polarUnitary A, polarFactor A),
    ⟨polarUnitary_mem_unitaryGroup hA, polarFactor_posDef hA,
      (polarUnitary_mul_polarFactor hA).symm⟩, ?_⟩
  rintro ⟨Q, P⟩ ⟨hQ, hP, hQP⟩
  exact Prod.ext (eq_polarUnitary_of_mul hA hQ hP hQP) (eq_polarFactor_of_mul hQ hP hQP)

end Invertible

end Matrix
