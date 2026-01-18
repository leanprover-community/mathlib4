/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/

@[expose] public section


namespace Matrix

section Finite

variable {m n R A : Type*} [CommRing R] [Finite m] [Finite n] (M : Matrix m n R)

attribute [local instance] Fintype.ofFinite

/-- A matrix `M` is right-separating if for all `w ≠ 0`, there is a `v` with `v * M * w ≠ 0`. -/
def SeparatingRight : Prop :=
  (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0)

/-- A matrix `M` is right-separating if for all `v ≠ 0`, there is a `w` with `v * M * w ≠ 0`. -/
def SeparatingLeft : Prop :=
  (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0)

/-- A matrix `M` is nondegenerate if it is both left-separating and right-separating. -/
structure Nondegenerate (M : Matrix m n R) : Prop where
  separatingLeft : SeparatingLeft M
  separatingRight : SeparatingRight M

end Finite

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

lemma separatingRight_def : M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert hw

lemma separatingLeft_def : M.SeparatingLeft ↔ (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) := by
  refine forall_congr' fun v ↦ ⟨fun hM hv ↦ hM ?_, fun hM hv ↦ hM ?_⟩ <;>
  convert hv

lemma nondegenerate_def : M.Nondegenerate ↔
   (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) ∧ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  constructor
  · exact fun h ↦ ⟨separatingLeft_def.mp h.1, separatingRight_def.mp h.2⟩
  · exact fun h ↦ ⟨separatingLeft_def.mpr h.1, separatingRight_def.mpr h.2⟩

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, v ⬝ᵥ M *ᵥ w = 0) : v = 0 :=
  (nondegenerate_def.mp hM).1 v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

/-- If `M` is nondegenerate and `w * M * v = 0` for all `v`, then `w = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho' {M : Matrix m n R} (hM : Nondegenerate M) {w : n → R}
    (hw : ∀ v, v ⬝ᵥ M *ᵥ w = 0) : w = 0 :=
  (nondegenerate_def.mp hM).2 w hw

/-- If `M` is nondegenerate and `w ≠ 0`, then there is some `v` such that `v * M * w ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero' {M : Matrix m n R} (hM : Nondegenerate M)
    {w : n → R} (hw : w ≠ 0) : ∃ v, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho' hw)

section Determinant
variable [DecidableEq m] {M : Matrix m m A}

/-- If `M` is square and has nonzero determinant, then `M` as a bilinear form on `n → A` is
nondegenerate. The "iff" implication, `nondegenerate_iff_det_ne_zero`, is proved in a later file.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDetNeZero`.
-/
theorem nondegenerate_of_det_ne_zero (hM : M.det ≠ 0) : Nondegenerate M := by
  refine nondegenerate_def.mpr ⟨fun v h ↦ ?_, fun w h ↦ ?_⟩
  · ext i
    specialize h (M.cramer (Pi.single i 1))
    simp_all
  · ext i
    contrapose! h
    use Pi.single i 1 ᵥ* M.adjugate
    rw [dotProduct_mulVec, vecMul_vecMul, adjugate_mul]
    simp_all [dotProduct, smul_apply, smul_eq_mul, Matrix.one_apply]

theorem eq_zero_of_vecMul_eq_zero (hM : M.det ≠ 0) {v : m → A}
    (hv : v ᵥ* M = 0) : v = 0 :=
  (nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho fun w => by
    rw [dotProduct_mulVec, hv, zero_dotProduct]

theorem eq_zero_of_mulVec_eq_zero (hM : M.det ≠ 0) {v : m → A}
    (hv : M *ᵥ v = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)

end Determinant

end Matrix
