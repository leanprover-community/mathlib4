/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.BilinearForm.IsPosSemidef

/-!
# Continuous bilinear forms

Define an abbreviation for continuous bilinear forms.

## Main definitions

* `ContinuousBilinForm.toMatrix`: The matrix representing a continuous bilinear form on a
  finite dimensional space.
* `ContinuousBilinForm.ofMatrix`: The continuous bilinear form represented by a matrix.
* `ContinuousBilinForm.inner`: The inner product as a continuous bilinear form.

## Implementation notes

We choose to redefine `ContinuousBilinForm.toMatrix` on top of `LinearMap.BilinForm.toMatrix`
to allow for dot notation.

## Tags

continuous bilinear form
-/

open scoped Matrix

namespace ContinuousBilinForm

variable {𝕜 E n : Type*} [NormedAddCommGroup E]

section RCLike

variable [RCLike 𝕜] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The type of continuous bilinear forms. -/
abbrev _root_.ContinuousBilinForm := E →L[𝕜] E →L[𝕜] 𝕜

variable (f : ContinuousBilinForm 𝕜 E) (b : Basis n 𝕜 E)

/-- The underlying bilinear form of a continuous bilinear form -/
def toBilinForm : LinearMap.BilinForm 𝕜 E where
  toFun x := f x
  map_add' x y := by simp
  map_smul' m x := by simp

@[simp]
lemma toBilinForm_apply (x y : E) : f.toBilinForm x y = f x y := rfl

section Matrix

variable [Fintype n] [DecidableEq n]

section toMatrix

/-- A continuous bilinear map on a finite dimensional space can be represented by a matrix. -/
noncomputable def toMatrix : Matrix n n 𝕜 :=
  BilinForm.toMatrix b f.toBilinForm

lemma toMatrix_def : f.toMatrix b = BilinForm.toMatrix b f.toBilinForm := rfl

@[simp]
lemma toMatrix_apply (i j : n) : f.toMatrix b i j = f (b i) (b j) := by
  simp [toMatrix]

lemma dotProduct_toMatrix_mulVec (x y : n → 𝕜) :
    x ⬝ᵥ (f.toMatrix b) *ᵥ y = f (b.equivFun.symm x) (b.equivFun.symm y) := by
  rw [toMatrix, BilinForm.dotProduct_toMatrix_mulVec, toBilinForm_apply]

lemma apply_eq_dotProduct_toMatrix_mulVec (x y : E) :
    f x y = (b.repr x) ⬝ᵥ (f.toMatrix b) *ᵥ (b.repr y) := by
  rw [toMatrix, ← BilinForm.apply_eq_dotProduct_toMatrix_mulVec, toBilinForm_apply]

end toMatrix

section ofMatrix

variable (b : Basis n 𝕜 E) (M : Matrix n n 𝕜)

/-- The continuous bilinear form represented by a matrix. -/
noncomputable def ofMatrix : ContinuousBilinForm 𝕜 E :=
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis b
  letI f : E →ₗ[𝕜] E →L[𝕜] 𝕜 :=
    { toFun x := (M.toBilin b x).toContinuousLinearMap
      map_add' x y := by ext; simp
      map_smul' m x := by ext; simp }
  f.toContinuousLinearMap

lemma ofMatrix_apply' (x y : E) : ofMatrix b M x y = M.toBilin b x y := rfl

lemma ofMatrix_apply (x y : E) :
    ofMatrix b M x y = b.repr x ⬝ᵥ M *ᵥ b.repr y := by
  simp [ofMatrix_apply', Matrix.toBilin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma ofMatrix_basis (i j : n) : ofMatrix b M (b i) (b j) = M i j := by
  simp [ofMatrix_apply, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]

lemma toMatrix_ofMatrix : ofMatrix b (f.toMatrix b) = f := by
  ext x y
  rw [ofMatrix_apply, f.apply_eq_dotProduct_toMatrix_mulVec b]

lemma ofMatrix_toMatrix : (ofMatrix b M).toMatrix b = M := by
  ext i j
  rw [toMatrix_apply, ofMatrix_basis]

end ofMatrix

end Matrix

end RCLike

section Real

section IsPosSemidef

variable [NormedSpace ℝ E] (f : ContinuousBilinForm ℝ E) (b : Basis n ℝ E)

/-- `f.IsPosSemidef` is an abbreviation for `f.toBilinForm.IsPosSemidef`. -/
abbrev IsPosSemidef : Prop := f.toBilinForm.IsPosSemidef

lemma isPosSemidef_def : f.IsPosSemidef ↔ f.toBilinForm.IsPosSemidef := .rfl

variable {f} [Fintype n] [DecidableEq n]

lemma isPosSemidef_iff_posSemidef_toMatrix :
    f.IsPosSemidef ↔ (f.toMatrix b).PosSemidef := by
  rw [f.isPosSemidef_def, LinearMap.BilinForm.isPosSemidef_iff_posSemidef_toMatrix b, toMatrix_def]

end IsPosSemidef

section Inner

variable [InnerProductSpace ℝ E]

open scoped RealInnerProductSpace

variable (E) in
/-- The inner product as continuous bilinear form.
-/
protected noncomputable def inner : ContinuousBilinForm ℝ E :=
  letI f : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ
    (fun x y ↦ ⟪x, y⟫)
    inner_add_left
    (fun c m n ↦ real_inner_smul_left m n c)
    inner_add_right
    (fun c m n ↦ real_inner_smul_right m n c)
  f.mkContinuous₂ 1 fun x y ↦
    by simpa [f] using abs_real_inner_le_norm x y

@[simp]
lemma inner_apply (x y : E) : ContinuousBilinForm.inner E x y = ⟪x, y⟫ := rfl

lemma isPosSemidef_inner : IsPosSemidef (.inner E) where
  eq := by simp [real_inner_comm]
  nonneg_re x := real_inner_self_nonneg

variable [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℝ E)

lemma inner_toMatrix_eq_one : (ContinuousBilinForm.inner E).toMatrix b.toBasis = 1 := by
  ext i j
  simp [Matrix.one_apply, b.inner_eq_ite]

end Inner

end Real

end ContinuousBilinForm
