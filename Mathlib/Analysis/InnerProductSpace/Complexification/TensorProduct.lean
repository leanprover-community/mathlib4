/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Complexification.Basic
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! # Tensor product description of complexifications

The complexification space of a real space `E` is equivalent to `ℂ ⊗[ℝ] E` (see
`Complexification.toTensor`.) And so the complexification of a tensor product is the tensor product
of the complexifications (see `TensorProduct.complexificationLinearEquiv`).

The matrix of a complexified operator is essentially the matrix of the original operator lifted
to `ℂ`. -/

public section

variable {𝕜 E Eₗ Fₗ : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup Eₗ] [NormedAddCommGroup Fₗ]
  [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ Eₗ] [InnerProductSpace ℝ Fₗ]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

open TensorProduct Complexification

/-- The complexification of a space `E` is `ℂ`-linearly equivalent to `ℂ ⊗[ℝ] E`. -/
@[expose] noncomputable def Complexification.toTensor :
    Complexification 𝕜 E ≃ₗ[ℂ] ℂ ⊗[ℝ] E := .symm
  { toLinearMap := AlgebraTensorModule.lift (.toSpanSingleton ℂ _ (inclusion 𝕜 E).toLinearMap)
    invFun v := 1 ⊗ₜ v.re + Complex.I ⊗ₜ v.im
    right_inv _ := by simp
    left_inv x := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul z x =>
        conv_rhs => rw [← Complex.re_add_im z]
        simp [-Complex.re_add_im, add_tmul, smul_def, smul_tmul']
      | add _ _ h1 h2 =>
        conv_rhs => rw [← h1, ← h2]
        simp [tmul_add]
        grind }

@[simp] lemma Complexification.toTensor_apply (v : Complexification 𝕜 E) :
    v.toTensor = 1 ⊗ₜ v.re + .I ⊗ₜ v.im := rfl

@[simp] lemma Complexification.symm_toTensor_tmul (z : ℂ) (x : E) :
    toTensor.symm (z ⊗ₜ x) = .mk 𝕜 (z.re • x) (z.im • x) := by simp [smul_def, toTensor]

/-- The rank of the complexification of a space over `ℂ` is equal to the rank of the original
space over `ℝ`. -/
@[simp] lemma Complexification.rank_eq :
    Module.rank ℂ (Complexification 𝕜 E) = Module.rank ℝ E := by
  simp [toTensor.rank_eq]

@[simp] lemma Complexification.finrank_eq :
    Module.finrank ℂ (Complexification 𝕜 E) = Module.finrank ℝ E := by
  simp [toTensor.finrank_eq]

open scoped RingTheory.LinearMap in
/-- The tensor version of `T.toComplexification` is `id ⊗ₘ T`. -/
lemma ContinuousLinearMap.arrowCongr_toTensor_toComplexification {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (T : E →L[𝕜] F) :
    toTensor.arrowCongr toTensor T.toComplexification.toLinearMap =
      (.id : ℂ →ₗ[ℝ] ℂ) ⊗ₘ (T.toLinearMap.restrictScalars ℝ) := by
  ext; simp [smul_tmul', ← add_tmul]

variable (𝕜) in
/-- The complexification of a basis, given by `b.complexification i = (b i, 0)`. -/
@[expose] noncomputable def Module.Basis.complexification {ι} (b : Module.Basis ι ℝ E) :
    Module.Basis ι ℂ (Complexification 𝕜 E) := (b.baseChange ℂ).map toTensor.symm

@[simp] lemma Module.Basis.complexification_apply {ι} (b : Module.Basis ι ℝ E) (i : ι) :
    b.complexification 𝕜 i = .mk 𝕜 (b i) 0 := by simp [Module.Basis.complexification]

@[simp] lemma Module.Basis.complexification_repr_apply {ι} (b : Module.Basis ι ℝ E) (v) :
    (b.complexification 𝕜).repr v = (b.baseChange ℂ).repr (1 ⊗ₜ[ℝ] v.re) +
      (b.baseChange ℂ).repr (Complex.I ⊗ₜ[ℝ] v.im) := by simp [Module.Basis.complexification]

/-- Complexifying `ℝ`-tensor products of real spaces is equivalent to `ℂ`-tensor products
of the complexification of each of those spaces. -/
@[expose, simps! -isSimp] noncomputable def TensorProduct.complexificationLinearEquiv :
    Complexification ℝ (Eₗ ⊗[ℝ] Fₗ) ≃ₗ[ℂ] Complexification ℝ Eₗ ⊗[ℂ] Complexification ℝ Fₗ :=
  toTensor ≪≫ₗ
    (AlgebraTensorModule.assoc ..).symm ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    TensorProduct.congr toTensor.symm toTensor.symm

@[simp] lemma TensorProduct.complexificationLinearEquiv_mk_tmul (x : Eₗ) (y : Fₗ) :
    TensorProduct.complexificationLinearEquiv (.mk ℝ (x ⊗ₜ y) 0) =
      .mk ℝ x 0 ⊗ₜ .mk ℝ y 0 := by simp [TensorProduct.complexificationLinearEquiv_apply]

@[simp] lemma TensorProduct.symm_complexificationLinearEquiv_mk_tmul_mk (x : Eₗ) (y : Fₗ) :
    TensorProduct.complexificationLinearEquiv.symm (.mk ℝ x 0 ⊗ₜ .mk ℝ y 0) =
      .mk ℝ (x ⊗ₜ y) 0 := by simp [TensorProduct.complexificationLinearEquiv_symm_apply]

lemma ContinuousLinearMap.toMatrix_complexification_toComplexification
    {F ι₁ ι₂ : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [Fintype ι₁] [Finite ι₂]
    [DecidableEq ι₁] (T : E →L[𝕜] F) (b₁ : Module.Basis ι₁ ℝ E) (b₂ : Module.Basis ι₂ ℝ F) :
    T.toComplexification.toMatrix (b₁.complexification 𝕜) (b₂.complexification 𝕜) =
      (T.toMatrix b₁ b₂).map (algebraMap ℝ ℂ) := by ext; simp [LinearMap.toMatrix_apply]
