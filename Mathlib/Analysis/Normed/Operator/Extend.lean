/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.LocallyConvex.Extend

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `LinearMap.extendOfNorm`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.

Moreover, we can extend a linear equivalence:
* `LinearEquiv.extend`: Extend a linear equivalence between normed spaces to a continuous linear
  equivalence between Banach spaces with two dense maps `e₁` and `e₂` and the corresponding norm
  estimates.
* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
  `Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Banach spaces
  and `f` preserves the norm.

-/

@[expose] public section

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) {e : E →L[𝕜] Eₗ}

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {C : ℝ≥0} [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le (h_dense : DenseRange e) (h_e : ∀ x, ‖x‖ ≤ C * ‖e x‖) :
    ‖f.extend e‖ ≤ C * ‖f‖ := by
  apply opNorm_le_bound _ (by positivity)
  refine isClosed_property h_dense (isClosed_le (by fun_prop) (by fun_prop)) fun x ↦ ?_
  rw [extend_eq _ h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing]
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
    _ ≤ ‖f‖ * (C * ‖e x‖) := by grw [h_e x]
    _ = C * ‖f‖ * ‖e x‖ := by ring


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section NormedDivisionRing

variable [NormedField 𝕜] [NormedField 𝕜₂] -- generalize to `NormedDivisionRing` after PR
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

/-- Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`. -/
def extendOfNorm : Eₗ →SL[σ₁₂] F := --(f.compLeftInverse e).extend (LinearMap.range e).subtypeL
  f.extendOfIsBounded e (norm_withSeminorms 𝕜 Eₗ) (norm_withSeminorms 𝕜₂ F)

variable {f e}

omit [CompleteSpace F] in
theorem foo (p : Seminorm 𝕜 E) (q : Seminorm 𝕜₂ F) :
    Seminorm.IsBounded (fun _ : Fin 1 ↦ p) (fun _ : Fin 1 ↦ q) f ↔ ∃ C : ℝ≥0, q.comp f ≤ C • p := by
  constructor
  · intro h
    obtain ⟨s, C, h⟩ := h 0
    use C
    by_cases! hs : s.Nonempty
    · simpa [Finset.sup_const hs p] using h
    · rw [hs] at h
      simp only [Finset.sup_empty] at h
      grw [h]
      simp only [Seminorm.bot_eq_zero, smul_zero, Seminorm.le_def, _root_.zero_apply,
        _root_.smul_apply]
      intro x
      positivity
  · intro ⟨C, h⟩ i
    use {0}, C
    simpa


omit [CompleteSpace F] in
theorem foo' (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖) :
    Seminorm.IsBounded (SeminormFamily.comp (fun _ : Fin 1 ↦ normSeminorm 𝕜 Eₗ) e)
      (fun _ : Fin 1 ↦ normSeminorm 𝕜₂ F) f := by
  obtain ⟨C, h⟩ := h_norm
  apply (foo _ _).mpr
  use C.toNNReal
  rw [Seminorm.le_def]
  peel h with x h
  simp only [Seminorm.comp_apply, coe_normSeminorm,
    _root_.smul_apply, NNReal.smul_def, smul_eq_mul]
  grw [h]
  gcongr
  · exact Real.le_coe_toNNReal C
  · rfl

theorem extendOfNorm_eq (h_dense : DenseRange e) (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖)
    (x : E) : f.extendOfNorm e (e x) = f x :=
  extendOfIsBounded_eq h_dense (norm_withSeminorms 𝕜 Eₗ) (norm_withSeminorms 𝕜₂ F) (foo' h_norm) _

theorem norm_extendOfNorm_apply_le (h_dense : DenseRange e) (C : ℝ)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : Eₗ) :
    ‖f.extendOfNorm e x‖ ≤ C * ‖x‖ := by
  have h_mem : ∀ (x : Eₗ) (hy : x ∈ (LinearMap.range e)), ‖extendOfNorm f e x‖ ≤ C * ‖x‖ := by
    intro x ⟨y, hxy⟩
    simpa only [← hxy, extendOfNorm_eq h_dense ⟨C, h_norm⟩ y] using h_norm y
  exact h_dense.induction h_mem (isClosed_le (by fun_prop) (by fun_prop)) x

theorem extendOfNorm_unique (h_dense : DenseRange e) (C : ℝ) (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖)
    (g : Eₗ →SL[σ₁₂] F) (H : g.toLinearMap.comp e = f) : extendOfNorm f e = g := by
  apply ContinuousLinearMap.extend_unique
  · simpa using! h_dense
  · exact isUniformEmbedding_subtype_val.isUniformInducing
  ext ⟨y, x, hxy⟩
  rw [compLeftInverse_apply_of_bdd _ _ (norm_withSeminorms 𝕜 Eₗ) (norm_withSeminorms 𝕜₂ F)
    (foo' ⟨C, h_norm⟩) x y hxy]
  simp [← hxy, ← H]

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ}

theorem opNorm_extendOfNorm_le (h_dense : DenseRange e) {C : ℝ} (hC : 0 ≤ C)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm e‖ ≤ C :=
  (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

end NormedField

end LinearMap

namespace LinearEquiv

section extend

variable [NormedField 𝕜] [NormedField 𝕜₂] -- generalize to `NormedDivisionRing` after PR
  [AddCommGroup E] [NormedAddCommGroup Eₗ] [AddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [NormedSpace 𝕜 Eₗ]
  [CompleteSpace Eₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

/-- Extension of a linear equivalence `f : E ≃ₛₗ[σ₁₂] F` to a continuous linear equivalence
`Eₗ ≃SL[σ₁₂] Fₗ`, where `E` and `F` are normed spaces and `Eₗ` and `Fₗ` are Banach spaces,
using dense maps `e₁ : E →ₗ[𝕜₁] Eₗ` and `e₂ : F →ₗ[𝕜₂] F₂` together with bounds
`‖e₂ (f x)‖ ≤ C * ‖e₁ x‖` for all `x : E` and `‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖` for all `x : F`. -/
def extend (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) :
    Eₗ ≃SL[σ₁₂] Fₗ where
  __ := (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    refine h_dense₁.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  right_inv := by
    refine h_dense₂.induction ?_ ?_
    · rintro _ ⟨_, rfl⟩
      simp [LinearMap.extendOfNorm_eq, h_dense₁, h_norm₁, h_dense₂, h_norm₂]
    · exact isClosed_eq (by simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      ContinuousLinearMap.coe_coe]; fun_prop) continuous_id
  continuous_invFun := ContinuousLinearMap.continuous _

theorem extend_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Eₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl

theorem extend_symm_apply (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Fₗ) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
theorem extend_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : E) :
    f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂ (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ h_norm₁ x

@[simp]
theorem extend_symm_eq (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : F) :
    (f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ h_norm₂).symm (e₂ x) = e₁ (f.symm x) :=
  LinearMap.extendOfNorm_eq h_dense₂ h_norm₂ x

theorem norm_extend_le (C : ℝ) (h_dense₁ : DenseRange e₁) (h_norm₁ : ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Eₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ ⟨C, h_norm₁⟩ h_dense₂ h_norm₂) x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₁ _ h_norm₁ _

theorem norm_extend_symm_le (C : ℝ) (h_dense₁ : DenseRange e₁)
    (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_dense₂ : DenseRange e₂)
    (h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Fₗ) :
    ‖(f.extend e₁ e₂ h_dense₁ h_norm₁ h_dense₂ ⟨C, h_norm₂⟩).symm x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le h_dense₂ _ h_norm₂ _

end extend

section extendOfIsometry

variable [NormedField 𝕜] [NormedField 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [CompleteSpace Eₗ]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

/-- Extend a densely defined operator that preserves the norm to a linear isometry equivalence. -/
def extendOfIsometry (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) :
    Eₗ ≃ₛₗᵢ[σ₁₂] Fₗ :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ := fun x ↦ by simpa using (h_norm (f.symm x)).symm
  { __ := f.extend e₁ e₂ h_dense₁ ⟨1, by simp [h_norm]⟩ h_dense₂ ⟨1, by simp [h_norm₂]⟩
    norm_map' := by
      refine h_dense₁.induction ?_ (isClosed_eq (by
        simp only [ContinuousLinearEquiv.coe_toLinearEquiv]; fun_prop) continuous_norm)
      rintro x ⟨y, rfl⟩
      convert! h_norm y
      apply LinearMap.extendOfNorm_eq h_dense₁ (by use 1; simp [h_norm]) }

theorem extendOfIsometry_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Eₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm) x =
    (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁ x := rfl

theorem extendOfIsometry_symm_apply (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : Fₗ) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm x =
    (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂ x := rfl

@[simp]
theorem extendOfIsometry_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : E) :
    f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x ↦ by simp [h_norm x]⟩ x

@[simp]
theorem extendOfIsometry_symm_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : F) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm (e₂ x) = e₁ (f.symm x) :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x ↦ by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x ↦ by simp [h_norm₂ x]⟩ x

end extendOfIsometry

end LinearEquiv
