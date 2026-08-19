/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide several different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `LinearMap.extendOfNorm`: Extend `f : E →ₛₗ[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map and we have the norm estimate
  `‖f x‖ ≤ C * ‖e x‖` for all `x : E`.
* `LinearMap.extendOfIsometry`: Extend a linear map `f : E →ₛₗ[𝕜] F` between normed spaces to a
  linear isometry `Eₗ →ₗᵢ[𝕜] F` between Banach spaces with a dense map `e : E →ₗ[𝕜] Eₗ` together
  with the corresponding norm estimate.
* `LinearEquiv.extend`: Extend a linear equivalence between normed spaces to a continuous linear
  equivalence between Banach spaces with two dense maps `e₁` and `e₂` and the corresponding norm
  estimates.
* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
  `Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Banach spaces
  and `f` preserves the norm.
* `LinearIsometry.completion`: The linear isometric version of `UniformSpace.Completion.extension`.
* `LinearIsometry.fromCompletion`: The linear isometric version of `UniformSpace.Completion.map`.
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
  (f : E →SL[σ₁₂] F) {e : E →L[𝕜] Eₗ}

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : ℝ≥0} [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le (h_dense : DenseRange e) (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) :
    ‖f.extend e‖ ≤ N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · rw [extend_eq _ h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := by gcongr; exact h_e x
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Composition of a semilinear map `f` with the left inverse of a linear map `g` as a continuous
linear map provided that the norm estimate `‖f x‖ ≤ C * ‖g x‖` holds for all `x : E`. -/
def compLeftInverse : range g →SL[σ₁₂] F :=
  if h : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖ then
  (((LinearMap.ker g).liftQ f (by
    obtain ⟨C, h⟩ := h
    intro x hx
    specialize h x
    rw [hx] at h
    simpa using h)).comp
    g.quotKerEquivRange.symm.toLinearMap).mkContinuousOfExistsBound
  (by
    obtain ⟨C, h⟩ := h
    use C
    intro ⟨x, y, hxy⟩
    simpa [← hxy] using h y)
  else 0

theorem compLeftInverse_apply_of_bdd (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖)
    (x : E) (y : Eₗ) (hx : g x = y) :
    f.compLeftInverse g ⟨y, ⟨x, hx⟩⟩ = f x := by
  simp [compLeftInverse, h_norm, ← hx]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

/-- Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`. -/
def extendOfNorm : Eₗ →SL[σ₁₂] F := (f.compLeftInverse e).extend (LinearMap.range e).subtypeL

variable {f e}

theorem extendOfNorm_eq (h_dense : DenseRange e) (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖)
    (x : E) : f.extendOfNorm e (e x) = f x := by
  have := (f.compLeftInverse e).extend_eq (e := (LinearMap.range e).subtypeL)
    (by simpa using! h_dense) isUniformEmbedding_subtype_val.isUniformInducing
  convert! this ⟨e x, LinearMap.mem_range_self e x⟩
  exact (compLeftInverse_apply_of_bdd _ _ h_norm _ _ rfl).symm

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
  rw [compLeftInverse_apply_of_bdd _ _ ⟨C, h_norm⟩ x y hxy]
  simp [← hxy, ← H]

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ}

theorem opNorm_extendOfNorm_le (h_dense : DenseRange e) {C : ℝ} (hC : 0 ≤ C)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm e‖ ≤ C :=
  (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)

end NormedField

section extendOfIsometry

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [NormedAddCommGroup F] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [CompleteSpace F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {e : E →ₗ[𝕜] Eₗ}

/-- Extend a linear map `f : E →ₛₗ[σ₁₂] F` to a linear isometry `Eₗ →ₛₗᵢ[σ₁₂] F` between
Banach spaces, using a dense linear map `e : E →ₗ[𝕜] Eₗ` together with the norm equality
`‖f x‖ = ‖e x‖` for all `x : E`. -/
def extendOfIsometry (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) :
    Eₗ →ₛₗᵢ[σ₁₂] F where
  toLinearMap := f.extendOfNorm e
  norm_map' := by
    refine h_dense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro x ⟨y, rfl⟩
    norm_cast
    rw [LinearMap.extendOfNorm_eq h_dense (by use 1; simp [h_norm]), h_norm y]

theorem extendOfIsometry_apply (h_dense : DenseRange e)
    (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : Eₗ) :
    f.extendOfIsometry h_dense h_norm x = f.extendOfNorm e x := rfl

@[simp]
theorem extendOfIsometry_eq (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq h_dense ⟨1, fun x ↦ by simp [h_norm x]⟩ x

theorem toContinuousLinearMap_extendOfIsometry (h_dense : DenseRange e)
    (h_norm : ∀ x, ‖f x‖ = ‖e x‖) :
    (f.extendOfIsometry h_dense h_norm).toContinuousLinearMap = f.extendOfNorm e := by rfl

theorem extendOfIsometry_unique (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖)
    (g : Eₗ →ₛₗᵢ[σ₁₂] F) (H : g.toLinearMap.comp e = f) :
    f.extendOfIsometry h_dense h_norm = g := by
  simp [extendOfIsometry, extendOfNorm_unique h_dense 1 (by simp [h_norm])
    g.toContinuousLinearMap H]

end extendOfIsometry

end LinearMap

namespace LinearEquiv

section extend

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [NormedAddCommGroup Eₗ] [AddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ] [Module 𝕜₂ F] [Module 𝕜₂ Fₗ] [IsBoundedSMul 𝕜₂ Fₗ]
  [CompleteSpace Eₗ] [CompleteSpace Fₗ]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

/-- Extension of a linear equivalence `f : E ≃ₛₗ[σ₁₂] F` to a continuous linear equivalence
`Eₗ ≃SL[σ₁₂] Fₗ`, where `E` and `F` are normed spaces and `Eₗ` and `Fₗ` are Banach spaces,
using dense maps `e₁ : E →ₗ[𝕜₁] Eₗ` and `e₂ : F →ₗ[𝕜₂] Fₗ` together with bounds
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

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
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

namespace LinearIsometry

open UniformSpace

variable {R R₂ : Type*} [Semiring R] [Semiring R₂] [SeminormedAddCommGroup E] [Module R E]
  [IsUniformAddGroup E] [UniformContinuousConstSMul R E] [NormedAddCommGroup F] [Module R₂ F]
  {σ₁₂ : R →+* R₂} (f : E →ₛₗᵢ[σ₁₂] F)

section fromCompletion

variable [PseudoMetricSpace R₂] [CompleteSpace F] [IsBoundedSMul R₂ F]

/-- Extend a linear isometry `f : E →ₛₗᵢ[σ₁₂] F` to a linear isometry
`UniformSpace.Completion E →ₛₗᵢ[σ₁₂] F` between the completions of `E` and a complete space
`F`, via the canonical completion embedding. This is the linear isometric version of
`UniformSpace.Completion.extension`. -/
def fromCompletion : UniformSpace.Completion E →ₛₗᵢ[σ₁₂] F where
  __ := f.toContinuousLinearMap.fromCompletion
  norm_map' := f.isometry.completion_extension.norm_map_of_map_zero
    f.toContinuousLinearMap.fromCompletion.map_zero

theorem fromCompletion_apply_coe (x : E) : f.fromCompletion x = f x :=
  ContinuousLinearMap.fromCompletion_apply_coe f.toContinuousLinearMap x

@[simp low]
theorem coe_fromCompletion : f.fromCompletion = Completion.extension f := by
  refine Completion.ext f.fromCompletion.continuous Completion.continuous_extension fun a => ?_
  rw [fromCompletion_apply_coe, Completion.extension_coe f.isometry.uniformContinuous]

@[simp]
theorem toContinuousLinearMap_fromCompletion :
    f.fromCompletion.toContinuousLinearMap = f.toContinuousLinearMap.fromCompletion := rfl

@[simp]
theorem toAddMonoidHom_fromCompletion (f : E →ₛₗᵢ[σ₁₂] F) :
    f.fromCompletion.toAddMonoidHom = f.toAddMonoidHom.extension f.continuous := rfl

end fromCompletion

section completion

variable [UniformContinuousConstSMul R₂ F]

/-- Extend a linear isometry `f : E →ₛₗᵢ[σ₁₂] F` to a linear isometry
`UniformSpace.Completion E →ₛₗᵢ[σ₁₂] UniformSpace.Completion F` between the completions of `E` and
`F`, via the canonical completion embeddings. This is the linear isometric version of
`UniformSpace.Completion.map`. -/
def completion : UniformSpace.Completion E →ₛₗᵢ[σ₁₂] UniformSpace.Completion F where
  __ := f.toContinuousLinearMap.completion
  norm_map' e := Completion.induction_on e
      (isClosed_eq (f.toContinuousLinearMap.completion.continuous.norm) continuous_norm) <| by
    simp [UniformSpace.Completion.norm_coe]

theorem completion_apply_coe (x : E) : f.completion x = f x :=
  ContinuousLinearMap.completion_apply_coe f.toContinuousLinearMap x

@[simp low]
theorem coe_completion : f.completion = Completion.map f := by
  refine Completion.ext f.completion.continuous Completion.continuous_map fun a => ?_
  rw [completion_apply_coe, Completion.map_coe f.isometry.uniformContinuous]

@[simp]
theorem toContinuousLinearMap_completion :
    f.completion.toContinuousLinearMap = f.toContinuousLinearMap.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq f.completion.continuous f.toContinuousLinearMap.completion.continuous
  | ih x => congr

@[simp]
theorem toAddMonoidHom_completion :
    f.completion.toAddMonoidHom = f.toAddMonoidHom.completion f.continuous := rfl

end completion

end LinearIsometry
