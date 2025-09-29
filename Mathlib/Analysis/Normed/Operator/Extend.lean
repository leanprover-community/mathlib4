/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend from a dense subspace using `IsUniformInducing`
* `ContinuousLinearMap.extendOfNorm`: Extend from a continuous linear map that is a dense
injection into the domain and using a norm estimate.

-/

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section NormedRing

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ) (h_dense : DenseRange e)

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`. -/
def extend : Eₗ →SL[σ₁₂] F :=
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h_e h_dense f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h_e h_dense f.uniformContinuous
  { toFun := (h_e.isDenseInducing h_dense).extend f
    map_add' := by
      refine h_dense.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h_dense.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }

@[simp]
theorem extend_eq (x : E) : extend f e h_dense h_e (e x) = f x :=
  IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

theorem extend_unique (g : Eₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)

end NormedRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) (e : E →L[𝕜] Eₗ)

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : ℝ≥0} (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le :
    ‖f.extend e h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing‖ ≤ N * ‖f‖ := by
  -- Add `opNorm_le_of_dense`?
  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ ?_) fun x ↦ ?_)
  · cases le_total 0 N with
    | inl hN => exact mul_nonneg hN (norm_nonneg _)
    | inr hN =>
      have : Unique E := ⟨⟨0⟩, fun x ↦ norm_le_zero_iff.mp <|
        (h_e x).trans (mul_nonpos_of_nonpos_of_nonneg hN (norm_nonneg _))⟩
      obtain rfl : f = 0 := Subsingleton.elim ..
      simp
  · exact (cont _).norm
  · exact continuous_const.mul continuous_norm
  · rw [extend_eq]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap

namespace LinearMap

section LeftInverse

variable [DivisionRing 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

variable (f : E →ₗ[𝕜] F)

open scoped Classical in
/-- The left inverse of a `f : LinearMap`. -/
def leftInverse_aux : F →ₗ[𝕜] E :=
  if h_inj : LinearMap.ker f = ⊥ then
  Classical.choose (f.exists_leftInverse_of_injective h_inj)
  else 0

/-- If `f` is injective, then the left inverse composed with `f` is the identity. -/
@[simp]
theorem leftInverseLM_aux_apply (h_inj : LinearMap.ker f = ⊥) (x : E) :
    f.leftInverse_aux (f x) = x := by
  have := Classical.choose_spec (f.exists_leftInverse_of_injective h_inj)
  rw [LinearMap.ext_iff] at this
  simp only [leftInverse_aux, h_inj, ↓reduceDIte]
  exact this x

end LeftInverse

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Composition with the left inverse as a CLM.

This definition is only used to construct extensions of continuous linear maps and should not
be used outside of this file. -/
def compInv_aux :=
  if h : LinearMap.ker g = ⊥ ∧ ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖ then
  (f ∘ₛₗ (g.leftInverse_aux.domRestrict
    (LinearMap.range g))).mkContinuousOfExistsBound
  (by
    rcases h.2 with ⟨C, hC⟩
    use C
    rintro ⟨x, y, hxy⟩
    simp only [← hxy, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.domRestrict_apply, AddSubgroupClass.coe_norm]
    convert hC y
    apply g.leftInverseLM_aux_apply h.1)
  else 0

@[simp]
theorem compInv_aux_apply (h_inj : LinearMap.ker g = ⊥)
    (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖) (y : LinearMap.range g) :
    f.compInv_aux g y = (f ∘ₛₗ (g.leftInverse_aux.domRestrict
      (LinearMap.range g))) y := by
  simp [compInv_aux, h_inj, h_norm]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F` to `Fₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space,
using an injective dense embedding `e : E →L[𝕜] Fₗ` together with a bound `‖f x‖ ≤ C * ‖e x‖`
for all `x : E`. -/
def extendOfNorm : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e then
  ContinuousLinearMap.extend (f.compInv_aux e) (LinearMap.range e).subtypeL
    (by
      simp only [Submodule.coe_subtypeL', Submodule.coe_subtype, denseRange_subtype_val]
      exact h)
    isUniformEmbedding_subtype_val.isUniformInducing
  else 0

variable {f e}

theorem extendOfNorm_eq (h_inj : LinearMap.ker e = ⊥)
    (h_dense : DenseRange e) (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖) (x : E) :
    f.extendOfNorm e (e x) = f x := by
  simp only [extendOfNorm, h_dense, ↓reduceDIte]
  have := ContinuousLinearMap.extend_eq (f.compInv_aux e) (LinearMap.range e).subtypeL (by
    simp only [Submodule.coe_subtypeL', Submodule.coe_subtype, denseRange_subtype_val]
    exact h_dense)
    isUniformEmbedding_subtype_val.isUniformInducing
  convert this ⟨e x, LinearMap.mem_range_self e x⟩
  simp only [h_inj, h_norm, compInv_aux_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.domRestrict_apply]
  congr
  apply (e.leftInverseLM_aux_apply h_inj _).symm

theorem extendOfNorm_norm_le (h_inj : LinearMap.ker e = ⊥) (h_dense : DenseRange e) (C : ℝ)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : Eₗ) :
    ‖f.extendOfNorm e x‖ ≤ C * ‖x‖ := by
  have h_mem : ∀ (x : Eₗ) (hy : x ∈ (LinearMap.range e)), ‖extendOfNorm f e x‖ ≤ C * ‖x‖ := by
    rintro x ⟨y, hxy⟩
    rw [← hxy]
    convert h_norm y
    apply extendOfNorm_eq h_inj h_dense ⟨C, h_norm⟩
  have h_closed : IsClosed { x | ‖f.extendOfNorm e x‖ ≤ C * ‖x‖ } :=
    (isClosed_le (ContinuousLinearMap.cont _).norm (continuous_const.mul continuous_norm))
  exact h_dense.induction h_mem h_closed x

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [SeminormedAddCommGroup Eₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Eₗ]
  [AddCommGroup E] [Module 𝕜 E] [CompleteSpace F]

variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

theorem extendOfNorm_opNorm_le (h_inj : LinearMap.ker e = ⊥)
    (h_dense : DenseRange e) (C : ℝ)
    (hC : 0 ≤ C) (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm e‖ ≤ C :=
  (f.extendOfNorm e).opNorm_le_bound hC (extendOfNorm_norm_le h_inj h_dense C h_norm)

end NormedField

end LinearMap

namespace LinearEquiv

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [AddCommGroup E] [NormedAddCommGroup Eₗ] [AddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ] [Module 𝕜₂ F] [Module 𝕜₂ Fₗ] [IsBoundedSMul 𝕜₂ Fₗ]
  [CompleteSpace Eₗ] [CompleteSpace Fₗ]

variable (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)

def extend (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) :
    Eₗ ≃SL[σ₁₂] Fₗ where
  __ := (e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁
  invFun := (e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂
  left_inv := by
    apply h_dense1.induction (P := fun x => ((e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂)
      ((((e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁)) x) = x)
    · intro x ⟨y, hxy⟩
      rw [← hxy, LinearMap.extendOfNorm_eq h_inj1 h_dense1 h_norm1, LinearMap.coe_comp, coe_coe,
        Function.comp_apply, LinearMap.extendOfNorm_eq h_inj2 h_dense2 h_norm2, LinearMap.coe_comp,
        coe_coe, Function.comp_apply, symm_apply_apply]
    · refine isClosed_eq ?_ continuous_id
      exact (ContinuousLinearMap.cont _).comp (ContinuousLinearMap.cont _)
  right_inv := by
    apply h_dense2.induction (P := fun x => ((e₂ ∘ₛₗ f.toLinearMap).extendOfNorm e₁)
      ((((e₁ ∘ₛₗ f.symm.toLinearMap).extendOfNorm e₂)) x) = x)
    · intro x ⟨y, hxy⟩
      rw [← hxy, LinearMap.extendOfNorm_eq h_inj2 h_dense2 h_norm2, LinearMap.coe_comp, coe_coe,
        Function.comp_apply, LinearMap.extendOfNorm_eq h_inj1 h_dense1 h_norm1, LinearMap.coe_comp,
        coe_coe, Function.comp_apply, apply_symm_apply]
    · refine isClosed_eq ?_ continuous_id
      exact (ContinuousLinearMap.cont _).comp (ContinuousLinearMap.cont _)
  continuous_invFun := ContinuousLinearMap.continuous _

theorem extend_eq (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : E) :
    f.extend e₁ e₂ h_inj1 h_dense1 h_norm1 h_inj2 h_dense2 h_norm2 (e₁ x) = e₂ (f x) := by
  apply LinearMap.extendOfNorm_eq h_inj1 h_dense1 h_norm1

theorem extend_symm_eq (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : F) :
    (f.extend e₁ e₂ h_inj1 h_dense1 h_norm1 h_inj2 h_dense2 h_norm2).symm (e₂ x)
    = e₁ (f.symm x) := by
  apply LinearMap.extendOfNorm_eq h_inj2 h_dense2 h_norm2

theorem extend_norm_le (C : ℝ) (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Eₗ) :
    ‖(f.extend e₁ e₂ h_inj1 h_dense1 ⟨C, h_norm1⟩ h_inj2 h_dense2 h_norm2) x‖ ≤ C * ‖x‖ := by
  apply LinearMap.extendOfNorm_norm_le h_inj1 h_dense1
  convert h_norm1

theorem extend_symm_norm_le (C : ℝ) (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) (x : Fₗ) :
    ‖(f.extend e₁ e₂ h_inj1 h_dense1 h_norm1 h_inj2 h_dense2 ⟨C, h_norm2⟩).symm x‖ ≤ C * ‖x‖ := by
  apply LinearMap.extendOfNorm_norm_le h_inj2 h_dense2
  convert h_norm2

end LinearEquiv
