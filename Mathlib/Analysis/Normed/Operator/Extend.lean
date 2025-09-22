/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
import Mathlib.Analysis.Normed.Operator.Basic

-- (#1649) was original extend (Zhouhang Zhou, 2019)

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E F Fₗ : Type*}

namespace LinearMap

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

end LinearMap

namespace ContinuousLinearMap

section Extend

section NormedRing

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Fₗ] [UniformSpace Fₗ] [ContinuousAdd Fₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Fₗ]
  [ContinuousConstSMul 𝕜 Fₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Fₗ) (h_dense : DenseRange e)

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Fₗ`. -/
def extend : Fₗ →SL[σ₁₂] F :=
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

theorem extend_unique (g : Fₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)

end NormedRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ]
  [NormedSpace 𝕜 E] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) (e : E →L[𝕜] Fₗ)

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

section compInv

variable [DivisionRing 𝕜] [DivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [TopologicalSpace E] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Fₗ]

variable (f : E →SL[σ₁₂] F) (g : E →L[𝕜] Fₗ)

open scoped Classical in
/-- Composition with the left inverse as a CLM.

This definition is only used to construct extensions of continuous linear maps and should not
be used outside of this file. -/
def compInv_aux :=
  if h : LinearMap.ker g = ⊥ ∧ ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖ then
  (f.toLinearMap ∘ₛₗ (g.toLinearMap.leftInverse_aux.domRestrict
    (LinearMap.range g))).mkContinuousOfExistsBound
  (by
    rcases h.2 with ⟨C, hC⟩
    use C
    rintro ⟨x, y, hxy⟩
    simp only [← hxy, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      LinearMap.domRestrict_apply, AddSubgroupClass.coe_norm]
    convert hC y
    apply g.toLinearMap.leftInverseLM_aux_apply h.1)
  else 0

@[simp]
theorem compInv_aux_apply (h_inj : LinearMap.ker g = ⊥)
    (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖g x‖) (y : LinearMap.range g) :
    compInv_aux f g y = (f.toLinearMap ∘ₛₗ (g.toLinearMap.leftInverse_aux.domRestrict
      (LinearMap.range g))) y := by
  simp [compInv_aux, h_inj, h_norm]

end compInv

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Fₗ] [IsBoundedSMul 𝕜 Fₗ]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [CompleteSpace F]

variable (f : E →SL[σ₁₂] F) (e : E →L[𝕜] Fₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F` to `Fₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space,
using an injective dense embedding `e : E →L[𝕜] Fₗ` together with a bound `‖f x‖ ≤ C * ‖e x‖`
for all `x : E`. -/
def extend_of_injCLM : Fₗ →SL[σ₁₂] F :=
  if h : DenseRange e then
  ContinuousLinearMap.extend (compInv_aux f e) (LinearMap.range e).subtypeL (by
    simp only [Submodule.coe_subtypeL', Submodule.coe_subtype, denseRange_subtype_val]
    exact h) isUniformEmbedding_subtype_val.isUniformInducing
  else 0

variable {f e}

theorem extend_of_injCLM_eq (h_inj : LinearMap.ker e = ⊥) (h_dense : DenseRange e)
    (h_norm : ∃ (C : ℝ), ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : E) :
    f.extend_of_injCLM e (e x) = f x := by
  simp only [extend_of_injCLM, h_dense, ↓reduceDIte]
  have := ContinuousLinearMap.extend_eq (f.compInv_aux e) (LinearMap.range e).subtypeL
    (by
    simp only [Submodule.coe_subtypeL', Submodule.coe_subtype, denseRange_subtype_val]
    exact h_dense)
    isUniformEmbedding_subtype_val.isUniformInducing
  convert this ⟨e x, LinearMap.mem_range_self e x⟩
  simp only [h_inj, h_norm, compInv_aux_apply, LinearMap.coe_comp, coe_coe, Function.comp_apply,
    LinearMap.domRestrict_apply]
  congr
  apply (e.leftInverseLM_aux_apply h_inj _).symm

theorem extend_of_injCLM_norm_le (h_inj : LinearMap.ker e = ⊥) (h_dense : DenseRange e) (C : ℝ)
    (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) (x : Fₗ) :
    ‖f.extend_of_injCLM e x‖ ≤ C * ‖x‖ := by
  have h_mem : ∀ (x : Fₗ) (hy : x ∈ (LinearMap.range e)), ‖f.extend_of_injCLM e x‖ ≤ C * ‖x‖ := by
    rintro x ⟨y, hxy⟩
    rw [← hxy]
    convert h_norm y
    apply extend_of_injCLM_eq h_inj h_dense ⟨C, h_norm⟩
  have h_closed : IsClosed { x | ‖f.extend_of_injCLM e x‖ ≤ C * ‖x‖ } :=
    (isClosed_le (ContinuousLinearMap.cont _).norm (continuous_const.mul continuous_norm))
  exact h_dense.induction (P := fun y => ‖f.extend_of_injCLM e y‖ ≤ C * ‖y‖) h_mem h_closed x

end NormedDivisionRing

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [CompleteSpace F]

variable (f : E →SL[σ₁₂] F) (e : E →L[𝕜] Fₗ)

theorem extend_of_injCLM_opNorm_le (h_inj : LinearMap.ker e = ⊥) (h_dense : DenseRange e) (C : ℝ)
    (hC : 0 ≤ C) (h_norm : ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) : ‖f.extend_of_injCLM e‖ ≤ C :=
  (f.extend_of_injCLM e).opNorm_le_bound hC (extend_of_injCLM_norm_le h_inj h_dense C h_norm)

end NormedField

end ContinuousLinearMap
