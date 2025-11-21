/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!

# Extension of continuous linear maps on Banach spaces

In this file we provide two different ways to extend a continuous linear map defined on a dense
subspace to the entire Banach space.

* `ContinuousLinearMap.extend`: Extend from a dense subspace using `IsUniformInducing`
* `ContinuousLinearMap.extendOfNorm`: Extend from a continuous linear map that is a dense
injection into the domain and using a norm estimate.

-/

@[expose] public section

suppress_compilation

open scoped NNReal

variable {𝕜 𝕜₂ E Eₗ F Fₗ : Type*}

namespace ContinuousLinearMap

section Extend

section Ring

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

open scoped Classical in
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Eₗ`. -/
def extend : Eₗ →SL[σ₁₂] F :=
  if h : DenseRange e ∧ IsUniformInducing e then
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h.2 h.1 f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h.2 h.1 f.uniformContinuous
  { toFun := (h.2.isDenseInducing h.1).extend f
    map_add' := by
      refine h.1.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h.1.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }
  else 0

variable {e}

@[simp]
theorem extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) :
    extend f e (e x) = f x := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte, coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

theorem extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e) (g : Eₗ →SL[σ₁₂] F)
    (H : g.comp e = f) : extend f e = g := by
  simp only [extend, h_dense, h_e, and_self, ↓reduceDIte]
  exact ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    extend (0 : E →SL[σ₁₂] F) e = 0 :=
  extend_unique _ h_dense h_e  _ (zero_comp _)

end Ring

section NormedField

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [NormedAddCommGroup E] [NormedAddCommGroup Eₗ] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₂ Fₗ] [CompleteSpace F]
  (f g : E →SL[σ₁₂] F) {e : E →L[𝕜] Eₗ}

variable (h_dense : DenseRange e) (h_e : IsUniformInducing e)

variable {N : ℝ≥0} [RingHomIsometric σ₁₂]

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le (h_dense : DenseRange e) (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) :
    ‖f.extend e‖ ≤ N * ‖f‖ := by
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
  · rw [extend_eq _ h_dense (isUniformEmbedding_of_bound _ h_e).isUniformInducing]
    calc
      ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
      _ ≤ ‖f‖ * (N * ‖e x‖) := mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
      _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]


end NormedField

end Extend

end ContinuousLinearMap
