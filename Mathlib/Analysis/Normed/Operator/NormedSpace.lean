/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Operator norm for maps on normed spaces

This file contains statements about operator norm for which it really matters that the
underlying space has a norm (rather than just a seminorm).
-/

@[expose] public section

suppress_compilation

open Topology
open scoped NNReal

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G : Type*}

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f : E →SL[σ₁₂] F)

namespace LinearIsometry
section
variable [NontrivialTopology E] [RingHomIsometric σ₁₂]

@[simp] lemma norm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ = 1 :=
  f.toContinuousLinearMap.homothety_norm <| by simp

@[simp] lemma nnnorm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖₊ = 1 :=
  Subtype.ext f.norm_toContinuousLinearMap

@[simp] lemma enorm_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ₑ = 1 :=
  congrArg _ f.nnnorm_toContinuousLinearMap

end

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm. -/
lemma norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F →ₛₗᵢ[σ₂₃] G)
    {g : E →SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  (f.toContinuousLinearMap.comp g).opNorm_ext g fun x ↦ by simp

/-- Composing on the left with a linear isometry gives a linear isometry between spaces of
continuous linear maps. -/
def postcomp [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] (E →SL[σ₁₃] G) where
  toFun f := a.toContinuousLinearMap.comp f
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := by simp [a.norm_toContinuousLinearMap_comp]

end LinearIsometry

namespace LinearIsometryEquiv
variable [NontrivialTopology E] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

@[simp] lemma norm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 :=
  e.toLinearIsometry.norm_toContinuousLinearMap

@[simp] lemma nnnorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖₊ = 1 :=
  e.toLinearIsometry.nnnorm_toContinuousLinearMap

@[simp] lemma enorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ₑ = 1 :=
  e.toLinearIsometry.enorm_toContinuousLinearMap

end LinearIsometryEquiv
end SeminormedAddCommGroup

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f : E →SL[σ₁₂] F)

namespace LinearMap

theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

/-- `LinearMap.bound_of_ball_bound'` is a version of this lemma over a field satisfying `RCLike`
that produces a concrete bound.
-/
theorem bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] Fₗ)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ‖f z‖ ≤ c) : ∃ C, ∀ z : E, ‖f z‖ ≤ C * ‖z‖ := by
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial 𝕜 _
  use c * (‖k‖ / r)
  intro z
  refine bound_of_shell _ r_pos hk (fun x hko hxo => ?_) _
  calc
    ‖f x‖ ≤ c := h _ (mem_ball_zero_iff.mpr hxo)
    _ ≤ c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff₀ (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko

theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 := Specializes.eq (specializes_iff_pure.2 <|
      ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ ≤ ‖c ^ n‖⁻¹ * 1 := by gcongr; exact (hε _ hlt).le
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]

end LinearMap

namespace ContinuousLinearMap

open Set Real

/-- An operator is zero iff its norm vanishes. -/
theorem opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

/-- Continuous linear maps themselves form a normed space with respect to the operator norm. -/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance toNormedRing : NormedRing (E →L[𝕜] E) where
  __ := toNormedAddCommGroup
  __ := toSeminormedRing

/-- If a continuous linear map is a topology embedding, then it is expands the distances
by a positive factor. -/
theorem antilipschitz_of_isEmbedding (f : E →L[𝕜] Fₗ) (hf : IsEmbedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge

end ContinuousLinearMap

end

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃}

variable {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₂'] {F' : Type*} [NormedAddCommGroup F']
  [NormedSpace 𝕜₂' F'] {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂'' : 𝕜₂ →+* 𝕜₂'} {σ₂₃' : 𝕜₂' →+* 𝕜₃}
  [RingHomInvPair σ₂' σ₂''] [RingHomInvPair σ₂'' σ₂'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomCompTriple σ₂'' σ₂₃' σ₂₃] [RingHomIsometric σ₂₃] [RingHomIsometric σ₂']
  [RingHomIsometric σ₂''] [RingHomIsometric σ₂₃']

@[simp]
theorem norm_smulRightL (c : StrongDual 𝕜 E) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply

lemma norm_smulRightL_le : ‖smulRightL 𝕜 E Fₗ‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end ContinuousLinearMap

/-! ### Composition with isometries -/

namespace ContinuousLinearMap
variable {𝕜₁ 𝕜₂ 𝕜₃ E F G : Type*}
  [NontriviallyNormedField 𝕜₁] [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
  [NontriviallyNormedField 𝕜₂] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  [NontriviallyNormedField 𝕜₃] [NormedAddCommGroup G] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : 𝕜₁ →+* 𝕜₃} [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff, ← e.forall_congr_right]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r ↦ by simp [opNNNorm_le_iff]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F →SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E →SL[σ₁₂] F)‖ = ‖f‖ :=
  congr($(opNNNorm_comp_linearIsometryEquiv f e))

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E →SL[σ₁₂] F) : ‖(e : F →SL[σ₂₃] G).comp f‖ = ‖f‖ :=
  congr($(opNNNorm_linearIsometryEquiv_comp e f))

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖₊ = ‖f‖₊ :=
  opNNNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNNNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖₊ = ‖f‖₊ :=
  opNNNorm_linearIsometryEquiv_comp ..

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_mul_linearIsometryEquiv (f : E →L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖ = ‖f‖ :=
  opNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
lemma opNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E →L[𝕜] E) : ‖e * f‖ = ‖f‖ :=
  opNorm_linearIsometryEquiv_comp ..

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F →SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv

theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 ≤ ‖(e : E →SL[σ₁₂] F)‖ * ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rw [mul_comm]
  convert! (e.symm : F →SL[σ₂₁] E).opNorm_comp_le (e : E →SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]

theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E →SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)

theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos

theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos

theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e

variable (𝕜)

@[simp]
theorem coord_norm (x : E) (h : x ≠ 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  haveI : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _

end

end ContinuousLinearEquiv

end Normed

/-- A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
def IsCoercive [SeminormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u

section Equicontinuous

variable {ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] (f : ι → E →SL[σ₁₂] F)

/-- Equivalent characterizations for equicontinuity of a family of continuous linear maps
between normed spaces. See also `WithSeminorms.equicontinuous_TFAE` for similar characterizations
between spaces satisfying `WithSeminorms`. -/
protected theorem NormedSpace.equicontinuous_TFAE : List.TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∃ C, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C ≥ 0, ∀ i x, ‖f i x‖ ≤ C * ‖x‖,
      ∃ C, ∀ i, ‖f i‖ ≤ C,
      ∃ C ≥ 0, ∀ i, ‖f i‖ ≤ C,
      BddAbove (Set.range (‖f ·‖)),
      (⨆ i, (‖f i‖₊ : ENNReal)) < ⊤ ] := by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 → 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1 := fun H ↦ H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we just have to use a lot of rewriting
  -- and `congr` lemmas
  tfae_have 4 ↔ 5 := by
    rw [exists_ge_and_iff_exists]
    exact fun C₁ C₂ hC ↦ forall₂_imp fun i x ↦ le_trans' <| by gcongr
  tfae_have 5 ↔ 7 := by
    refine exists_congr (fun C ↦ and_congr_right fun hC ↦ forall_congr' fun i ↦ ?_)
    rw [ContinuousLinearMap.opNorm_le_iff hC]
  tfae_have 7 ↔ 8 := by
    simp_rw [bddAbove_iff_exists_ge (0 : ℝ), Set.forall_mem_range]
  tfae_have 6 ↔ 8 := by
    simp_rw [bddAbove_def, Set.forall_mem_range]
  tfae_have 8 ↔ 9 := by
    rw [ENNReal.iSup_coe_lt_top, ← NNReal.bddAbove_coe, ← Set.range_comp]
    rfl
  -- `3 ↔ 4` is the interesting part of the result. It is essentially a combination of
  -- `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` which turns
  -- equicontinuity into existence of some continuous seminorm and
  -- `Seminorm.bound_of_continuous_normedSpace` which characterize such seminorms.
  tfae_have 3 ↔ 4 := by
    refine ((norm_withSeminorms 𝕜₂ F).uniformEquicontinuous_iff_exists_continuous_seminorm _).trans
      ?_
    rw [forall_const]
    constructor
    · intro ⟨p, hp, hpf⟩
      rcases p.bound_of_continuous_normedSpace hp with ⟨C, -, hC⟩
      exact ⟨C, fun i x ↦ (hpf i x).trans (hC x)⟩
    · intro ⟨C, hC⟩
      refine ⟨C.toNNReal • normSeminorm 𝕜 E,
        ((norm_withSeminorms 𝕜 E).continuous_seminorm 0).const_smul C.toNNReal, fun i x ↦ ?_⟩
      exact (hC i x).trans (mul_le_mul_of_nonneg_right (C.le_coe_toNNReal) (norm_nonneg x))
  tfae_finish

end Equicontinuous

section single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : ι → Type*)

/-- The injection `x ↦ Pi.single i x` as a linear isometry. -/
protected def LinearIsometry.single [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (i : ι) : E i →ₗᵢ[𝕜] Π j, E j :=
  (LinearMap.single 𝕜 E i).toLinearIsometry (.single i)

lemma ContinuousLinearMap.norm_single_le_one [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (i : ι) :
    ‖ContinuousLinearMap.single 𝕜 E i‖ ≤ 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap_le

lemma ContinuousLinearMap.norm_single [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] (i : ι) [NontrivialTopology (E i)] :
    ‖ContinuousLinearMap.single 𝕜 E i‖ = 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap

end single

section inl_inr

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E F : Type*)

/-- The injection `x ↦ LinearMap.inl E F x` as a linear isometry. -/
protected def LinearIsometry.inl [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : E →ₗᵢ[𝕜] E × F :=
  (LinearMap.inl 𝕜 E F).toLinearIsometry .inl

@[simp]
lemma LinearIsometry.inl_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (x : E) :
    LinearIsometry.inl 𝕜 E F x = (x, 0) := rfl

/-- The injection `x ↦ LinearMap.inr E F x` as a linear isometry. -/
protected def LinearIsometry.inr [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : F →ₗᵢ[𝕜] E × F :=
  (LinearMap.inr 𝕜 E F).toLinearIsometry .inr

@[simp]
lemma LinearIsometry.inr_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (y : F) :
    LinearIsometry.inr 𝕜 E F y = (0, y) := rfl

lemma ContinuousLinearMap.norm_inl_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ ≤ 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap_le

lemma ContinuousLinearMap.norm_inr_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ ≤ 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap_le

lemma ContinuousLinearMap.norm_inl [SeminormedAddCommGroup E] [NontrivialTopology E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ = 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap

lemma ContinuousLinearMap.norm_inr [SeminormedAddCommGroup E] [NontrivialTopology E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NontrivialTopology F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ = 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap

end inl_inr
