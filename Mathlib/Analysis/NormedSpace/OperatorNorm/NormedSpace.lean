/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm
import Mathlib.Analysis.NormedSpace.Span

/-!
# Operator norm for maps on normed spaces

This file contains statements about operator norm for which it really matters that the
underlying space has a norm (rather than just a seminorm).
-/

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped Classical NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}


section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)

namespace LinearMap

theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)
#align linear_map.bound_of_shell LinearMap.bound_of_shell

/-- `LinearMap.bound_of_ball_bound'` is a version of this lemma over a field satisfying `RCLike`
that produces a concrete bound.
-/
theorem bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] Fₗ)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ‖f z‖ ≤ c) : ∃ C, ∀ z : E, ‖f z‖ ≤ C * ‖z‖ := by
  cases' @NontriviallyNormedField.non_trivial 𝕜 _ with k hk
  use c * (‖k‖ / r)
  intro z
  refine' bound_of_shell _ r_pos hk (fun x hko hxo => _) _
  calc
    ‖f x‖ ≤ c := h _ (mem_ball_zero_iff.mpr hxo)
    _ ≤ c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko
#align linear_map.bound_of_ball_bound LinearMap.bound_of_ball_bound

theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => _⟩
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
    _ ≤ ‖c ^ n‖⁻¹ * 1 := (mul_le_mul_of_nonneg_left (hε _ hlt).le (inv_nonneg.2 (norm_nonneg _)))
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]
#align linear_map.antilipschitz_of_comap_nhds_le LinearMap.antilipschitz_of_comap_nhds_le

end LinearMap

namespace ContinuousLinearMap

section OpNorm

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
#align continuous_linear_map.op_norm_zero_iff ContinuousLinearMap.opNorm_zero_iff

@[deprecated] alias op_norm_zero_iff := opNorm_zero_iff -- deprecated on 2024-02-02

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem norm_id [Nontrivial E] : ‖id 𝕜 E‖ = 1 := by
  apply norm_id_of_nontrivial_seminorm
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩
#align continuous_linear_map.norm_id ContinuousLinearMap.norm_id

@[simp]
lemma nnnorm_id [Nontrivial E] : ‖id 𝕜 E‖₊ = 1 := NNReal.eq norm_id

instance normOneClass [Nontrivial E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩
#align continuous_linear_map.norm_one_class ContinuousLinearMap.normOneClass

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp
#align continuous_linear_map.to_normed_add_comm_group ContinuousLinearMap.toNormedAddCommGroup

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance toNormedRing : NormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedAddCommGroup, ContinuousLinearMap.toSemiNormedRing with }
#align continuous_linear_map.to_normed_ring ContinuousLinearMap.toNormedRing

variable {f}

theorem homothety_norm [RingHomIsometric σ₁₂] [Nontrivial E] (f : E →SL[σ₁₂] F) {a : ℝ}
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a := by
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  rw [← norm_pos_iff] at hx
  have ha : 0 ≤ a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_right] using f.le_opNorm x
#align continuous_linear_map.homothety_norm ContinuousLinearMap.homothety_norm

variable (f)

/-- If a continuous linear map is a topology embedding, then it is expands the distances
by a positive factor. -/
theorem antilipschitz_of_embedding (f : E →L[𝕜] Fₗ) (hf : Embedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge
#align continuous_linear_map.antilipschitz_of_embedding ContinuousLinearMap.antilipschitz_of_embedding

end OpNorm

end ContinuousLinearMap

namespace LinearIsometry

@[simp]
theorem norm_toContinuousLinearMap [Nontrivial E] [RingHomIsometric σ₁₂] (f : E →ₛₗᵢ[σ₁₂] F) :
    ‖f.toContinuousLinearMap‖ = 1 :=
  f.toContinuousLinearMap.homothety_norm <| by simp
#align linear_isometry.norm_to_continuous_linear_map LinearIsometry.norm_toContinuousLinearMap

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm. -/
theorem norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F →ₛₗᵢ[σ₂₃] G)
    {g : E →SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  opNorm_ext (f.toContinuousLinearMap.comp g) g fun x => by
    simp only [norm_map, coe_toContinuousLinearMap, coe_comp', Function.comp_apply]
#align linear_isometry.norm_to_continuous_linear_map_comp LinearIsometry.norm_toContinuousLinearMap_comp

end LinearIsometry

end

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

variable {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₂'] {F' : Type*} [NormedAddCommGroup F']
  [NormedSpace 𝕜₂' F'] {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂'' : 𝕜₂ →+* 𝕜₂'} {σ₂₃' : 𝕜₂' →+* 𝕜₃}
  [RingHomInvPair σ₂' σ₂''] [RingHomInvPair σ₂'' σ₂'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomCompTriple σ₂'' σ₂₃' σ₂₃] [RingHomIsometric σ₂₃] [RingHomIsometric σ₂']
  [RingHomIsometric σ₂''] [RingHomIsometric σ₂₃']

/-- Precomposition with a linear isometry preserves the operator norm. -/
theorem opNorm_comp_linearIsometryEquiv (f : F →SL[σ₂₃] G) (g : F' ≃ₛₗᵢ[σ₂'] F) :
    ‖f.comp g.toLinearIsometry.toContinuousLinearMap‖ = ‖f‖ := by
  cases subsingleton_or_nontrivial F'
  · haveI := g.symm.toLinearEquiv.toEquiv.subsingleton
    simp
  refine' le_antisymm _ _
  · convert f.opNorm_comp_le g.toLinearIsometry.toContinuousLinearMap
    simp [g.toLinearIsometry.norm_toContinuousLinearMap]
  · convert (f.comp g.toLinearIsometry.toContinuousLinearMap).opNorm_comp_le
        g.symm.toLinearIsometry.toContinuousLinearMap
    · ext
      simp
    haveI := g.symm.surjective.nontrivial
    simp [g.symm.toLinearIsometry.norm_toContinuousLinearMap]
#align continuous_linear_map.op_norm_comp_linear_isometry_equiv ContinuousLinearMap.opNorm_comp_linearIsometryEquiv

@[deprecated] -- deprecated on 2024-02-02
alias op_norm_comp_linearIsometryEquiv := opNorm_comp_linearIsometryEquiv

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
theorem norm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine' le_antisymm _ _
  · refine' opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => _
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := mul_le_mul_of_nonneg_right (le_opNorm _ _) (norm_nonneg _)
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · by_cases h : f = 0
    · simp [h]
    · have : 0 < ‖f‖ := norm_pos_iff.2 h
      rw [← le_div_iff this]
      refine' opNorm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) fun x => _
      rw [div_mul_eq_mul_div, le_div_iff this]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ ≤ ‖smulRight c f‖ * ‖x‖ := le_opNorm _ _
#align continuous_linear_map.norm_smul_right_apply ContinuousLinearMap.norm_smulRight_apply

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
theorem nnnorm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f
#align continuous_linear_map.nnnorm_smul_right_apply ContinuousLinearMap.nnnorm_smulRight_apply

variable (𝕜 E Fₗ)

set_option linter.uppercaseLean3 false

/-- `ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : E →L[𝕜] 𝕜) (f : F) (x : E) = c x • f`. -/
def smulRightL : (E →L[𝕜] 𝕜) →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        dsimp
        rw [smul_smul] }
    1 fun c x => by
      simp only [coe_smulRightₗ, one_mul, norm_smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk,
        le_refl]
#align continuous_linear_map.smul_rightL ContinuousLinearMap.smulRightL

variable {𝕜 E Fₗ}

@[simp]
theorem norm_smulRightL_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRightL 𝕜 E Fₗ c f‖ = ‖c‖ * ‖f‖ :=
  norm_smulRight_apply c f
#align continuous_linear_map.norm_smul_rightL_apply ContinuousLinearMap.norm_smulRightL_apply

@[simp]
theorem norm_smulRightL (c : E →L[𝕜] 𝕜) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply
#align continuous_linear_map.norm_smul_rightL ContinuousLinearMap.norm_smulRightL

variable (𝕜 E Fₗ) in
/-- An auxiliary instance to be able to just state the fact that the norm of `smulRightL` makes
sense. This shouldn't be needed. See lean4#3927. -/
def seminormedAddCommGroup_aux_for_smulRightL :
    SeminormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ) :=
  toSeminormedAddCommGroup (F := Fₗ →L[𝕜] E →L[𝕜] Fₗ) (𝕜 := 𝕜) (σ₁₂ := RingHom.id 𝕜)

lemma norm_smulRightL_le :
    letI := seminormedAddCommGroup_aux_for_smulRightL 𝕜 E Fₗ
    ‖smulRightL 𝕜 E Fₗ‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}

theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap
set_option linter.uppercaseLean3 false in
#align submodule.norm_subtypeL Submodule.norm_subtypeL

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F →SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv
#align continuous_linear_equiv.antilipschitz ContinuousLinearEquiv.antilipschitz

theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 ≤ ‖(e : E →SL[σ₁₂] F)‖ * ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rw [mul_comm]
  convert (e.symm : F →SL[σ₂₁] E).opNorm_comp_le (e : E →SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]
#align continuous_linear_equiv.one_le_norm_mul_norm_symm ContinuousLinearEquiv.one_le_norm_mul_norm_symm

theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E →SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_pos ContinuousLinearEquiv.norm_pos

theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_symm_pos ContinuousLinearEquiv.norm_symm_pos

theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos
#align continuous_linear_equiv.nnnorm_symm_pos ContinuousLinearEquiv.nnnorm_symm_pos

theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖ := by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos
#align continuous_linear_equiv.subsingleton_or_norm_symm_pos ContinuousLinearEquiv.subsingleton_or_norm_symm_pos

theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e
#align continuous_linear_equiv.subsingleton_or_nnnorm_symm_pos ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos

variable (𝕜)

@[simp]
theorem coord_norm (x : E) (h : x ≠ 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  haveI : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _
#align continuous_linear_equiv.coord_norm ContinuousLinearEquiv.coord_norm

end

end ContinuousLinearEquiv

end Normed

/-- A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
def IsCoercive [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u
#align is_coercive IsCoercive

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
  tfae_have 1 → 3
  · exact uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2
  · exact UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1
  · exact fun H ↦ H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we just have to use a lot of rewriting
  -- and `congr` lemmas
  tfae_have 4 ↔ 5
  · rw [exists_ge_and_iff_exists]
    exact fun C₁ C₂ hC ↦ forall₂_imp fun i x ↦ le_trans' <| by gcongr
  tfae_have 5 ↔ 7
  · refine exists_congr (fun C ↦ and_congr_right fun hC ↦ forall_congr' fun i ↦ ?_)
    rw [ContinuousLinearMap.opNorm_le_iff hC]
  tfae_have 7 ↔ 8
  · simp_rw [bddAbove_iff_exists_ge (0 : ℝ), Set.forall_mem_range]
  tfae_have 6 ↔ 8
  · simp_rw [bddAbove_def, Set.forall_mem_range]
  tfae_have 8 ↔ 9
  · rw [ENNReal.iSup_coe_lt_top, ← NNReal.bddAbove_coe, ← Set.range_comp]
    rfl
  -- `3 ↔ 4` is the interesting part of the result. It is essentially a combination of
  -- `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` which turns
  -- equicontinuity into existence of some continuous seminorm and
  -- `Seminorm.bound_of_continuous_normedSpace` which characterize such seminorms.
  tfae_have 3 ↔ 4
  · refine ((norm_withSeminorms 𝕜₂ F).uniformEquicontinuous_iff_exists_continuous_seminorm _).trans
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
