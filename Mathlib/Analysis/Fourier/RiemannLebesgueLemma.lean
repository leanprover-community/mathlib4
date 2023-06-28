/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.fourier.riemann_lebesgue_lemma
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Fourier.FourierTransform
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.InnerProductSpace.EuclideanDist
import Mathbin.MeasureTheory.Function.ContinuousMapDense
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.MeasureTheory.Measure.Haar.NormedSpace
import Mathbin.Topology.MetricSpace.EmetricParacompact

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma, for functions on finite-dimensional real vector
spaces `V`: if `f` is a function on `V` (valued in a complete normed space `E`), then the
Fourier transform of `f`, viewed as a function on the dual space of `V`, tends to 0 along the
cocompact filter. Here the Fourier transform is defined by

`λ w : V →L[ℝ] ℝ, ∫ (v : V), exp (↑(2 * π * w v) * I) • f x`.

This is true for arbitrary functions, but is only interesting for `L¹` functions (if `f` is not
integrable then the integral is zero for all `w`). This is proved first for continuous
compactly-supported functions on inner-product spaces; then we pass to arbitrary functions using the
density of continuous compactly-supported functions in `L¹` space. Finally we generalise from
inner-product spaces to arbitrary finite-dimensional spaces, by choosing a continuous linear
equivalence to an inner-product space.

## Main results

- `tendsto_integral_exp_inner_smul_cocompact` : for `V` a finite-dimensional real inner product
  space and `f : V → E`, the function `λ w : V, ∫ v : V, exp (2 * π * ⟪w, v⟫ * I) • f v` tends to 0
  along `cocompact V`.
- `tendsto_integral_exp_smul_cocompact` : for `V` a finite-dimensional real vector space (endowed
  with its unique Hausdorff topological vector space structure), and `W` the dual of `V`, the
  function `λ w : W, ∫ v : V, exp (2 * π * w v * I) • f v` tends to along `cocompact W`.
- `real.tendsto_integral_exp_smul_cocompact`: special case of functions on `ℝ`.
- `real.zero_at_infty_fourier_integral` and `real.zero_at_infty_vector_fourier_integral`:
  reformulations explicitly using the Fourier integral.
-/


noncomputable section

open MeasureTheory Filter Complex Set FiniteDimensional

open scoped Filter Topology Real ENNReal FourierTransform RealInnerProductSpace NNReal

variable {E V : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

local notation "e" => Real.fourierChar

section InnerProductSpace

variable [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The integrand in the Riemann-Lebesgue lemma for `f` is integrable iff `f` is. -/
theorem fourier_integrand_integrable (w : V) :
    Integrable f ↔ Integrable fun v : V => e[-⟪v, w⟫] • f v :=
  by
  have hL : Continuous fun p : V × V => bilin_form_of_real_inner.to_lin p.1 p.2 := continuous_inner
  rw [VectorFourier.fourier_integral_convergent_iff Real.continuous_fourierChar hL w]
  · simp only [BilinForm.toLin_apply, bilinFormOfRealInner_apply]
  · infer_instance
#align fourier_integrand_integrable fourier_integrand_integrable

variable [CompleteSpace E]

local notation "i" => fun w => (1 / (2 * ‖w‖ ^ 2)) • w

/-- Shifting `f` by `(1 / (2 * ‖w‖ ^ 2)) • w` negates the integral in the Riemann-Lebesgue lemma. -/
theorem fourier_integral_half_period_translate {w : V} (hw : w ≠ 0) :
    ∫ v : V, e[-⟪v, w⟫] • f (v + i w) = -∫ v : V, e[-⟪v, w⟫] • f v :=
  by
  have hiw : ⟪i w, w⟫ = 1 / 2 :=
    by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, IsROrC.ofReal_real_eq_id, id.def,
      IsROrC.conj_to_real, ← div_div, div_mul_cancel]
    rwa [Ne.def, sq_eq_zero_iff, norm_eq_zero]
  have :
    (fun v : V => e[-⟪v, w⟫] • f (v + i w)) = fun v : V =>
      (fun x : V => -e[-⟪x, w⟫] • f x) (v + i w) :=
    by
    ext1 v
    simp_rw [inner_add_left, hiw, Real.fourierChar_apply, neg_add, mul_add, of_real_add, add_mul,
      exp_add]
    have : 2 * π * -(1 / 2) = -π := by field_simp; ring
    rw [this, of_real_neg, neg_mul, exp_neg, exp_pi_mul_I, inv_neg, inv_one, mul_neg_one, neg_neg]
  rw [this, integral_add_right_eq_self]
  simp only [neg_smul, integral_neg]
#align fourier_integral_half_period_translate fourier_integral_half_period_translate

/-- Rewrite the Fourier integral in a form that allows us to use uniform continuity. -/
theorem fourier_integral_eq_half_sub_half_period_translate {w : V} (hw : w ≠ 0)
    (hf : Integrable f) :
    ∫ v : V, e[-⟪v, w⟫] • f v = (1 / (2 : ℂ)) • ∫ v : V, e[-⟪v, w⟫] • (f v - f (v + i w)) :=
  by
  simp_rw [smul_sub]
  rw [integral_sub, fourier_integral_half_period_translate hw, sub_eq_add_neg, neg_neg, ←
    two_smul ℂ _, ← @smul_assoc _ _ _ _ _ _ (IsScalarTower.left ℂ), smul_eq_mul]
  norm_num
  exacts [(fourier_integrand_integrable w).mp hf,
    (fourier_integrand_integrable w).mp (hf.comp_add_right _)]
#align fourier_integral_eq_half_sub_half_period_translate fourier_integral_eq_half_sub_half_period_translate

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 wrt `cocompact V`. Note that this is primarily
of interest as a preparatory step for the more general result
`tendsto_integral_exp_inner_smul_cocompact` in which `f` can be arbitrary. -/
theorem tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun w : V => ∫ v : V, e[-⟪v, w⟫] • f v) (cocompact V) (𝓝 0) :=
  by
  refine' normed_add_comm_group.tendsto_nhds_zero.mpr fun ε hε => _
  suffices ∃ T : ℝ, ∀ w : V, T ≤ ‖w‖ → ‖∫ v : V, e[-⟪v, w⟫] • f v‖ < ε
    by
    simp_rw [← comap_dist_left_atTop_eq_cocompact (0 : V), eventually_comap, eventually_at_top,
      dist_eq_norm', sub_zero]
    exact
      let ⟨T, hT⟩ := this
      ⟨T, fun b hb v hv => hT v (hv.symm ▸ hb)⟩
  obtain ⟨R, hR_pos, hR_bd⟩ : ∃ R : ℝ, 0 < R ∧ ∀ x : V, R ≤ ‖x‖ → f x = 0
  exact hf2.exists_pos_le_norm
  let A := {v : V | ‖v‖ ≤ R + 1}
  have mA : MeasurableSet A :=
    by
    suffices A = Metric.closedBall (0 : V) (R + 1) by rw [this];
      exact metric.is_closed_ball.measurable_set
    simp_rw [A, Metric.closedBall, dist_eq_norm, sub_zero]
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ B : ℝ≥0, 0 < B ∧ volume A ≤ B :=
    by
    have hc : IsCompact A := by
      simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using is_compact_closed_ball (0 : V) _
    let B₀ := volume A
    replace hc : B₀ < ⊤ := hc.measure_lt_top
    refine' ⟨B₀.to_nnreal + 1, add_pos_of_nonneg_of_pos B₀.to_nnreal.coe_nonneg one_pos, _⟩
    rw [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal hc.ne]
    exact le_self_add
  --* Use uniform continuity to choose δ such that `‖x - y‖ < δ` implies `‖f x - f y‖ < ε / B`.
  obtain ⟨δ, hδ1, hδ2⟩ :=
    metric.uniform_continuous_iff.mp (hf2.uniform_continuous_of_continuous hf1) (ε / B)
      (div_pos hε hB_pos)
  refine' ⟨1 / 2 + 1 / (2 * δ), fun w hw_bd => _⟩
  have hw_ne : w ≠ 0 := by
    contrapose! hw_bd; rw [hw_bd, norm_zero]
    exact add_pos one_half_pos (one_div_pos.mpr <| mul_pos two_pos hδ1)
  have hw'_nm : ‖i w‖ = 1 / (2 * ‖w‖) := by
    rw [norm_smul, norm_div, Real.norm_of_nonneg (mul_nonneg two_pos.le <| sq_nonneg _), norm_one,
      sq, ← div_div, ← div_div, ← div_div, div_mul_cancel _ (norm_eq_zero.not.mpr hw_ne)]
  --* Rewrite integral in terms of `f v - f (v + w')`.
  rw [fourier_integral_eq_half_sub_half_period_translate hw_ne
      (hf1.integrable_of_has_compact_support hf2),
    norm_smul, norm_eq_abs, ← Complex.ofReal_one, ← of_real_bit0, ← of_real_div,
    Complex.abs_of_nonneg one_half_pos.le]
  have : ε = 1 / 2 * (2 * ε) := by field_simp; rw [mul_comm]
  rw [this, mul_lt_mul_left (one_half_pos : (0 : ℝ) < 1 / 2)]
  refine' lt_of_le_of_lt (norm_integral_le_integral_norm _) _
  simp_rw [norm_smul, norm_eq_abs, abs_coe_circle, one_mul]
  --* Show integral can be taken over A only.
  have int_A : ∫ v : V, ‖f v - f (v + i w)‖ = ∫ v in A, ‖f v - f (v + i w)‖ :=
    by
    refine' (set_integral_eq_integral_of_forall_compl_eq_zero fun v hv => _).symm
    dsimp only [A] at hv 
    simp only [A, mem_set_of_eq, not_le] at hv 
    rw [hR_bd v _, hR_bd (v + i w) _, sub_zero, norm_zero]
    · rw [← sub_neg_eq_add]
      refine' le_trans _ (norm_sub_norm_le _ _)
      rw [le_sub_iff_add_le, norm_neg]
      refine' le_trans _ hv.le
      rw [add_le_add_iff_left, hw'_nm, ← div_div]
      refine' (div_le_one <| norm_pos_iff.mpr hw_ne).mpr _
      refine' le_trans (le_add_of_nonneg_right <| one_div_nonneg.mpr <| _) hw_bd
      exact (mul_pos (zero_lt_two' ℝ) hδ1).le
    · exact ((le_add_iff_nonneg_right _).mpr zero_le_one).trans hv.le
  rw [int_A]; clear int_A
  --* Bound integral using fact that `‖f v - f (v + w')‖` is small.
  have bdA : ∀ v : V, v ∈ A → ‖‖f v - f (v + i w)‖‖ ≤ ε / B :=
    by
    simp_rw [norm_norm]
    simp_rw [dist_eq_norm] at hδ2 
    refine' fun x _ => (hδ2 _).le
    rw [sub_add_cancel', norm_neg, hw'_nm, ← div_div, div_lt_iff (norm_pos_iff.mpr hw_ne), ←
      div_lt_iff' hδ1, div_div]
    refine' (lt_add_of_pos_left _ _).trans_le hw_bd
    exact one_half_pos
  have bdA2 := norm_set_integral_le_of_norm_le_const (hB_vol.trans_lt ENNReal.coe_lt_top) bdA _
  swap;
  · apply Continuous.aestronglyMeasurable
    exact
      continuous_norm.comp <|
        Continuous.sub hf1 <| Continuous.comp hf1 <| continuous_id'.add continuous_const
  have : ‖_‖ = ∫ v : V in A, ‖f v - f (v + i w)‖ :=
    Real.norm_of_nonneg (set_integral_nonneg mA fun x hx => norm_nonneg _)
  rw [this] at bdA2 
  refine' bdA2.trans_lt _
  rw [div_mul_eq_mul_div, div_lt_iff (nnreal.coe_pos.mpr hB_pos), mul_comm (2 : ℝ), mul_assoc,
    mul_lt_mul_left hε]
  rw [← ENNReal.toReal_le_toReal] at hB_vol 
  · refine' hB_vol.trans_lt _
    rw [(by rfl : (↑B : ENNReal).toReal = ↑B), two_mul]
    exact lt_add_of_pos_left _ hB_pos
  exacts [(hB_vol.trans_lt ENNReal.coe_lt_top).Ne, ennreal.coe_lt_top.ne]
#align tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support

variable (f)

/-- Riemann-Lebesgue lemma for functions on a real inner-product space: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 as `w → ∞`. -/
theorem tendsto_integral_exp_inner_smul_cocompact :
    Tendsto (fun w : V => ∫ v, e[-⟪v, w⟫] • f v) (cocompact V) (𝓝 0) :=
  by
  by_cases hfi : integrable f; swap
  · convert tendsto_const_nhds
    ext1 w
    apply integral_undef
    rwa [← fourier_integrand_integrable w]
  refine' metric.tendsto_nhds.mpr fun ε hε => _
  obtain ⟨g, hg_supp, hfg, hg_cont, -⟩ :=
    hfi.exists_has_compact_support_integral_sub_le (div_pos hε two_pos)
  refine'
    ((metric.tendsto_nhds.mp
            (tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hg_cont
              hg_supp))
          _ (div_pos hε two_pos)).mp
      (eventually_of_forall fun w hI => _)
  rw [dist_eq_norm] at hI ⊢
  have : ‖(∫ v, e[-⟪v, w⟫] • f v) - ∫ v, e[-⟪v, w⟫] • g v‖ ≤ ε / 2 :=
    by
    refine' le_trans _ hfg
    simp_rw [←
      integral_sub ((fourier_integrand_integrable w).mp hfi)
        ((fourier_integrand_integrable w).mp (hg_cont.integrable_of_has_compact_support hg_supp)),
      ← smul_sub, ← Pi.sub_apply]
    exact
      VectorFourier.norm_fourierIntegral_le_integral_norm e volume bilin_form_of_real_inner.to_lin
        (f - g) w
  replace := add_lt_add_of_le_of_lt this hI
  rw [add_halves] at this 
  refine' ((le_of_eq _).trans (norm_add_le _ _)).trans_lt this
  simp only [sub_zero, sub_add_cancel]
#align tendsto_integral_exp_inner_smul_cocompact tendsto_integral_exp_inner_smul_cocompact

/-- The Riemann-Lebesgue lemma for functions on `ℝ`. -/
theorem Real.tendsto_integral_exp_smul_cocompact (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, e[-(v * w)] • f v) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
#align real.tendsto_integral_exp_smul_cocompact Real.tendsto_integral_exp_smul_cocompact

/-- The Riemann-Lebesgue lemma for functions on `ℝ`, formulated via `real.fourier_integral`. -/
theorem Real.zero_at_infty_fourierIntegral (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
#align real.zero_at_infty_fourier_integral Real.zero_at_infty_fourierIntegral

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional inner-product space, formulated
via dual space. **Do not use** -- it is only a stepping stone to
`tendsto_integral_exp_smul_cocompact` where the inner-product-space structure isn't required. -/
theorem tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, e[-w v] • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) :=
  by
  obtain ⟨C, C_ne_zero, C_ne_top, hC⟩ := μ.is_add_haar_measure_eq_smul_is_add_haar_measure volume
  rw [hC]
  simp_rw [integral_smul_measure]
  rw [← (smul_zero _ : C.to_real • (0 : E) = 0)]
  apply tendsto.const_smul
  let A := (InnerProductSpace.toDual ℝ V).symm
  have : (fun w : V →L[ℝ] ℝ => ∫ v, e[-w v] • f v) = (fun w : V => ∫ v, e[-⟪v, w⟫] • f v) ∘ A :=
    by
    ext1 w
    congr 1 with v : 1
    rw [← inner_conj_symm, IsROrC.conj_to_real, InnerProductSpace.toDual_symm_apply,
      Real.fourierChar_apply]
  rw [this]
  exact
    (tendsto_integral_exp_inner_smul_cocompact f).comp
      A.to_homeomorph.to_cocompact_map.cocompact_tendsto'
#align tendsto_integral_exp_smul_cocompact_of_inner_product tendsto_integral_exp_smul_cocompact_of_inner_product

end InnerProductSpace

section NoInnerProduct

variable (f) [AddCommGroup V] [TopologicalSpace V] [TopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] [Module ℝ V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace E]

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional real vector space, formulated via
dual space. -/
theorem tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, e[-w v] • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) :=
  by
  -- We have already proved the result for inner-product spaces, formulated in a way which doesn't
  -- refer to the inner product. So we choose an arbitrary inner-product space isomorphic to V
  -- and port the result over from there.
  let V' := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have A : V ≃L[ℝ] V' := toEuclidean
  borelize V'
  -- various equivs derived from A
  let Aₘ : MeasurableEquiv V V' := A.to_homeomorph.to_measurable_equiv
  -- isomorphism between duals derived from A -- need to do continuity as a separate step in order
  -- to apply `linear_map.continuous_of_finite_dimensional`.
  let Adualₗ : (V →L[ℝ] ℝ) ≃ₗ[ℝ] V' →L[ℝ] ℝ :=
    { toFun := fun t => t.comp A.symm.to_continuous_linear_map
      invFun := fun t => t.comp A.to_continuous_linear_map
      map_add' := by intro t s; ext1 v;
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.add_apply]
      map_smul' := by intro x f; ext1 v;
        simp only [RingHom.id_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.smul_apply]
      left_inv := by intro w; ext1 v;
        simp only [ContinuousLinearEquiv.coe_def_rev, ContinuousLinearMap.coe_comp',
          ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := by intro w; ext1 v;
        simp only [ContinuousLinearEquiv.coe_def_rev, ContinuousLinearMap.coe_comp',
          ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          ContinuousLinearEquiv.apply_symm_apply] }
  let Adual : (V →L[ℝ] ℝ) ≃L[ℝ] V' →L[ℝ] ℝ :=
    { Adualₗ with
      continuous_toFun := Adualₗ.to_linear_map.continuous_of_finite_dimensional
      continuous_invFun := Adualₗ.symm.to_linear_map.continuous_of_finite_dimensional }
  have : (μ.map Aₘ).IsAddHaarMeasure := measure.map_continuous_linear_equiv.is_add_haar_measure _ A
  convert
    (tendsto_integral_exp_smul_cocompact_of_inner_product (f ∘ A.symm) (μ.map Aₘ)).comp
      Adual.to_homeomorph.to_cocompact_map.cocompact_tendsto'
  ext1 w
  rw [Function.comp_apply, integral_map_equiv]
  congr 1 with v : 1
  congr <;> exact (ContinuousLinearEquiv.symm_apply_apply A v).symm
#align tendsto_integral_exp_smul_cocompact tendsto_integral_exp_smul_cocompact

/-- The Riemann-Lebesgue lemma, formulated in terms of `vector_fourier.fourier_integral` (with the
pairing in the definition of `fourier_integral` taken to be the canonical pairing between `V` and
its dual space). -/
theorem Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (VectorFourier.fourierIntegral e μ (topDualPairing ℝ V).flip f) (cocompact (V →L[ℝ] ℝ))
      (𝓝 0) :=
  tendsto_integral_exp_smul_cocompact f μ
#align real.zero_at_infty_vector_fourier_integral Real.zero_at_infty_vector_fourierIntegral

end NoInnerProduct

