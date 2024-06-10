/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.MeasureTheory.Measure.Haar.Unique

#align_import analysis.fourier.riemann_lebesgue_lemma from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma, for functions on finite-dimensional real vector
spaces `V`: if `f` is a function on `V` (valued in a complete normed space `E`), then the
Fourier transform of `f`, viewed as a function on the dual space of `V`, tends to 0 along the
cocompact filter. Here the Fourier transform is defined by

`fun w : V →L[ℝ] ℝ ↦ ∫ (v : V), exp (↑(2 * π * w v) * I) • f v`.

This is true for arbitrary functions, but is only interesting for `L¹` functions (if `f` is not
integrable then the integral is zero for all `w`). This is proved first for continuous
compactly-supported functions on inner-product spaces; then we pass to arbitrary functions using the
density of continuous compactly-supported functions in `L¹` space. Finally we generalise from
inner-product spaces to arbitrary finite-dimensional spaces, by choosing a continuous linear
equivalence to an inner-product space.

## Main results

- `tendsto_integral_exp_inner_smul_cocompact` : for `V` a finite-dimensional real inner product
  space and `f : V → E`, the function `fun w : V ↦ ∫ v : V, exp (2 * π * ⟪w, v⟫ * I) • f v`
  tends to 0 along `cocompact V`.
- `tendsto_integral_exp_smul_cocompact` : for `V` a finite-dimensional real vector space (endowed
  with its unique Hausdorff topological vector space structure), and `W` the dual of `V`, the
  function `fun w : W ↦ ∫ v : V, exp (2 * π * w v * I) • f v` tends to along `cocompact W`.
- `Real.tendsto_integral_exp_smul_cocompact`: special case of functions on `ℝ`.
- `Real.zero_at_infty_fourierIntegral` and `Real.zero_at_infty_vector_fourierIntegral`:
  reformulations explicitly using the Fourier integral.
-/

noncomputable section

open MeasureTheory Filter Complex Set FiniteDimensional

open scoped Filter Topology Real ENNReal FourierTransform RealInnerProductSpace NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

section InnerProductSpace

variable [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

#align fourier_integrand_integrable Real.fourierIntegral_convergent_iff

variable [CompleteSpace E]

local notation3 "i" => fun (w : V) => (1 / (2 * ‖w‖ ^ 2) : ℝ) • w

/-- Shifting `f` by `(1 / (2 * ‖w‖ ^ 2)) • w` negates the integral in the Riemann-Lebesgue lemma. -/
theorem fourierIntegral_half_period_translate {w : V} (hw : w ≠ 0) :
    (∫ v : V, 𝐞 (-⟪v, w⟫) • f (v + i w)) = -∫ v : V, 𝐞 (-⟪v, w⟫) • f v := by
  have hiw : ⟪i w, w⟫ = 1 / 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id,
      RCLike.conj_to_real, ← div_div, div_mul_cancel₀]
    rwa [Ne, sq_eq_zero_iff, norm_eq_zero]
  have :
    (fun v : V => 𝐞 (-⟪v, w⟫) • f (v + i w)) =
      fun v : V => (fun x : V => -(𝐞 (-⟪x, w⟫) • f x)) (v + i w) := by
    ext1 v
    simp_rw [inner_add_left, hiw, Submonoid.smul_def, Real.fourierChar_apply, neg_add, mul_add,
      ofReal_add, add_mul, exp_add]
    have : 2 * π * -(1 / 2) = -π := by field_simp; ring
    rw [this, ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I, inv_neg, inv_one, mul_neg_one, neg_smul,
      neg_neg]
  rw [this]
  -- Porting note:
  -- The next three lines had just been
  -- rw [integral_add_right_eq_self (fun (x : V) ↦ -(𝐞[-⟪x, w⟫]) • f x)
  --       ((fun w ↦ (1 / (2 * ‖w‖ ^ (2 : ℕ))) • w) w)]
  -- Unfortunately now we need to specify `volume`.
  have := integral_add_right_eq_self (μ := volume) (fun (x : V) ↦ -(𝐞 (-⟪x, w⟫) • f x))
    ((fun w ↦ (1 / (2 * ‖w‖ ^ (2 : ℕ))) • w) w)
  rw [this]
  simp only [neg_smul, integral_neg]
#align fourier_integral_half_period_translate fourierIntegral_half_period_translate

/-- Rewrite the Fourier integral in a form that allows us to use uniform continuity. -/
theorem fourierIntegral_eq_half_sub_half_period_translate {w : V} (hw : w ≠ 0)
    (hf : Integrable f) :
    ∫ v : V, 𝐞 (-⟪v, w⟫) • f v = (1 / (2 : ℂ)) • ∫ v : V, 𝐞 (-⟪v, w⟫) • (f v - f (v + i w)) := by
  simp_rw [smul_sub]
  rw [integral_sub, fourierIntegral_half_period_translate hw, sub_eq_add_neg, neg_neg, ←
    two_smul ℂ _, ← @smul_assoc _ _ _ _ _ _ (IsScalarTower.left ℂ), smul_eq_mul]
  · norm_num
  exacts [(Real.fourierIntegral_convergent_iff w).2 hf,
    (Real.fourierIntegral_convergent_iff w).2 (hf.comp_add_right _)]
#align fourier_integral_eq_half_sub_half_period_translate fourierIntegral_eq_half_sub_half_period_translate

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 wrt `cocompact V`. Note that this is primarily
of interest as a preparatory step for the more general result
`tendsto_integral_exp_inner_smul_cocompact` in which `f` can be arbitrary. -/
theorem tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun w : V => ∫ v : V, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  refine NormedAddCommGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  suffices ∃ T : ℝ, ∀ w : V, T ≤ ‖w‖ → ‖∫ v : V, 𝐞 (-⟪v, w⟫) • f v‖ < ε by
    simp_rw [← comap_dist_left_atTop_eq_cocompact (0 : V), eventually_comap, eventually_atTop,
      dist_eq_norm', sub_zero]
    exact
      let ⟨T, hT⟩ := this
      ⟨T, fun b hb v hv => hT v (hv.symm ▸ hb)⟩
  obtain ⟨R, -, hR_bd⟩ : ∃ R : ℝ, 0 < R ∧ ∀ x : V, R ≤ ‖x‖ → f x = 0 := hf2.exists_pos_le_norm
  let A := {v : V | ‖v‖ ≤ R + 1}
  have mA : MeasurableSet A := by
    suffices A = Metric.closedBall (0 : V) (R + 1) by
      rw [this]
      exact Metric.isClosed_ball.measurableSet
    simp_rw [Metric.closedBall, dist_eq_norm, sub_zero]
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ B : ℝ≥0, 0 < B ∧ volume A ≤ B := by
    have hc : IsCompact A := by
      simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using isCompact_closedBall (0 : V) _
    let B₀ := volume A
    replace hc : B₀ < ⊤ := hc.measure_lt_top
    refine ⟨B₀.toNNReal + 1, add_pos_of_nonneg_of_pos B₀.toNNReal.coe_nonneg one_pos, ?_⟩
    rw [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal hc.ne]
    exact le_self_add
  --* Use uniform continuity to choose δ such that `‖x - y‖ < δ` implies `‖f x - f y‖ < ε / B`.
  obtain ⟨δ, hδ1, hδ2⟩ :=
    Metric.uniformContinuous_iff.mp (hf2.uniformContinuous_of_continuous hf1) (ε / B)
      (div_pos hε hB_pos)
  refine ⟨1 / 2 + 1 / (2 * δ), fun w hw_bd => ?_⟩
  have hw_ne : w ≠ 0 := by
    contrapose! hw_bd; rw [hw_bd, norm_zero]
    exact add_pos one_half_pos (one_div_pos.mpr <| mul_pos two_pos hδ1)
  have hw'_nm : ‖i w‖ = 1 / (2 * ‖w‖) := by
    rw [norm_smul, norm_div, Real.norm_of_nonneg (mul_nonneg two_pos.le <| sq_nonneg _), norm_one,
      sq, ← div_div, ← div_div, ← div_div, div_mul_cancel₀ _ (norm_eq_zero.not.mpr hw_ne)]
  --* Rewrite integral in terms of `f v - f (v + w')`.
  have : ‖(1 / 2 : ℂ)‖ = 2⁻¹ := by norm_num
  rw [fourierIntegral_eq_half_sub_half_period_translate hw_ne
      (hf1.integrable_of_hasCompactSupport hf2),
    norm_smul, this, inv_mul_eq_div, div_lt_iff' two_pos]
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  simp_rw [norm_circle_smul]
  --* Show integral can be taken over A only.
  have int_A : ∫ v : V, ‖f v - f (v + i w)‖ = ∫ v in A, ‖f v - f (v + i w)‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    dsimp only [A] at hv
    simp only [mem_setOf, not_le] at hv
    rw [hR_bd v _, hR_bd (v + i w) _, sub_zero, norm_zero]
    · rw [← sub_neg_eq_add]
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [le_sub_iff_add_le, norm_neg]
      refine le_trans ?_ hv.le
      rw [add_le_add_iff_left, hw'_nm, ← div_div]
      refine (div_le_one <| norm_pos_iff.mpr hw_ne).mpr ?_
      refine le_trans (le_add_of_nonneg_right <| one_div_nonneg.mpr <| ?_) hw_bd
      exact (mul_pos (zero_lt_two' ℝ) hδ1).le
    · exact (le_add_of_nonneg_right zero_le_one).trans hv.le
  rw [int_A]; clear int_A
  --* Bound integral using fact that `‖f v - f (v + w')‖` is small.
  have bdA : ∀ v : V, v ∈ A → ‖‖f v - f (v + i w)‖‖ ≤ ε / B := by
    simp_rw [norm_norm]
    simp_rw [dist_eq_norm] at hδ2
    refine fun x _ => (hδ2 ?_).le
    rw [sub_add_cancel_left, norm_neg, hw'_nm, ← div_div, div_lt_iff (norm_pos_iff.mpr hw_ne), ←
      div_lt_iff' hδ1, div_div]
    exact (lt_add_of_pos_left _ one_half_pos).trans_le hw_bd
  have bdA2 := norm_setIntegral_le_of_norm_le_const (hB_vol.trans_lt ENNReal.coe_lt_top) bdA ?_
  swap
  · apply Continuous.aestronglyMeasurable
    exact
      continuous_norm.comp <|
        Continuous.sub hf1 <| Continuous.comp hf1 <| continuous_id'.add continuous_const
  have : ‖_‖ = ∫ v : V in A, ‖f v - f (v + i w)‖ :=
    Real.norm_of_nonneg (setIntegral_nonneg mA fun x _ => norm_nonneg _)
  rw [this] at bdA2
  refine bdA2.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff (NNReal.coe_pos.mpr hB_pos), mul_comm (2 : ℝ), mul_assoc,
    mul_lt_mul_left hε]
  rw [← ENNReal.toReal_le_toReal] at hB_vol
  · refine hB_vol.trans_lt ?_
    rw [(by rfl : (↑B : ENNReal).toReal = ↑B), two_mul]
    exact lt_add_of_pos_left _ hB_pos
  exacts [(hB_vol.trans_lt ENNReal.coe_lt_top).ne, ENNReal.coe_lt_top.ne]
#align tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support

variable (f)

/-- Riemann-Lebesgue lemma for functions on a real inner-product space: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 as `w → ∞`. -/
theorem tendsto_integral_exp_inner_smul_cocompact :
    Tendsto (fun w : V => ∫ v, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  by_cases hfi : Integrable f; swap
  · convert tendsto_const_nhds (x := (0 : E)) with w
    apply integral_undef
    rwa [Real.fourierIntegral_convergent_iff]
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g, hg_supp, hfg, hg_cont, -⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (div_pos hε two_pos)
  refine
    ((Metric.tendsto_nhds.mp
            (tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hg_cont
              hg_supp))
          _ (div_pos hε two_pos)).mp
      (eventually_of_forall fun w hI => ?_)
  rw [dist_eq_norm] at hI ⊢
  have : ‖(∫ v, 𝐞 (-⟪v, w⟫) • f v) - ∫ v, 𝐞 (-⟪v, w⟫) • g v‖ ≤ ε / 2 := by
    refine le_trans ?_ hfg
    simp_rw [← integral_sub ((Real.fourierIntegral_convergent_iff w).2 hfi)
      ((Real.fourierIntegral_convergent_iff w).2 (hg_cont.integrable_of_hasCompactSupport hg_supp)),
      ← smul_sub, ← Pi.sub_apply]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 _ bilinFormOfRealInner (f - g) w
  replace := add_lt_add_of_le_of_lt this hI
  rw [add_halves] at this
  refine ((le_of_eq ?_).trans (norm_add_le _ _)).trans_lt this
  simp only [sub_zero, sub_add_cancel]
#align tendsto_integral_exp_inner_smul_cocompact tendsto_integral_exp_inner_smul_cocompact

/-- The Riemann-Lebesgue lemma for functions on `ℝ`. -/
theorem Real.tendsto_integral_exp_smul_cocompact (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, 𝐞 (-(v * w)) • f v) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
#align real.tendsto_integral_exp_smul_cocompact Real.tendsto_integral_exp_smul_cocompact

/-- The Riemann-Lebesgue lemma for functions on `ℝ`, formulated via `Real.fourierIntegral`. -/
theorem Real.zero_at_infty_fourierIntegral (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f
#align real.zero_at_infty_fourier_integral Real.zero_at_infty_fourierIntegral

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional inner-product space, formulated
via dual space. **Do not use** -- it is only a stepping stone to
`tendsto_integral_exp_smul_cocompact` where the inner-product-space structure isn't required. -/
theorem tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) := by
  rw [μ.isAddLeftInvariant_eq_smul volume]
  simp_rw [integral_smul_nnreal_measure]
  rw [← (smul_zero _ : Measure.addHaarScalarFactor μ volume • (0 : E) = 0)]
  apply Tendsto.const_smul
  let A := (InnerProductSpace.toDual ℝ V).symm
  have : (fun w : V →L[ℝ] ℝ ↦ ∫ v, 𝐞 (-w v) • f v) = (fun w : V ↦ ∫ v, 𝐞 (-⟪v, w⟫) • f v) ∘ A := by
    ext1 w
    congr 1 with v : 1
    rw [← inner_conj_symm, RCLike.conj_to_real, InnerProductSpace.toDual_symm_apply]
  rw [this]
  exact (tendsto_integral_exp_inner_smul_cocompact f).comp
      A.toHomeomorph.toCocompactMap.cocompact_tendsto'
#align tendsto_integral_exp_smul_cocompact_of_inner_product tendsto_integral_exp_smul_cocompact_of_inner_product

end InnerProductSpace

section NoInnerProduct

variable (f) [AddCommGroup V] [TopologicalSpace V] [TopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] [Module ℝ V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace E]

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional real vector space, formulated via
dual space. -/
theorem tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : V →L[ℝ] ℝ => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) := by
  -- We have already proved the result for inner-product spaces, formulated in a way which doesn't
  -- refer to the inner product. So we choose an arbitrary inner-product space isomorphic to V
  -- and port the result over from there.
  let V' := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have A : V ≃L[ℝ] V' := toEuclidean
  borelize V'
  -- various equivs derived from A
  let Aₘ : MeasurableEquiv V V' := A.toHomeomorph.toMeasurableEquiv
  -- isomorphism between duals derived from A -- need to do continuity as a separate step in order
  -- to apply `LinearMap.continuous_of_finiteDimensional`.
  let Adualₗ : (V →L[ℝ] ℝ) ≃ₗ[ℝ] V' →L[ℝ] ℝ :=
    { toFun := fun t => t.comp A.symm.toContinuousLinearMap
      invFun := fun t => t.comp A.toContinuousLinearMap
      map_add' := by
        intro t s
        ext1 v
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.add_apply]
      map_smul' := by
        intro x f
        ext1 v
        simp only [RingHom.id_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.smul_apply]
      left_inv := by
        intro w
        ext1 v
        simp only [ContinuousLinearMap.coe_comp',
          ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := by
        intro w
        ext1 v
        simp only [ContinuousLinearMap.coe_comp',
          ContinuousLinearEquiv.coe_coe, Function.comp_apply,
          ContinuousLinearEquiv.apply_symm_apply] }
  let Adual : (V →L[ℝ] ℝ) ≃L[ℝ] V' →L[ℝ] ℝ :=
    { Adualₗ with
      continuous_toFun := Adualₗ.toLinearMap.continuous_of_finiteDimensional
      continuous_invFun := Adualₗ.symm.toLinearMap.continuous_of_finiteDimensional }
  have : (μ.map Aₘ).IsAddHaarMeasure := Measure.MapContinuousLinearEquiv.isAddHaarMeasure _ A
  convert
    (tendsto_integral_exp_smul_cocompact_of_inner_product (f ∘ A.symm) (μ.map Aₘ)).comp
      Adual.toHomeomorph.toCocompactMap.cocompact_tendsto' with w
  rw [Function.comp_apply, integral_map_equiv]
  congr 1 with v : 1
  congr
  · -- Porting note: added `congr_arg`
    apply congr_arg w
    exact (ContinuousLinearEquiv.symm_apply_apply A v).symm
  · exact (ContinuousLinearEquiv.symm_apply_apply A v).symm
#align tendsto_integral_exp_smul_cocompact tendsto_integral_exp_smul_cocompact

/-- The Riemann-Lebesgue lemma, formulated in terms of `VectorFourier.fourierIntegral` (with the
pairing in the definition of `fourier_integral` taken to be the canonical pairing between `V` and
its dual space). -/
theorem Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (VectorFourier.fourierIntegral 𝐞 μ (topDualPairing ℝ V).flip f) (cocompact (V →L[ℝ] ℝ))
      (𝓝 0) :=
  _root_.tendsto_integral_exp_smul_cocompact f μ
#align real.zero_at_infty_vector_fourier_integral Real.zero_at_infty_vector_fourierIntegral

end NoInnerProduct
