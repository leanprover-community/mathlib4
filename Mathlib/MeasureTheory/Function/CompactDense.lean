/-
Copyright (c) 2025 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Density results for compact functions -/

open MeasureTheory Filter
open scoped ENNReal CompactlySupported ContDiff Convolution Topology Pointwise

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Compact

variable [MeasurableSpace E] [BorelSpace E]

-- TODO: Provide `.toLp` as CLM?
-- Would require `TopologicalSpace (E →C_c F)`, e.g. via `PseudoMetricSpace`.

-- TODO: Move?
/-- Any `CompactlySupportedContinuousMap` is in `L^p`. -/
theorem CompactlySupportedContinuousMap.memℒp (f : E →C_c F) (p : ℝ≥0∞)
    (μ : Measure E := by volume_tac) [IsFiniteMeasureOnCompacts μ] : Memℒp f p μ :=
  f.continuous.memℒp_of_hasCompactSupport f.hasCompactSupport

variable (F) in
/-- The mapping from continuous, compact-support functions to `L^p` with `1 ≤ p < ⊤` is dense. -/
theorem CompactlySupportedContinuousMap.toLp_denseRange
    [NormalSpace E] [WeaklyLocallyCompactSpace E] [NormedSpace ℝ F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤) (μ : Measure E := by volume_tac) [μ.Regular] :
    DenseRange (fun f : E →C_c F ↦ (f.memℒp p μ).toLp) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  -- Use `ε / 2` to obtain strict inequality.
  obtain ⟨g, hg_supp, hg_dist, hg_cont, _⟩ := (Lp.memℒp f).exists_hasCompactSupport_eLpNorm_sub_le
    hp_top (ε := .ofReal (ε / 2)) (by simpa using hε)
  use ⟨⟨g, hg_cont⟩, hg_supp⟩
  rw [Lp.dist_def]
  refine ENNReal.toReal_lt_of_lt_ofReal ?_
  refine lt_of_eq_of_lt (eLpNorm_congr_ae ?_) (lt_of_le_of_lt hg_dist ?_)
  · exact .sub .rfl (Memℒp.coeFn_toLp _)
  · exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨div_two_lt_of_pos hε, hε⟩

end Compact

/-! ## Smooth, compact functions -/

section Smooth

variable [MeasurableSpace E] [BorelSpace E]

/-- When `f` is continuous and has compact support, the `L^p` norm of `fun x ↦ f(x + t) - f(x)`
tends to zero as `t` tends to zero.

This is useful for proving the density of smooth, compactly-supported functions in `L^p`. -/
theorem eLpNorm_comp_add_right_sub_self_tendsto_zero_of_hasCompactSupport
    {f : E → F} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    (p : NNReal) (μ : Measure E := by volume_tac) [μ.Regular] [μ.IsAddRightInvariant] :
    Tendsto (fun t ↦ eLpNorm (fun x ↦ f (x + t) - f x) p μ) (𝓝 0) (𝓝 0) := by
  cases Decidable.eq_or_ne p 0 with | inl hp => simp [hp] | inr hp =>
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  cases ε with | top => simp | coe ε =>
  rw [Metric.eventually_nhds_iff]
  -- Set bound `‖f (x + t) - f x‖ < r`.
  -- Choose `r` such that `r ^ p * μ (tsupport fun x ↦ f (x + t) - f x) ≤ ε ^ p`.
  -- Use that `μ (tsupport fun x ↦ f (x + t) - f x) ≤ 2 * μ (tsupport f)` independent of `t`.
  -- Add 1 to avoid `ENNReal.toNNReal` mapping ⊤ to 0.
  have hr_top : ε / (1 + 2 * μ (tsupport f)) ^ (p⁻¹ : ℝ) < ⊤ := by
    refine ENNReal.div_lt_top ENNReal.coe_ne_top ?_
    simp
  have hr_pos : 0 < ε / (1 + 2 * μ (tsupport f)) ^ (p⁻¹ : ℝ) := by
    refine ENNReal.div_pos hε.ne' ?_
    refine ENNReal.rpow_ne_top_of_nonneg (by simp) ?_
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ?_⟩
    exact ENNReal.mul_ne_top ENNReal.two_ne_top hf_supp.isCompact.measure_ne_top
  generalize hr : ε / (1 + 2 * μ (tsupport f)) ^ (p⁻¹ : ℝ) = r at hr_top hr_pos
  -- Obtain `δ` from `r` using the uniform continuity of `f`.
  rcases Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont)
    r.toReal (ENNReal.toReal_pos hr_pos.ne' hr_top.ne) with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun t ht ↦ ?_⟩
  refine le_trans (b := r * μ (tsupport fun x ↦ f (x + t) - f x) ^ (p⁻¹ : ℝ)) ?_ ?_
  · -- testing
    rw [← eLpNorm_restrict_eq_of_support_subset (subset_tsupport _)]
    rw [eLpNorm_nnreal_eq_eLpNorm' hp, eLpNorm'_eq_lintegral_nnnorm]
    rw [one_div, ENNReal.rpow_inv_le_iff (z := p) (NNReal.coe_pos.mpr <| pos_iff_ne_zero.mpr hp)]
    -- Bound integrand with constant function.
    refine le_of_le_of_eq (lintegral_mono (g := fun _ ↦ r ^ (p : ℝ)) fun x ↦ ?_) ?_
    · refine ENNReal.rpow_le_rpow ?_ NNReal.zero_le_coe
      refine le_trans ?_ ENNReal.coe_toNNReal_le_self
      rw [ENNReal.coe_le_coe]
      simp only [dist_eq_norm] at hδ
      exact le_of_lt (hδ (by simpa using ht))
    · rw [lintegral_const, Measure.restrict_apply .univ, Set.univ_inter]
      rw [ENNReal.mul_rpow_of_nonneg _ _ NNReal.zero_le_coe]
      rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hp)]
      simp
  · rw [← hr]
    rw [ENNReal.mul_comm_div]
    refine mul_le_of_le_one_right' ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    refine ENNReal.rpow_le_rpow ?_ (by simp)
    refine le_add_left ?_
    -- Use `μ.AddRightInvariant` to show `μ (tsupport fun x ↦ f (x + t)) = μ (tsupport f)`.
    refine le_trans (measure_mono (closure_mono (Function.support_sub _ _))) ?_
    rw [closure_union]
    refine le_of_le_of_eq (measure_union_le _ _) ?_
    rw [tsupport, two_mul]
    refine congrArg₂ _ ?_ rfl
    change μ (closure (Function.support (f ∘ (Homeomorph.addRight t)))) = _
    rw [Function.support_comp_eq_preimage, ← Homeomorph.preimage_closure]
    simp

theorem exists_contDiffBump_eLpNorm_conv_sub_self_lt
    [NormedSpace ℝ E] [NormedSpace ℝ F] [HasContDiffBump E]
    [FiniteDimensional ℝ E]
    {f : E → F} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    (p : NNReal) (hp : 1 ≤ p) (μ : Measure E := by volume_tac) [hμ : μ.Regular] [μ.IsOpenPosMeasure]
    [μ.IsAddRightInvariant] -- [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    [CompleteSpace F]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ContDiffBump 0, eLpNorm (φ.normed μ ⋆[.lsmul ℝ ℝ, μ] f - f) p μ ≤ .ofReal ε := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  -- Obtain `δ` to control `eLpNorm (fun x ↦ f (x + t) - f x) p` for `‖t‖ < δ`.
  have := eLpNorm_comp_add_right_sub_self_tendsto_zero_of_hasCompactSupport hf_cont hf_supp p μ
  simp only [ENNReal.tendsto_nhds_zero, Metric.eventually_nhds_iff_ball] at this
  -- specialize this ε' (ENNReal.coe_pos.mpr hε')
  -- let ε_nn := ε.toNNReal
  -- have hε_nn : 0 < ε_nn := Real.toNNReal_pos.mpr hε
  -- specialize this ε_nn (ENNReal.coe_pos.mpr hε_nn)
  specialize this (.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨δ, hδ_pos, hδ⟩ := this
  -- rcases this with ⟨δ, hδ_pos, hδ⟩

  -- Obtain `φ` whose support is contained within a `δ` ball.
  -- TODO: Is there a more idiomatic way to define `φ`?
  let φ : ContDiffBump (0 : E) := (⟨_, δ, half_pos hδ_pos, div_two_lt_of_pos hδ_pos⟩)
  have hφδ : Function.support (φ.normed μ) = Metric.ball 0 δ := ContDiffBump.support_normed_eq _
  use φ

  -- TODO: Is proving `Memℒp` the cleanest way to do this?
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm (ENNReal.coe_ne_zero.mpr hp_pos.ne') ENNReal.coe_ne_top]
  swap
  · refine Memℒp.sub ?_ ?_
    · refine Continuous.memℒp_of_hasCompactSupport ?_ ?_
      · exact hf_supp.continuous_convolution_right _ φ.integrable_normed.locallyIntegrable hf_cont
      · exact φ.hasCompactSupport_normed.convolution _ hf_supp
    · exact hf_cont.memℒp_of_hasCompactSupport hf_supp

  rw [ENNReal.ofReal_le_ofReal_iff hε.le]
  simp only [Pi.sub_apply, ENNReal.coe_toReal]
  rw [Real.rpow_inv_le_iff_of_pos (integral_nonneg fun _ ↦ by simp [Real.rpow_nonneg]) hε.le
    (NNReal.coe_pos.mpr hp_pos)]

  -- Establish `Continuous` and `HasCompactSupport` for the integrand.
  -- This will be useful for changing the order of the integral.
  have hφf_cont : Continuous
      (Function.uncurry fun x t ↦ φ.normed μ t * ‖f (x - t) - f x‖ ^ (p : ℝ)) := by
    refine .mul ?_ ?_
    · refine φ.continuous_normed.comp continuous_snd
    · refine .rpow_const (.norm ?_) fun _ ↦ Or.inr NNReal.zero_le_coe
      exact .sub (hf_cont.comp (.sub continuous_fst continuous_snd)) (hf_cont.comp continuous_fst)
  have hφf_supp : HasCompactSupport
      (Function.uncurry fun x t ↦ φ.normed μ t * ‖f (x - t) - f x‖ ^ (p : ℝ)) := by
    rw [hasCompactSupport_def]
    have hφ_supp : HasCompactSupport (φ.normed μ) := φ.hasCompactSupport_normed
    refine IsCompact.closure_of_subset (.prod (.add hφ_supp hf_supp) hφ_supp) ?_
    rw [Function.support_subset_iff]
    rintro ⟨x, t⟩
    simp only [Function.uncurry_apply_pair, mul_ne_zero_iff, Set.mem_prod]
    rintro ⟨hφ, hf⟩
    rw [Real.rpow_ne_zero (norm_nonneg _) (NNReal.coe_ne_zero.mpr hp_pos.ne'), norm_ne_zero_iff]
      at hf
    refine ⟨?_, subset_closure hφ⟩
    · rw [sub_ne_zero] at hf
      rw [Set.mem_add]
      cases hf.ne_or_ne 0 with
      | inl hf => exact ⟨t, subset_closure hφ, x - t, subset_closure hf, add_sub_cancel t x⟩
      | inr hf =>
        refine ⟨0, ?_, x, subset_closure hf, zero_add x⟩
        simpa [ContDiffBump.tsupport_normed_eq] using φ.rOut_pos.le
  -- Product is integrable. This allows us to use `integrable_prod_iff`.
  have hφf_int := hφf_cont.integrable_of_hasCompactSupport hφf_supp (μ := μ.prod μ)

  refine le_trans (integral_mono_of_nonneg ?_ ?_ ?_
    (g := fun x ↦ ∫ t, φ.normed μ t * ‖f (x - t) - f x‖ ^ (p : ℝ) ∂μ)) ?_
  · exact .of_forall fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  · have := ((integrable_prod_iff hφf_cont.measurable.aestronglyMeasurable).mp hφf_int).2
    refine Eq.subst (motive := fun f : E → E → ℝ ↦ Integrable (fun x ↦ ∫ y, f x y ∂μ) μ) ?_ this
    ext x y
    simp [abs_of_nonneg (φ.nonneg_normed _), Real.rpow_nonneg (norm_nonneg _)]
  · refine .of_forall fun x ↦ ?_
    simp only

    have h₁ (x : E) : (φ.normed μ ⋆[.lsmul ℝ ℝ, μ] f) x - f x =
        ∫ t, φ.normed μ t • (f (x - t) - f x) ∂μ := by
      simp only [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
      simp only [smul_sub]
      -- rw [integral_sub]
      -- TODO: Re-jig to avoid conv?
      conv => lhs; rw [← ContDiffBump.integral_normed_smul φ μ (f x)]
      rw [integral_sub]
      · refine Integrable.smul_of_top_left φ.integrable_normed ?_
        obtain ⟨C, hC⟩ := hf_cont.bounded_above_of_compact_support hf_supp
        refine memℒp_top_of_bound ?_ C ?_
        · exact (hf_cont.comp (continuous_sub_left x)).aestronglyMeasurable
        · exact .of_forall fun t ↦ hC (x - t)
      · exact φ.integrable_normed.smul_const _
    rw [h₁]; clear h₁

    rw [← Real.le_rpow_inv_iff_of_pos (norm_nonneg _) ?_ (NNReal.coe_pos.mpr hp_pos)]
    swap
    · refine integral_nonneg fun t ↦ ?_
      simp [mul_nonneg, φ.nonneg_normed, Real.rpow_nonneg]

    -- Note: `generalize` seems to play nicer than `let :=` for e.g. `cases q`.
    have hpq := ENNReal.IsConjExponent.conjExponent (p := p) (by simpa using hp)
    generalize (p : ℝ≥0∞).conjExponent = q at hpq

    -- Note: Can have `p = 1` and `q = ⊤`. This condition still holds since `0⁻¹ = 0`.
    have hpq_real : (p : ℝ)⁻¹ + q.toReal⁻¹ = (1 : ℝ) := by
      rw [← ENNReal.coe_toNNReal_eq_toReal]
      simp only [← NNReal.coe_inv, ← NNReal.coe_add, NNReal.coe_eq_one]
      cases hp.eq_or_gt with
      | inl hp => simp [hpq.conj_eq, hp]
      | inr hp =>
        rw [← hpq.conjExponent_eq, ← ENNReal.coe_conjExponent hp, ENNReal.toNNReal_coe]
        exact NNReal.IsConjExponent.inv_add_inv_conj (.conjExponent hp)

    have h₁ : eLpNorm (fun t ↦ φ.normed μ t ^ q.toReal⁻¹) q μ = 1 := by
      cases q with | top => simp [eLpNormEssSup_eq_essSup_nnnorm] | coe q =>
      simp only [ENNReal.coe_toReal]
      have hq_pos : 0 < q := ENNReal.coe_pos.mp hpq.symm.pos
      rw [eLpNorm_nnreal_eq_lintegral hq_pos.ne']
      -- Cancel the powers.
      simp_rw [Real.nnnorm_rpow_of_nonneg (φ.nonneg_normed _)]
      simp_rw [← ENNReal.coe_rpow_of_nonneg _ NNReal.zero_le_coe]
      simp_rw [← NNReal.rpow_mul]
      rw [inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hq_pos.ne')]
      -- Show integral is equal to one.
      have : ∫ (x : E), ‖φ.normed μ x‖ ∂μ = 1 := by
        simp only [Real.norm_of_nonneg (φ.nonneg_normed _)]
        exact φ.integral_normed
      rw [integral_norm_eq_lintegral_nnnorm φ.continuous_normed.aestronglyMeasurable] at this
      rw [ENNReal.toReal_eq_one_iff] at this
      simp [this]

    have h_eLpNorm : eLpNorm (fun t ↦ φ.normed μ t • (f (x - t) - f x)) 1 μ ≤
        eLpNorm (fun t ↦ φ.normed μ t ^ q.toReal⁻¹) q μ *
        eLpNorm (fun t ↦ φ.normed μ t ^ (p⁻¹ : ℝ) • (f (x - t) - f x)) (↑p) μ := by
      refine le_of_eq_of_le (congrArg (eLpNorm · 1 μ) ?_) <| eLpNorm_smul_le_mul_eLpNorm
        (Continuous.aestronglyMeasurable <| by
          refine .smul ?_ ?_
          · exact φ.continuous_normed.rpow_const (by simp)
          · exact .sub (hf_cont.comp (continuous_sub_left x)) continuous_const)
        (Continuous.aestronglyMeasurable <| φ.continuous_normed.rpow_const (by simp))
        (by simpa [add_comm, eq_comm] using hpq.inv_add_inv_conj)
      ext t
      simp only [Pi.smul_apply', smul_smul]
      rw [mul_comm, ← Real.rpow_add' (φ.nonneg_normed t) (hpq_real.trans_ne one_ne_zero)]
      simp [hpq_real]

    rw [h₁, one_mul] at h_eLpNorm; clear h₁

    rw [Memℒp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top] at h_eLpNorm
    swap
    · refine .smul ?_ ?_ (p := 1) (r := ⊤) (q := 1) (by simp)
      · refine .sub ?_ (memℒp_top_const _)
        refine Continuous.memℒp_top_of_hasCompactSupport ?_ ?_ μ
        · exact hf_cont.comp (continuous_sub_left x)
        · exact .comp_homeomorph hf_supp (.subLeft x)
      · exact memℒp_one_iff_integrable.mpr φ.integrable_normed

    -- TODO: Ugly to use `hpq` here? Nicer than `ENNReal.coe_ne_zero.mpr hp_pos.ne'` though?
    rw [Memℒp.eLpNorm_eq_integral_rpow_norm hpq.ne_zero ENNReal.coe_ne_top] at h_eLpNorm
    swap
    · refine .smul ?_ ?_ (p := p) (r := ⊤) (q := p) (by simp)
      · refine .sub ?_ (memℒp_top_const _)
        refine Continuous.memℒp_top_of_hasCompactSupport ?_ ?_ μ
        · exact hf_cont.comp (continuous_sub_left x)
        · exact .comp_homeomorph hf_supp (.subLeft x)
      · have := (memℒp_one_iff_integrable.mpr φ.integrable_normed).norm_rpow_div p⁻¹ (μ := μ)
        simpa [abs_of_nonneg (φ.nonneg_normed _)] using this

    simp at h_eLpNorm
    rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _)] at h_eLpNorm

    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_le_of_eq h_eLpNorm (congrArg (fun f : E → ℝ ↦ (∫ t, f t ∂μ) ^ (p : ℝ)⁻¹) ?_)
    clear h_eLpNorm

    ext t
    rw [norm_smul]
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (φ.nonneg_normed _) _)]
    refine congrArg (· * _) ?_
    rw [← Real.rpow_mul (φ.nonneg_normed t)]
    rw [← NNReal.coe_inv, ← NNReal.coe_mul]  -- TODO: Use `suffices` to make cleaner?
    rw [inv_mul_cancel₀ hp_pos.ne']
    simp

  rw [integral_integral_swap_of_hasCompactSupport hφf_cont hφf_supp]
  simp only [integral_mul_left]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0 : E) δ)]
  swap
  · intro x hx
    refine mul_eq_zero_of_left (Function.nmem_support.mp ?_) _
    simpa only [hφδ] using hx

  refine le_trans (integral_mono_of_nonneg ?_ ?_ ?_ (g := fun x ↦ φ.normed μ x * ε ^ (p : ℝ))) ?_
  · refine .of_forall fun t ↦ mul_nonneg (φ.nonneg_normed t) (integral_nonneg fun x ↦ ?_)
    simp [Real.rpow_nonneg]
  · exact φ.integrable_normed.restrict.mul_const _
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_ball]
    refine .of_forall fun t ht ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
    specialize hδ (-t) (by simpa using ht)
    replace hδ := ENNReal.rpow_le_rpow hδ (z := (p : ℝ)) (NNReal.zero_le_coe)
    rw [ENNReal.ofReal_rpow_of_nonneg hε.le NNReal.zero_le_coe] at hδ
    rw [Memℒp.eLpNorm_eq_integral_rpow_norm (ENNReal.coe_ne_zero.mpr hp_pos.ne')
      ENNReal.coe_ne_top] at hδ
    rotate_left
    · refine Memℒp.sub ?_ ?_
      · refine Continuous.memℒp_of_hasCompactSupport ?_ ?_
        · exact hf_cont.comp (continuous_add_right (-t))
        · exact .comp_homeomorph hf_supp (.addRight (-t))
      · exact hf_cont.memℒp_of_hasCompactSupport hf_supp
    -- TODO: Address all these non-negativity conditions!
    -- Maybe better to use `nnnorm`?
    rw [ENNReal.ofReal_rpow_of_nonneg _ NNReal.zero_le_coe] at hδ
    swap
    · exact Real.rpow_nonneg (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _) _
    rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hε.le _)] at hδ
    rw [← Real.rpow_mul] at hδ
    swap
    · exact integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
    rw [ENNReal.coe_toReal] at hδ
    rw [inv_mul_cancel₀ (NNReal.coe_ne_zero.mpr hp_pos.ne')] at hδ
    rw [Real.rpow_one] at hδ
    simp [← sub_eq_add_neg] at hδ
    exact hδ

  rw [integral_mul_right]
  refine mul_le_of_le_one_left (Real.rpow_nonneg hε.le _) ?_
  refine le_of_le_of_eq (setIntegral_le_integral φ.integrable_normed ?_) φ.integral_normed
  · refine Eventually.of_forall ?_
    simp [ContDiffBump.nonneg_normed]

-- TODO: Define using `ContMDiffMap`?
theorem ContDiff.toLp_denseRange [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormalSpace E]
    [WeaklyLocallyCompactSpace E]
    [HasContDiffBump E]
    [NormedSpace ℝ F] [CompleteSpace F]
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hp_top : p ≠ ⊤)
    (μ : Measure E := by volume_tac) [μ.Regular]
    [μ.IsAddRightInvariant] [μ.IsNegInvariant] [μ.IsAddLeftInvariant]
    [μ.IsOpenPosMeasure] :
    DenseRange (α := {f : E → F // ContDiff ℝ ∞ f ∧ HasCompactSupport f}) (X := Lp F p μ)
      (fun f ↦ (f.prop.1.continuous.memℒp_of_hasCompactSupport f.prop.2).toLp) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hfg⟩ := DenseRange.exists_dist_lt
    (CompactlySupportedContinuousMap.toLp_denseRange F hp_top μ) f (half_pos hε)
  obtain ⟨φ, hφ⟩ := exists_contDiffBump_eLpNorm_conv_sub_self_lt g.continuous g.hasCompactSupport
    p.toNNReal (ENNReal.le_toNNReal_of_coe_le hp.out hp_top) μ (ε / 2) (half_pos hε)
  -- TODO: Use `p : ENNReal` to avoid this ugliness?
  rw [ENNReal.coe_toNNReal hp_top] at hφ
  -- Show that `φ.normed μ ⋆ g` satisfies `ContDiff` and `HasCompactSupport`.
  refine ⟨⟨φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g, ⟨?_, ?_⟩⟩, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).locallyIntegrable
  · exact .convolution _ φ.hasCompactSupport_normed g.hasCompactSupport
  -- Apply triangle inequality.
  rw [← add_halves ε]
  refine lt_of_le_of_lt (dist_triangle f (g.memℒp p μ).toLp _) ?_
  refine add_lt_add_of_lt_of_le hfg ?_
  rw [dist_comm, Lp.dist_def]
  refine ENNReal.toReal_le_of_le_ofReal (half_pos hε).le ?_
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) hφ
  -- TODO: More idiomatic to solve with `filter_upwards`?
  exact .sub (Memℒp.coeFn_toLp _) (Memℒp.coeFn_toLp _)

end Smooth
