/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Probability.Independence.Basic

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `MeasurableSpace` `M2` to define `μ`:

```lean
example {M1 : MeasurableSpace Ω} [M2 : MeasurableSpace Ω] {μ : Measure Ω} : sorry := sorry
example [M1 : MeasurableSpace Ω] {M2 : MeasurableSpace Ω} {μ : Measure Ω} : sorry := sorry
```

-/


noncomputable section

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal MeasureTheory

variable {Ω Ω' : Type*} {Mf Mg mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'} {κ : Kernel Ω' Ω} {f g : Ω → ℝ≥0∞} {X Y : Ω → ℝ}

namespace ProbabilityTheory

theorem Kernel.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
    (hMf : Mf ≤ mΩ) (c : ℝ≥0∞) {T : Set Ω} (h_meas_T : MeasurableSet T)
    (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} κ ν) (h_meas_f : Measurable[Mf] f) :
    ∀ᵐ ω' ∂ν,
      (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂(κ ω')) =
        (∫⁻ ω, f ω ∂(κ ω')) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂(κ ω') := by
  revert f
  have h_mul_indicator : ∀ g, Measurable g → Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    filter_upwards [h_ind s' T h_meas_s' (mem_singleton _)] with ω' hω'
    rw [lintegral_indicator (MeasurableSet.inter (hMf _ h_meas_s') h_meas_T),
      lintegral_indicator (hMf _ h_meas_s'), lintegral_indicator h_meas_T]
    simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter]
    rw [mul_mul_mul_comm, hω']
  · intro f' g _ h_meas_f' _ h_ind_f' h_ind_g
    have h_measM_f' : Measurable f' := h_meas_f'.mono hMf le_rfl
    simp_rw [Pi.add_apply, right_distrib]
    filter_upwards [h_ind_f', h_ind_g] with ω' h_ind_f' h_ind_g
    rw [lintegral_add_left (h_mul_indicator _ h_measM_f'), lintegral_add_left h_measM_f',
      right_distrib, h_ind_f', h_ind_g]
  · intro f h_meas_f h_mono_f h_ind_f
    have h_measM_f : ∀ n, Measurable (f n) := fun n => (h_meas_f n).mono hMf le_rfl
    simp_rw [ENNReal.iSup_mul]
    rw [← ae_all_iff] at h_ind_f
    filter_upwards [h_ind_f] with ω' h_ind_f
    rw [lintegral_iSup h_measM_f h_mono_f, lintegral_iSup, ENNReal.iSup_mul]
    · simp_rw [← h_ind_f]
    · exact fun n => h_mul_indicator _ (h_measM_f n)
    · exact fun m n h_le a => mul_le_mul_right' (h_mono_f h_le a) _

/-- If a random variable `f` in `ℝ≥0∞` is independent of an event `T`, then if you restrict the
  random variable to `T`, then `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
  `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`. -/
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
    (hMf : Mf ≤ mΩ) (c : ℝ≥0∞) {T : Set Ω} (h_meas_T : MeasurableSet T)
    (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} μ) (h_meas_f : Measurable[Mf] f) :
    (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂μ) =
      (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂μ := by
  simpa using Kernel.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf c h_meas_T
    h_ind h_meas_f

theorem Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (hMf : Mf ≤ mΩ) (hMg : Mg ≤ mΩ)
    (h_ind : Indep Mf Mg κ ν) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] g) :
    ∀ᵐ ω' ∂ν, ∫⁻ ω, f ω * g ω ∂(κ ω') = (∫⁻ ω, f ω ∂(κ ω')) * ∫⁻ ω, g ω ∂(κ ω') := by
  revert g
  have h_measM_f : Measurable f := h_meas_f.mono hMf le_rfl
  apply @Measurable.ennreal_induction _ Mg
  · intro c s h_s
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f
    apply indepSets_of_indepSets_of_le_right h_ind
    rwa [singleton_subset_iff]
  · intro f' g _ h_measMg_f' _ h_ind_f' h_ind_g'
    have h_measM_f' : Measurable f' := h_measMg_f'.mono hMg le_rfl
    simp_rw [Pi.add_apply, left_distrib]
    filter_upwards [h_ind_f', h_ind_g'] with ω' h_ind_f' h_ind_g'
    rw [lintegral_add_left h_measM_f', lintegral_add_left (h_measM_f.mul h_measM_f'), left_distrib,
      h_ind_f', h_ind_g']
  · intro f' h_meas_f' h_mono_f' h_ind_f'
    have h_measM_f' : ∀ n, Measurable (f' n) := fun n => (h_meas_f' n).mono hMg le_rfl
    simp_rw [ENNReal.mul_iSup]
    rw [← ae_all_iff] at h_ind_f'
    filter_upwards [h_ind_f'] with ω' h_ind_f'
    rw [lintegral_iSup, lintegral_iSup h_measM_f' h_mono_f', ENNReal.mul_iSup]
    · simp_rw [← h_ind_f']
    · exact fun n => h_measM_f.mul (h_measM_f' n)
    · exact fun n m (h_le : n ≤ m) a => mul_le_mul_left' (h_mono_f' h_le a) _

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` for
   a more common variant of the product of independent variables. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (hMf : Mf ≤ mΩ) (hMg : Mg ≤ mΩ)
    (h_ind : Indep Mf Mg μ) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  simpa using Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hMf hMg
    h_ind h_meas_f h_meas_g

theorem Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : IndepFun f g κ ν) :
    ∀ᵐ ω' ∂ν, (∫⁻ ω, (f * g) ω ∂(κ ω')) = (∫⁻ ω, f ω ∂(κ ω')) * ∫⁻ ω, g ω ∂(κ ω') :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
   then `E[f * g] = E[f] * E[g]`. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : IndepFun f g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  simpa using Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f h_meas_g
    h_indep_fun

theorem Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
    -- todo: h_meas_f could be `AEMeasurable f (ν ⊗ₘ κ)`
    (h_meas_f : ∃ f', Measurable f' ∧ ∀ᵐ ω' ∂ν, f =ᵐ[κ ω'] f')
    (h_meas_g : ∃ g', Measurable g' ∧ ∀ᵐ ω' ∂ν, g =ᵐ[κ ω'] g')
    (h_indep_fun : IndepFun f g κ ν) :
    ∀ᵐ ω' ∂ν, ∫⁻ ω, (f * g) ω ∂(κ ω') = (∫⁻ ω, f ω ∂(κ ω')) * ∫⁻ ω, g ω ∂(κ ω') := by
  obtain ⟨f', h_meas_f', hf⟩ := h_meas_f
  obtain ⟨g', h_meas_g', hg⟩ := h_meas_g
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f' h_meas_g'
    (h_indep_fun.ae_eq hf hg)
  filter_upwards [h, hf, hg] with ω' h hf hg
  have fg_ae : f * g =ᵐ[κ ω'] f' * g' := hf.mul hg
  rw [lintegral_congr_ae hf, lintegral_congr_ae hg, lintegral_congr_ae fg_ae, h]

/-- If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measurable,
   then `E[f * g] = E[f] * E[g]` (slightly generalizing
   `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`). -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : IndepFun f g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  convert Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' ?_ ?_ h_indep_fun
  · simp
  · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
    exact h_meas_f
  · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
    exact h_meas_g

theorem Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (h_meas_f : ∃ f', Measurable f' ∧ ∀ᵐ ω' ∂ν, f =ᵐ[κ ω'] f')
    (h_meas_g : ∃ g', Measurable g' ∧ ∀ᵐ ω' ∂ν, g =ᵐ[κ ω'] g')
    (h_indep_fun : IndepFun f g κ ν) :
    ∀ᵐ ω' ∂ν, ∫⁻ ω, f ω * g ω ∂(κ ω') = (∫⁻ ω, f ω ∂(κ ω')) * ∫⁻ ω, g ω ∂(κ ω') :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : IndepFun f g μ) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

theorem Kernel.lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : iIndepFun (fun _ ↦ ENNReal.measurableSpace) X κ ν)
    (x_mea : ∀ i, Measurable (X i)) :
    ∀ᵐ ω' ∂ν, ∫⁻ ω, ∏ i ∈ s, (X i ω) ∂(κ ω') = ∏ i ∈ s, ∫⁻ ω, X i ω ∂(κ ω') := by
  have : ∀ᵐ ω' ∂ν, IsProbabilityMeasure (κ ω') := hX.ae_isProbabilityMeasure
  induction s using Finset.induction
  case empty => filter_upwards [this] with ω' h_prop; simp
  case insert _ j s hj v =>
    have h_prod : Measurable (∏ i ∈ s, X i) := by fun_prop
    filter_upwards [v, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (x_mea j) h_prod
      (iIndepFun.indepFun_finset_prod_of_not_mem hX (fun i ↦ x_mea i) hj).symm] with ω' v h_eq
    calc  ∫⁻ ω, ∏ i ∈ insert j s, X i ω ∂(κ ω')
      _ = ∫⁻ ω, (∏ i ∈ insert j s, X i) ω ∂(κ ω') := by simp only [Finset.prod_apply]
      _ =  ∫⁻ ω, (X j * ∏ i ∈ s, X i) ω ∂(κ ω') :=
        lintegral_congr fun ω ↦ congrFun (Finset.prod_insert hj) ω
      _ = (∫⁻ ω, X j ω ∂(κ ω')) * ∫⁻ ω, (∏ i ∈ s, X i) ω ∂(κ ω') := h_eq
      _ = ∏ i' ∈ insert j s, ∫⁻ ω, X i' ω ∂(κ ω') := by
        simp only [Finset.prod_apply]
        rw [v, Finset.prod_insert hj]

theorem lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : iIndepFun (fun _ ↦ ENNReal.measurableSpace) X μ)
    (x_mea : ∀ i, Measurable (X i)) :
    ∫⁻ ω, ∏ i ∈ s, (X i ω) ∂μ = ∏ i ∈ s, ∫⁻ ω, X i ω ∂μ := by
  simpa using Kernel.lintegral_prod_eq_prod_lintegral_of_indepFun s X hX x_mea

/-- The product of two independent, integrable, real-valued random variables is integrable. -/
theorem Kernel.IndepFun.integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    (∃ f, StronglyMeasurable f ∧ ∀ᵐ ω' ∂ν, X * Y =ᵐ[κ ω'] f)
      ∧ ∀ᵐ ω' ∂ν, Integrable X (κ ω') → Integrable Y (κ ω') → Integrable (X * Y) (κ ω') := by
  have hXY' : IndepFun (fun a => ‖X a‖ₑ) (fun a => ‖Y a‖ₑ) κ ν :=
    hXY.comp measurable_enorm measurable_enorm
  obtain ⟨X', hX', hXX'⟩ := hX
  obtain ⟨Y', hY', hYY'⟩ := hY
  have h_mul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' ?_ ?_ hXY'
  rotate_left
  · refine ⟨fun a => ‖X' a‖ₑ, ?_, ?_⟩
    · have := hX'.measurable
      fun_prop
    · filter_upwards [hXX'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  · refine ⟨fun a => ‖Y' a‖ₑ, ?_, ?_⟩
    · have := hY'.measurable
      fun_prop
    · filter_upwards [hYY'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  refine ⟨⟨X' * Y', hX'.mul hY', ?_⟩, ?_⟩
  · filter_upwards [hXX', hYY'] with ω' hX' hY' using hX'.mul hY'
  filter_upwards [h_mul, hXX', hYY'] with ω' hmul hXX' hYY' hX_int hY_int
  simp only [Pi.mul_apply] at hmul
  refine ⟨?_, ?_⟩
  · refine ⟨X' * Y', hX'.mul hY', ?_⟩
    filter_upwards [hXX', hYY'] with ω hXX' hYY'
    simp [hXX', hYY']
  · simp_rw [hasFiniteIntegral_iff_enorm, Pi.mul_apply, enorm_mul, hmul]
    exact ENNReal.mul_lt_top hX_int.2 hY_int.2

/-- The product of two independent, integrable, real-valued random variables is integrable. -/
theorem IndepFun.integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (hX : Integrable X μ)
    (hY : Integrable Y μ) : Integrable (X * Y) μ := by
  have h := Kernel.IndepFun.integrable_mul hXY ?_ ?_
  all_goals simp_all only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure, forall_const]
  exacts [hX.1, hY.1]

theorem Kernel.IndepFun.integrable_left_of_integrable_mul
    {β : Type*} [MeasurableSpace β] {X Y : Ω → β} [NormedDivisionRing β] [BorelSpace β]
    (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν, Integrable (X * Y) (κ ω') → ¬Y =ᵐ[κ ω'] 0 → Integrable X (κ ω') := by
  let ⟨X', hX', hXX'⟩ := hX
  let ⟨Y', hY', hYY'⟩ := hY
  have J : IndepFun (‖X ·‖ₑ) (‖Y ·‖ₑ) κ ν := hXY.comp measurable_enorm measurable_enorm
  have h_ind := Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' ?_ ?_ J
  rotate_left
  · refine ⟨fun ω ↦ ‖X' ω‖ₑ, ?_, ?_⟩
    · have := hX'.measurable
      fun_prop
    · filter_upwards [hXX'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  · refine ⟨fun ω ↦ ‖Y' ω‖ₑ, ?_, ?_⟩
    · have := hY'.measurable
      fun_prop
    · filter_upwards [hYY'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  filter_upwards [hXX', hYY', h_ind] with ω' hXX' hYY' h_ind hXY_int h'Y
  refine ⟨⟨X', hX', hXX'⟩, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂(κ ω')) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖Y ω‖ₑ : Ω → ℝ≥0∞) =ᵐ[κ ω'] 0 := (lintegral_eq_zero_iff' ?_).1 H
    · apply h'Y
      filter_upwards [I] with ω hω
      simpa using hω
    · refine ⟨fun ω ↦ ‖Y' ω‖ₑ, ?_, ?_⟩
      · have := hY'.measurable
        fun_prop
      · filter_upwards [hYY'] with ω hω
        rw [hω]
  refine hasFiniteIntegral_iff_enorm.mpr <| lt_top_iff_ne_top.2 fun H => ?_
  have A : ∫⁻ ω, ‖X ω * Y ω‖ₑ ∂(κ ω') < ∞ := hXY_int.2
  simp only [enorm_mul, ENNReal.coe_mul] at A
  rw [h_ind, H] at A
  simp only [ENNReal.top_mul I, lt_self_iff_false] at A

/-- If the product of two independent real-valued random variables is integrable and
the second one is not almost everywhere zero, then the first one is integrable. -/
theorem IndepFun.integrable_left_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  have h := Kernel.IndepFun.integrable_left_of_integrable_mul hXY ?_ ?_
  all_goals simp_all only [Kernel.const_apply, not_false_eq_true, forall_const, ae_dirac_eq,
    Filter.eventually_pure]
  exacts [hX, hY]

theorem Kernel.IndepFun.integrable_right_of_integrable_mul
    {β : Type*} [MeasurableSpace β] {X Y : Ω → β} [NormedDivisionRing β] [BorelSpace β]
    (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν, Integrable (X * Y) (κ ω') → ¬X =ᵐ[κ ω'] 0 → Integrable Y (κ ω') := by
  let ⟨X', hX', hXX'⟩ := hX
  let ⟨Y', hY', hYY'⟩ := hY
  have J : IndepFun (‖X ·‖ₑ) (‖Y ·‖ₑ) κ ν := hXY.comp measurable_enorm measurable_enorm
  have h_ind := Kernel.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' ?_ ?_ J
  rotate_left
  · refine ⟨fun ω ↦ ‖X' ω‖ₑ, ?_, ?_⟩
    · have := hX'.measurable
      fun_prop
    · filter_upwards [hXX'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  · refine ⟨fun ω ↦ ‖Y' ω‖ₑ, ?_, ?_⟩
    · have := hY'.measurable
      fun_prop
    · filter_upwards [hYY'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  filter_upwards [hXX', hYY', h_ind] with ω' hXX' hYY' h_ind hXY_int h'X
  refine ⟨⟨Y', hY', hYY'⟩, ?_⟩
  have I : (∫⁻ ω, ‖X ω‖ₑ ∂(κ ω')) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖X ω‖ₑ : Ω → ℝ≥0∞) =ᵐ[κ ω'] 0 := (lintegral_eq_zero_iff' ?_).1 H
    · apply h'X
      filter_upwards [I] with ω hω
      simpa using hω
    · refine ⟨fun ω ↦ ‖X' ω‖ₑ, ?_, ?_⟩
      · have := hX'.measurable
        fun_prop
      · filter_upwards [hXX'] with ω hω
        rw [hω]
  refine hasFiniteIntegral_iff_enorm.mpr <| lt_top_iff_ne_top.2 fun H => ?_
  have A : ∫⁻ ω, ‖X ω * Y ω‖ₑ ∂(κ ω') < ∞ := hXY_int.2
  simp only [enorm_mul, ENNReal.coe_mul] at A
  rw [h_ind, H] at A
  simp only [ENNReal.mul_top I, lt_self_iff_false] at A

/-- If the product of two independent real-valued random variables is integrable and the
first one is not almost everywhere zero, then the second one is integrable. -/
theorem IndepFun.integrable_right_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  have h := Kernel.IndepFun.integrable_right_of_integrable_mul hXY ?_ ?_
  all_goals simp_all only [Kernel.const_apply, not_false_eq_true, forall_const, ae_dirac_eq,
    Filter.eventually_pure]
  exacts [hX, hY]

theorem Kernel.IndepFun.integral_mul_of_nonneg (hXY : IndepFun X Y κ ν) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
    (hXm : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hYm : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν , integral (κ ω') (X * Y) = integral (κ ω') X * integral (κ ω') Y := by
  obtain ⟨X', hX', hXX'⟩ := hXm
  obtain ⟨Y', hY', hYY'⟩ := hYm
  have h_ind_ofReal : IndepFun (fun a ↦ ENNReal.ofReal (X a)) (fun a ↦ ENNReal.ofReal (Y a)) κ ν :=
    hXY.comp ENNReal.measurable_ofReal ENNReal.measurable_ofReal
  have h_mul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' ?_ ?_ h_ind_ofReal
  rotate_left
  · refine ⟨fun a => ENNReal.ofReal (X' a), ?_, ?_⟩
    · have := hX'.measurable
      fun_prop
    · filter_upwards [hXX'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  · refine ⟨fun a => ENNReal.ofReal (Y' a), ?_, ?_⟩
    · have := hY'.measurable
      fun_prop
    · filter_upwards [hYY'] with ω' hω'
      filter_upwards [hω'] with ω hω
      rw [hω]
  filter_upwards [h_mul, hXX', hYY'] with ω' h_mul hXX' hYY'
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ ?_),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hXp),
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hYp)]
  rotate_left
  · exact ⟨Y', hY', hYY'⟩
  · exact ⟨X', hX', hXX'⟩
  · refine ⟨X' * Y', hX'.mul hY', ?_⟩
    filter_upwards [hXX', hYY'] with ω hX hY
    simp [hX, hY]
  · simpa using mul_nonneg (hXp ω) (hYp ω)
  simp only [Pi.mul_apply, ENNReal.ofReal_mul (hXp _), ← ENNReal.toReal_mul]
  congr

/-- The (Bochner) integral of the product of two independent, nonnegative random
  variables is the product of their integrals. The proof is just plumbing around
  `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'`. -/
theorem IndepFun.integral_mul_of_nonneg (hXY : IndepFun X Y μ) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ) :
    integral μ (X * Y) = integral μ X * integral μ Y := by
  have h := Kernel.IndepFun.integral_mul_of_nonneg hXY ?_ ?_ ?_ ?_
  all_goals simp_all only [Kernel.const_apply, not_false_eq_true, ae_dirac_eq,
    Filter.eventually_pure, forall_const]
  exacts [hXm.aestronglyMeasurable, hYm.aestronglyMeasurable]

theorem Kernel.IndepFun.integral_mul_of_integrable (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν, Integrable X (κ ω') → Integrable Y (κ ω') →
      integral (κ ω') (X * Y) = integral (κ ω') X * integral (κ ω') Y := by
  let pos : ℝ → ℝ := fun x => max x 0
  let neg : ℝ → ℝ := fun x => max (-x) 0
  have posm : Measurable pos := measurable_id'.max measurable_const
  have negm : Measurable neg := measurable_id'.neg.max measurable_const
  let Xp := pos ∘ X
  let Xm := neg ∘ X
  let Yp := pos ∘ Y
  let Ym := neg ∘ Y
  have hXpm : X = Xp - Xm := funext fun ω => (max_zero_sub_max_neg_zero_eq_self (X ω)).symm
  have hYpm : Y = Yp - Ym := funext fun ω => (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm
  have hp1 : 0 ≤ Xm := fun ω => le_max_right _ _
  have hp2 : 0 ≤ Xp := fun ω => le_max_right _ _
  have hp3 : 0 ≤ Ym := fun ω => le_max_right _ _
  have hp4 : 0 ≤ Yp := fun ω => le_max_right _ _
  obtain ⟨X', hX', hXX'⟩ := hX
  obtain ⟨Y', hY', hYY'⟩ := hY
  have hm1 : ∃ f, StronglyMeasurable f ∧ ∀ᵐ ω' ∂ν, Xm =ᵐ[κ ω'] f := by
    refine ⟨neg ∘ X', (negm.comp hX'.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [hXX'] with ω' hω'
    filter_upwards [hω'] with ω hω
    simp [hω, Xm]
  have hm2 : ∃ f, StronglyMeasurable f ∧ ∀ᵐ ω' ∂ν, Xp =ᵐ[κ ω'] f := by
    refine ⟨pos ∘ X', (posm.comp hX'.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [hXX'] with ω' hω'
    filter_upwards [hω'] with ω hω
    simp [hω, Xp]
  have hm3 : ∃ f, StronglyMeasurable f ∧ ∀ᵐ ω' ∂ν, Ym =ᵐ[κ ω'] f := by
    refine ⟨neg ∘ Y', (negm.comp hY'.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [hYY'] with ω' hω'
    filter_upwards [hω'] with ω hω
    simp [hω, Ym]
  have hm4 : ∃ f, StronglyMeasurable f ∧ ∀ᵐ ω' ∂ν, Yp =ᵐ[κ ω'] f := by
    refine ⟨pos ∘ Y', (posm.comp hY'.measurable).stronglyMeasurable, ?_⟩
    filter_upwards [hYY'] with ω' hω'
    filter_upwards [hω'] with ω hω
    simp [hω, Yp]
  have hi1 : IndepFun Xm Ym κ ν := hXY.comp negm negm
  have hi2 : IndepFun Xp Ym κ ν := hXY.comp posm negm
  have hi3 : IndepFun Xm Yp κ ν := hXY.comp negm posm
  have hi4 : IndepFun Xp Yp κ ν := hXY.comp posm posm
  have hl1' : ∀ᵐ ω' ∂ν, Integrable Xm (κ ω') → Integrable Ym (κ ω') → Integrable (Xm * Ym) (κ ω') :=
    (hi1.integrable_mul hm1 hm3).2
  have hl2' : ∀ᵐ ω' ∂ν, Integrable Xp (κ ω') → Integrable Ym (κ ω') → Integrable (Xp * Ym) (κ ω') :=
    (hi2.integrable_mul hm2 hm3).2
  have hl3' : ∀ᵐ ω' ∂ν, Integrable Xm (κ ω') → Integrable Yp (κ ω') → Integrable (Xm * Yp) (κ ω') :=
    (hi3.integrable_mul hm1 hm4).2
  have hl4' : ∀ᵐ ω' ∂ν, Integrable Xp (κ ω') → Integrable Yp (κ ω') → Integrable (Xp * Yp) (κ ω') :=
    (hi4.integrable_mul hm2 hm4).2
  have h_mul_1 := hi1.integral_mul_of_nonneg hp1 hp3 hm1 hm3
  have h_mul_2 := hi2.integral_mul_of_nonneg hp2 hp3 hm2 hm3
  have h_mul_3 := hi3.integral_mul_of_nonneg hp1 hp4 hm1 hm4
  have h_mul_4 := hi4.integral_mul_of_nonneg hp2 hp4 hm2 hm4
  filter_upwards [h_mul_1, h_mul_2, h_mul_3, h_mul_4, hl1', hl2', hl3', hl4']
    with ω' h1 h2 h3 h4 hl1' hl2' hl3' hl4' hX_int hY_int
  have hv1 : Integrable Xm (κ ω') := hX_int.neg_part
  have hv2 : Integrable Xp (κ ω') := hX_int.pos_part
  have hv3 : Integrable Ym (κ ω') := hY_int.neg_part
  have hv4 : Integrable Yp (κ ω') := hY_int.pos_part
  have hl1 : Integrable (Xm * Ym) (κ ω') := hl1' hv1 hv3
  have hl2 : Integrable (Xp * Ym) (κ ω') := hl2' hv2 hv3
  have hl3 : Integrable (Xm * Yp) (κ ω') := hl3' hv1 hv4
  have hl4 : Integrable (Xp * Yp) (κ ω') := hl4' hv2 hv4
  have hl5 : Integrable (Xp * Yp - Xm * Yp) (κ ω') := hl4.sub hl3
  have hl6 : Integrable (Xp * Ym - Xm * Ym) (κ ω') := hl2.sub hl1
  rw [hXpm, hYpm, mul_sub, sub_mul, sub_mul, integral_sub' hl5 hl6, integral_sub' hl4 hl3,
    integral_sub' hl2 hl1, integral_sub' hv2 hv1, integral_sub' hv4 hv3, h1, h2, h3, h4]
  ring

/-- The (Bochner) integral of the product of two independent, integrable random
  variables is the product of their integrals. The proof is pedestrian decomposition
  into their positive and negative parts in order to apply `IndepFun.integral_mul_of_nonneg`
  four times. -/
theorem IndepFun.integral_mul_of_integrable (hXY : IndepFun X Y μ) (hX : Integrable X μ)
    (hY : Integrable Y μ) : integral μ (X * Y) = integral μ X * integral μ Y := by
  have h := Kernel.IndepFun.integral_mul_of_integrable hXY ?_ ?_
  all_goals simp_all only [Kernel.const_apply, not_false_eq_true, ae_dirac_eq,
    Filter.eventually_pure, forall_const]
  exacts [hX.1, hY.1]

theorem Kernel.IndepFun.integral_mul (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν, integral (κ ω') (X * Y) = integral (κ ω') X * integral (κ ω') Y := by
  have h_left := hXY.integrable_left_of_integrable_mul hX hY
  have h_right := hXY.integrable_right_of_integrable_mul hX hY
  have h_mul := hXY.integral_mul_of_integrable hX hY
  have h_int := hXY.integrable_mul hX hY
  filter_upwards [h_left, h_right, h_mul, h_int.2] with ω' h_left h_right h_mul h_int
  by_cases h'X : X =ᵐ[κ ω'] 0
  · have h' : X * Y =ᵐ[κ ω'] 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp only [integral_congr_ae h'X, integral_congr_ae h', Pi.zero_apply, integral_const,
      Algebra.id.smul_eq_mul, mul_zero, zero_mul]
  by_cases h'Y : Y =ᵐ[κ ω'] 0
  · have h' : X * Y =ᵐ[κ ω'] 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp only [integral_congr_ae h'Y, integral_congr_ae h', Pi.zero_apply, integral_const,
      Algebra.id.smul_eq_mul, mul_zero, zero_mul]
  by_cases h : Integrable (X * Y) (κ ω')
  · have HX : Integrable X (κ ω') := h_left h h'Y
    have HY : Integrable Y (κ ω') := h_right h h'X
    exact h_mul HX HY
  · rw [integral_undef h]
    have I : ¬(Integrable X (κ ω') ∧ Integrable Y (κ ω')) := by
      rintro ⟨HX, HY⟩
      exact h (h_int HX HY)
    rw [not_and_or] at I
    cases' I with I I <;> simp [integral_undef I]

/-- The (Bochner) integral of the product of two independent random
  variables is the product of their integrals. -/
theorem IndepFun.integral_mul (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : integral μ (X * Y) = integral μ X * integral μ Y := by
  have h := Kernel.IndepFun.integral_mul hXY ?_ ?_
  all_goals simp_all only [Kernel.const_apply, not_false_eq_true, ae_dirac_eq,
    Filter.eventually_pure, forall_const]
  exacts [hX, hY]

theorem Kernel.IndepFun.integral_mul' (hXY : IndepFun X Y κ ν)
    (hX : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (hY : ∃ Y', StronglyMeasurable Y' ∧ ∀ᵐ ω' ∂ν, Y =ᵐ[κ ω'] Y') :
    ∀ᵐ ω' ∂ν, (integral (κ ω') fun ω ↦ X ω * Y ω) = integral (κ ω') X * integral (κ ω') Y :=
  hXY.integral_mul hX hY

theorem IndepFun.integral_mul' (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) :
    (integral μ fun ω => X ω * Y ω) = integral μ X * integral μ Y :=
  hXY.integral_mul hX hY

/-- Independence of functions `f` and `g` into arbitrary types is characterized by the relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` with values in `ℝ`
  satisfying appropriate integrability conditions. -/
theorem indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} {f : Ω → β} {g : Ω → β'} {hfm : Measurable f} {hgm : Measurable g} :
    IndepFun f g μ ↔ ∀ {φ : β → ℝ} {ψ : β' → ℝ}, Measurable φ → Measurable ψ →
      Integrable (φ ∘ f) μ → Integrable (ψ ∘ g) μ →
        integral μ (φ ∘ f * ψ ∘ g) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) := by
  refine ⟨fun hfg _ _ hφ hψ => IndepFun.integral_mul_of_integrable (hfg.comp hφ hψ), ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
      ((integrable_const 1).indicator (hfm.comp measurable_id hA))
      ((integrable_const 1).indicator (hgm.comp measurable_id hB))
  rwa [← ENNReal.toReal_eq_toReal (measure_ne_top μ _), ENNReal.toReal_mul, ←
    integral_indicator_one ((hfm hA).inter (hgm hB)), ← integral_indicator_one (hfm hA), ←
    integral_indicator_one (hgm hB), Set.inter_indicator_one]
  exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

end ProbabilityTheory
