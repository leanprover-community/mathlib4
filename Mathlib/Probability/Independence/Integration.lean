/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara, Etienne Marion
-/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integrable
import Mathlib.Probability.Notation

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


open Set MeasureTheory

open scoped ENNReal MeasureTheory

variable {Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ≥0∞}
    {X Y : Ω → 𝕜}

namespace ProbabilityTheory

/-- If a random variable `f` in `ℝ≥0∞` is independent of an event `T`, then if you restrict the
  random variable to `T`, then `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
  `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`. -/
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hMf : Mf ≤ mΩ) (c : ℝ≥0∞) {T : Set Ω} (h_meas_T : MeasurableSet T)
    (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} μ) (h_meas_f : Measurable[Mf] f) :
    (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂μ) =
      (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂μ := by
  revert f
  have h_mul_indicator : ∀ g, Measurable g → Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    rw [lintegral_indicator (MeasurableSet.inter (hMf _ h_meas_s') h_meas_T),
      lintegral_indicator (hMf _ h_meas_s'), lintegral_indicator h_meas_T]
    simp only [lintegral_const, univ_inter,
      MeasurableSet.univ, Measure.restrict_apply]
    rw [IndepSets_iff] at h_ind
    rw [mul_mul_mul_comm, h_ind s' T h_meas_s' (Set.mem_singleton _)]
  · intro f' g _ h_meas_f' _ h_ind_f' h_ind_g
    have h_measM_f' : Measurable f' := h_meas_f'.mono hMf le_rfl
    simp_rw [Pi.add_apply, right_distrib]
    rw [lintegral_add_left (h_mul_indicator _ h_measM_f'), lintegral_add_left h_measM_f',
      right_distrib, h_ind_f', h_ind_g]
  · intro f h_meas_f h_mono_f h_ind_f
    have h_measM_f : ∀ n, Measurable (f n) := fun n => (h_meas_f n).mono hMf le_rfl
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup h_measM_f h_mono_f, lintegral_iSup, ENNReal.iSup_mul]
    · simp_rw [← h_ind_f]
    · exact fun n => h_mul_indicator _ (h_measM_f n)
    · exact fun m n h_le a => mul_le_mul_right' (h_mono_f h_le a) _

/--
If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
of the random variables, it uses the independence of measurable spaces for the
domains of `f` and `g`. This is similar to the sigma-algebra approach to
independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` for
a more common variant of the product of independent variables. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    {Mf Mg mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hMf : Mf ≤ mΩ) (hMg : Mg ≤ mΩ)
    (h_ind : Indep Mf Mg μ) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
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
    rw [lintegral_add_left h_measM_f', lintegral_add_left (h_measM_f.mul h_measM_f'), left_distrib,
      h_ind_f', h_ind_g']
  · intro f' h_meas_f' h_mono_f' h_ind_f'
    have h_measM_f' : ∀ n, Measurable (f' n) := fun n => (h_meas_f' n).mono hMg le_rfl
    simp_rw [ENNReal.mul_iSup]
    rw [lintegral_iSup, lintegral_iSup h_measM_f' h_mono_f', ENNReal.mul_iSup]
    · simp_rw [← h_ind_f']
    · exact fun n => h_measM_f.mul (h_measM_f' n)
    · exact fun n m (h_le : n ≤ m) a => mul_le_mul_left' (h_mono_f' h_le a) _

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : IndepFun f g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

/-- If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measurable,
then `E[f * g] = E[f] * E[g]` (slightly generalizing
`lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`). -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : IndepFun f g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk, lintegral_congr_ae h_meas_g.ae_eq_mk,
    lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurable_mk
      h_meas_g.measurable_mk
  exact h_indep_fun.congr h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk

theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : IndepFun f g μ) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

theorem lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ≥0∞) (hX : iIndepFun X μ)
    (x_mea : ∀ i, Measurable (X i)) :
    ∫⁻ ω, ∏ i ∈ s, (X i ω) ∂μ = ∏ i ∈ s, ∫⁻ ω, X i ω ∂μ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
    · exact (x_mea j).aemeasurable
    · exact s.aemeasurable_prod (fun i _ ↦ (x_mea i).aemeasurable)
    · exact (iIndepFun.indepFun_finset_prod_of_notMem hX x_mea hj).symm

/-- The product of two independent, integrable, real-valued random variables is integrable. -/
theorem IndepFun.integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (hX : Integrable X μ)
    (hY : Integrable Y μ) : Integrable (X * Y) μ := by
  let nX : Ω → ℝ≥0∞ := fun a => ‖X a‖ₑ
  let nY : Ω → ℝ≥0∞ := fun a => ‖Y a‖ₑ
  have hXY' : IndepFun nX nY μ := hXY.comp measurable_enorm measurable_enorm
  have hnX : AEMeasurable nX μ := hX.1.aemeasurable.enorm
  have hnY : AEMeasurable nY μ := hY.1.aemeasurable.enorm
  have hmul : ∫⁻ a, nX a * nY a ∂μ = (∫⁻ a, nX a ∂μ) * ∫⁻ a, nY a ∂μ :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' hnX hnY hXY'
  refine ⟨hX.1.mul hY.1, ?_⟩
  simp only [nX, nY] at hmul
  simp_rw [hasFiniteIntegral_iff_enorm, Pi.mul_apply, enorm_mul, hmul]
  exact ENNReal.mul_lt_top hX.2 hY.2

/-- If the product of two independent real-valued random variables is integrable and
the second one is not almost everywhere zero, then the first one is integrable. -/
theorem IndepFun.integrable_left_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [OpensMeasurableSpace β]
    (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖Y ω‖ₑ : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
  refine hasFiniteIntegral_iff_enorm.mpr <| lt_top_iff_ne_top.2 fun H => ?_
  have J : IndepFun (‖X ·‖ₑ) (‖Y ·‖ₑ) μ := hXY.comp measurable_enorm measurable_enorm
  have A : ∫⁻ ω, ‖X ω * Y ω‖ₑ ∂μ < ∞ := h'XY.2
  simp only [enorm_mul] at A
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.enorm hY.enorm J, H] at A
  simp only [ENNReal.top_mul I, lt_self_iff_false] at A

/-- If the product of two independent real-valued random variables is integrable and the
first one is not almost everywhere zero, then the second one is integrable. -/
theorem IndepFun.integrable_right_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [OpensMeasurableSpace β]
    (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  refine ⟨hY, ?_⟩
  have I : ∫⁻ ω, ‖X ω‖ₑ ∂μ ≠ 0 := fun H ↦ by
    have I : ((‖X ·‖ₑ) : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hX.enorm).1 H
    apply h'X
    filter_upwards [I] with ω hω
    simpa using hω
  refine lt_top_iff_ne_top.2 fun H => ?_
  have J : IndepFun (fun ω => ‖X ω‖ₑ : Ω → ℝ≥0∞) (fun ω => ‖Y ω‖ₑ : Ω → ℝ≥0∞) μ :=
    IndepFun.comp hXY measurable_enorm measurable_enorm
  have A : ∫⁻ ω, ‖X ω * Y ω‖ₑ ∂μ < ∞ := h'XY.2
  simp only [enorm_mul] at A
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.enorm hY.enorm J, H] at A
  simp only [ENNReal.mul_top I, lt_self_iff_false] at A

lemma IndepFun.integral_fun_comp_mul_comp {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) * g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) * ∫ ω, g (Y ω) ∂μ := by
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : ∀ᵐ ω ∂μ, f (X ω) = 0
  · have h' : ∀ᵐ ω ∂μ, f (X ω) * g (Y ω) = 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp [integral_congr_ae h'X, integral_congr_ae h']
  by_cases h'Y : ∀ᵐ ω ∂μ, g (Y ω) = 0
  · have h' : ∀ᵐ ω ∂μ, f (X ω) * g (Y ω) = 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp [integral_congr_ae h'Y, integral_congr_ae h']
  by_cases h : Integrable (fun ω ↦ f (X ω) * g (Y ω)) μ
  · have :=
      (hfXgY.integrable_left_of_integrable_mul h hfX hgY h'Y).isProbabilityMeasure_of_indepFun
        _ _ h'X hfXgY
    change ∫ ω, (fun x ↦ f x.1 * g x.2) (X ω, Y ω) ∂μ = _
    rw [← integral_map (f := fun x ↦ f x.1 * g x.2) (φ := fun ω ↦ (X ω, Y ω)),
      (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY, integral_prod_mul, integral_map,
      integral_map]
    any_goals fun_prop
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY]
    exact hf.comp_fst.mul hg.comp_snd
  · rw [integral_undef h]
    obtain h | h : ¬(Integrable (fun ω ↦ f (X ω)) μ) ∨ ¬(Integrable (fun ω ↦ g (Y ω)) μ) :=
      not_and_or.1 fun ⟨HX, HY⟩ ↦ h (hfXgY.integrable_mul HX HY)
    all_goals simp [integral_undef h]

lemma IndepFun.integral_comp_mul_comp {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) * (g ∘ Y)] = μ[f ∘ X] * μ[g ∘ Y] :=
  hXY.integral_fun_comp_mul_comp hX hY hf hg

lemma IndepFun.integral_mul_eq_mul_integral
    (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_comp_mul_comp hX.aemeasurable hY.aemeasurable
    aestronglyMeasurable_id aestronglyMeasurable_id

lemma IndepFun.integral_fun_mul_eq_mul_integral
    (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = μ[X] * μ[Y] :=
  hXY.integral_mul_eq_mul_integral hX hY

@[deprecated (since := "2025-07-30")] alias IndepFun.integral_mul_of_nonneg :=
  IndepFun.integral_mul_eq_mul_integral

@[deprecated (since := "2025-07-30")] alias IndepFun.integral_mul_of_integrable :=
  IndepFun.integral_mul_eq_mul_integral

@[deprecated (since := "2025-07-30")] alias IndepFun.integral_mul :=
  IndepFun.integral_mul_eq_mul_integral

@[deprecated (since := "2025-07-30")] alias IndepFun.integral_mul' :=
  IndepFun.integral_fun_mul_eq_mul_integral

/-- Independence of functions `f` and `g` into arbitrary types is characterized by the relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` with values in `ℝ`
  satisfying appropriate integrability conditions. -/
theorem indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} {f : Ω → β} {g : Ω → β'} {hfm : Measurable f} {hgm : Measurable g} :
    IndepFun f g μ ↔ ∀ {φ : β → ℝ} {ψ : β' → ℝ}, Measurable φ → Measurable ψ →
      Integrable (φ ∘ f) μ → Integrable (ψ ∘ g) μ →
        integral μ (φ ∘ f * ψ ∘ g) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) := by
  refine ⟨fun hfg _ _ hφ hψ _ _ => hfg.integral_comp_mul_comp
      hfm.aemeasurable hgm.aemeasurable hφ.aestronglyMeasurable hψ.aestronglyMeasurable, ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
      ((integrable_const 1).indicator (hfm.comp measurable_id hA))
      ((integrable_const 1).indicator (hgm.comp measurable_id hB))
  rwa [← ENNReal.toReal_eq_toReal (measure_ne_top μ _), ENNReal.toReal_mul, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, ← integral_indicator_one ((hfm hA).inter (hgm hB)),
    ← integral_indicator_one (hfm hA), ← integral_indicator_one (hgm hB), Set.inter_indicator_one]
  exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

variable {ι : Type*} [Fintype ι] {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
    {X : (i : ι) → Ω → 𝓧 i} {f : (i : ι) → 𝓧 i → 𝕜}

lemma iIndepFun.integral_fun_prod_comp (hX : iIndepFun X μ)
    (mX : ∀ i, AEMeasurable (X i) μ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    ∫ ω, ∏ i, f i (X i ω) ∂μ = ∏ i, ∫ ω, f i (X i ω) ∂μ := by
  have := hX.isProbabilityMeasure
  change ∫ ω, (fun x ↦ ∏ i, f i (x i)) (X · ω) ∂μ = _
  rw [← integral_map (f := fun x ↦ ∏ i, f i (x i)) (φ := fun ω ↦ (X · ω)),
    (iIndepFun_iff_map_fun_eq_pi_map mX).1 hX, integral_fintype_prod_eq_prod]
  · congr with i
    rw [integral_map (mX i) (hf i)]
  · fun_prop
  rw [(iIndepFun_iff_map_fun_eq_pi_map mX).1 hX]
  exact Finset.aestronglyMeasurable_fun_prod Finset.univ fun i _ ↦
    (hf i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)

lemma iIndepFun.integral_prod_comp (hX : iIndepFun X μ)
    (mX : ∀ i, AEMeasurable (X i) μ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    μ[∏ i, (f i) ∘ (X i)] = ∏ i, μ[(f i) ∘ (X i)] := by
  convert hX.integral_fun_prod_comp mX hf
  simp

variable {X : (i : ι) → Ω → 𝕜}

lemma iIndepFun.integral_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    μ[∏ i, X i] = ∏ i, μ[X i] :=
  hX.integral_prod_comp (fun i ↦ (mX i).aemeasurable) (fun _ ↦ aestronglyMeasurable_id)

lemma iIndepFun.integral_fun_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    ∫ ω, ∏ i, X i ω ∂μ = ∏ i, μ[X i] :=
  hX.integral_fun_prod_comp (fun i ↦ (mX i).aemeasurable) (fun _ ↦ aestronglyMeasurable_id)

end ProbabilityTheory
