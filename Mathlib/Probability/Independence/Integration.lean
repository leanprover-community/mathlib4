/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.Probability.Notation

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

public section


open Set MeasureTheory ENNReal

open scoped NNReal MeasureTheory

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
    simp_rw [iSup_mul]
    rw [lintegral_iSup h_measM_f h_mono_f, lintegral_iSup, iSup_mul]
    · simp_rw [← h_ind_f]
    · exact fun n => h_mul_indicator _ (h_measM_f n)
    · exact fun m n h_le a => mul_le_mul_left (h_mono_f h_le a) _

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
    simp_rw [mul_iSup]
    rw [lintegral_iSup, lintegral_iSup h_measM_f' h_mono_f', mul_iSup]
    · simp_rw [← h_ind_f']
    · exact fun n => h_measM_f.mul (h_measM_f' n)
    · exact fun n m (h_le : n ≤ m) a => mul_le_mul_right (h_mono_f' h_le a) _

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

/-- If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measurable,
then `E[f * g] = E[f] * E[g]` (slightly generalizing
`lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`). -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk, lintegral_congr_ae h_meas_g.ae_eq_mk,
    lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurable_mk
      h_meas_g.measurable_mk
  exact h_indep_fun.congr h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk

theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
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
    · exact (iIndepFun.indepFun_finsetProd_of_notMem hX x_mea hj).symm

section Integral

variable {𝓧 𝓨 E F G : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- If `X` and `Y` are two independent and integrable random variables, and `B` is a function of
two variables such that `‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ`, then `B X Y` is integrable.

This is useful in particular if `B` is a continuous bilinear map. -/
theorem IndepFun.integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E → F → G) (cB : Continuous B.uncurry) (C : ℝ≥0) (hB : ∀ x y, ‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ) :
    Integrable (fun ω ↦ B (X ω) (Y ω)) μ := by
  refine ⟨cB.comp_aestronglyMeasurable₂ hX.1 hY.1, ?_⟩
  unfold HasFiniteIntegral
  calc
  _ ≤ C * ∫⁻ ω, ‖X ω‖ₑ * ‖Y ω‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ (by fun_prop)]
    gcongr with ω
    simp [← mul_assoc, hB]
  _ = C * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.1.enorm hY.1.enorm
        (hXY.comp measurable_enorm measurable_enorm)]
  _ < ∞ := mul_lt_top (by finiteness) (mul_lt_top hX.2 hY.2)

/-- A continuous bilinear map applied to two independent and integrable random variables
is integrable. -/
theorem IndepFun.integrable_bilin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E →L[𝕜] F →L[𝕜] G) :
    Integrable (fun ω ↦ B (X ω) (Y ω)) μ := by
  refine hXY.integrable_op hX hY (B · ·) (by fun_prop) ‖B‖.toNNReal (fun x y ↦ ?_)
  rw [← toReal_le_toReal (by finiteness) (by finiteness)]
  simp [B.le_opNorm₂]

/-- If `X` and `Y` are two independent random variables, `B X Y` is integrable, `Y` is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `X` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow to drop
integrability hypotheses. -/
theorem IndepFun.integrable_left_of_integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E → F → G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω ↦ B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖Y ω‖ₑ : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
  refine hasFiniteIntegral_iff_enorm.mpr <| lt_top_iff_ne_top.2 fun H => ?_
  have J : (‖X ·‖ₑ) ⟂ᵢ[μ] (‖Y ·‖ₑ) := hXY.comp measurable_enorm measurable_enorm
  have : ∞ < ∞ := calc
    ∞ = c * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
      rw [H, top_mul I, mul_top (by simpa)]
    _ ≤ ∫⁻ ω, ‖B (X ω) (Y ω)‖ₑ ∂μ := by
      rw [← lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.enorm hY.enorm J,
        ← lintegral_const_mul'' _ (by fun_prop)]
      gcongr with ω
      simp [hB, ← mul_assoc]
    _ < ∞ := h'XY.2
  contradiction

/-- If `X` and `Y` are two independent random variables, `B X Y` is integrable, `X` is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `Y` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow to drop
integrability hypotheses. -/
theorem IndepFun.integrable_right_of_integrable_op
    [NormedAddGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E → F → G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω ↦ B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  refine hXY.symm.integrable_left_of_integrable_op (Function.swap B) c hc (fun y x ↦ ?_)
    h'XY hY hX h'X
  grw [mul_right_comm, hB]

/-- If `X` and `Y` are independent random variables such that `f(X)` and `g(Y)` are integrable
and `B` is a continuous bilinear map, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).` -/
theorem IndepFun.integral_bilin_comp_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : Integrable f (μ.map X)) (hg : Integrable g (μ.map Y)) (B : E →L[𝕜] F →L[𝕜] G) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  by_cases h : ∀ᵐ ω ∂μ, f (X ω) = 0
  · have h1 : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    simp [integral_congr_ae h1, integral_congr_ae h]
  borelize E F
  have : IsProbabilityMeasure μ :=
    (hf.comp_aemeasurable hX).isProbabilityMeasure_of_indepFun (f ∘ X) (g ∘ Y) h
      (hXY.comp₀ hX hY hf.1.aemeasurable hg.1.aemeasurable)
  rw [← integral_map (f := fun z ↦ B (f z.1) (g z.2)) (φ := fun ω ↦ (X ω, Y ω)) (by fun_prop),
    (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY,
    integral_prod_bilin _ hf hg, integral_map hX hf.1, integral_map hY hg.1]
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY]
  exact Continuous.comp_aestronglyMeasurable₂ (g := (B · ·)) (by fun_prop)
    hf.1.comp_fst hg.1.comp_snd

/-- If `X` and `Y` are random variables and `B` is a continuous bilinear map
such that `∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖`, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).`

The assumtion on `B` allows to drop the integrability condition in
`IndepFun.integral_bilin_comp_comp`, which is useful for the versions where `B` is the scalar
multiplication or the multiplication. -/
theorem IndepFun.integral_bilin_comp_comp'
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y))
    (B : E →L[𝕜] F →L[𝕜] G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  borelize E F
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : ∀ᵐ ω ∂μ, f (X ω) = 0
  · have h' : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp [integral_congr_ae h'X, integral_congr_ae h']
  by_cases h'Y : ∀ᵐ ω ∂μ, g (Y ω) = 0
  · have h' : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp [integral_congr_ae h'Y, integral_congr_ae h']
  have hB x y : c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ := by
    rw [← toReal_le_toReal]
    · simpa using hB x y
    all_goals finiteness
  by_cases h : Integrable (fun ω ↦ B (f (X ω)) (g (Y ω))) μ
  · have h1 : Integrable f (μ.map X) := (integrable_map_measure hf hX).2 <|
      hfXgY.integrable_left_of_integrable_op (B · ·) c hc hB h hfX hgY h'Y
    have h2 : Integrable g (μ.map Y) := (integrable_map_measure hg hY).2 <|
      hfXgY.integrable_right_of_integrable_op (B · ·) c hc hB h hfX hgY h'X
    exact hXY.integral_bilin_comp_comp hX hY h1 h2 B
  · rw [integral_undef h]
    obtain h | h : ¬(Integrable (fun ω ↦ f (X ω)) μ) ∨ ¬(Integrable (fun ω ↦ g (Y ω)) μ) :=
      not_and_or.1 fun ⟨HX, HY⟩ ↦ h (hfXgY.integrable_bilin HX HY B)
    all_goals simp [integral_undef h]

/-- If `X` and `Y` are independent and integrable random variables and `B`
is a continuous bilinear map, then `∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y].` -/
theorem IndepFun.integral_bilin
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y] :=
  hXY.integral_bilin_comp_comp hX.aemeasurable hY.aemeasurable
    ((integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).2 hX)
    ((integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).2 hY) B

/-- The scalar product of two independent and integrable random variables is integrable. -/
theorem IndepFun.integrable_smul
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SMul E F] [ContinuousSMul E F] [ENormSMulClass E F]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (fun ω ↦ (X ω) • (Y ω)) μ :=
  hXY.integrable_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

/-- The product of two independent and integrable random variables is integrable. -/
theorem IndepFun.integrable_mul
    [TopologicalSpace E] [ContinuousENorm E] [Mul E] [ContinuousMul E] [ENormSMulClass E E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {X Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ := hXY.integrable_smul hX hY

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_left_of_integrable_mul :=
  IndepFun.integrable_left_of_integrable_op

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_right_of_integrable_mul :=
  IndepFun.integrable_right_of_integrable_op

lemma IndepFun.integral_fun_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) • g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) • (∫ ω, g (Y ω) ∂μ) := by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin_comp_comp' hX hY hf hg (.lsmul ℝ 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

lemma IndepFun.integral_fun_comp_mul_comp
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) * g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) * (∫ ω, g (Y ω) ∂μ) :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg

lemma IndepFun.integral_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) • (g ∘ Y)] = μ[f ∘ X] • μ[g ∘ Y] :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg

lemma IndepFun.integral_comp_mul_comp
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) * (g ∘ Y)] = μ[f ∘ X] * μ[g ∘ Y] :=
  hXY.integral_fun_comp_mul_comp hX hY hf hg

lemma IndepFun.integral_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {X : Ω → 𝕜} {Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X • Y] = μ[X] • μ[Y] :=
  hXY.integral_comp_smul_comp hX.aemeasurable hY.aemeasurable
    aestronglyMeasurable_id aestronglyMeasurable_id

lemma IndepFun.integral_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_smul_eq_smul_integral hX hY

lemma IndepFun.integral_fun_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {X : Ω → 𝕜} {Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω • Y ω ∂μ = (∫ ω, X ω ∂μ) • ∫ ω, Y ω ∂μ :=
  hXY.integral_smul_eq_smul_integral hX hY

lemma IndepFun.integral_fun_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = μ[X] * μ[Y] :=
  hXY.integral_fun_smul_eq_smul_integral hX hY

end Integral

/-- Independence of functions `f` and `g` into arbitrary types is characterized by the relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` with values in `ℝ`
  satisfying appropriate integrability conditions. -/
theorem indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} {f : Ω → β} {g : Ω → β'} {hfm : Measurable f} {hgm : Measurable g} :
    f ⟂ᵢ[μ] g ↔ ∀ {φ : β → ℝ} {ψ : β' → ℝ}, Measurable φ → Measurable ψ →
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
  rwa [← toReal_eq_toReal_iff' (measure_ne_top μ _), toReal_mul, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, ← integral_indicator_one ((hfm hA).inter (hgm hB)),
    ← integral_indicator_one (hfm hA), ← integral_indicator_one (hgm hB), Set.inter_indicator_one]
  exact mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

lemma IndepSets.congr_set {S₁ S₂ T₁ T₂ : Set (Set Ω)} (h : IndepSets S₂ T₂ P)
    (hS : ∀ s₁ ∈ S₁, ∃ s₂ ∈ S₂, s₁ =ᵐ[P] s₂) (hT : ∀ t₁ ∈ T₁, ∃ t₂ ∈ T₂, t₁ =ᵐ[P] t₂) :
    IndepSets S₁ T₁ P := by
  rw [IndepSets_iff]
  intro s₁ t₁ hs₁ ht₁
  obtain ⟨s₂, hs₂, hs₂'⟩ := hS s₁ hs₁
  obtain ⟨t₂, ht₂, ht₂'⟩ := hT t₁ ht₁
  rw [measure_congr (hs₂'.inter ht₂'), (IndepSets_iff _ _ _).1 h _ _ hs₂ ht₂, measure_congr hs₂',
    measure_congr ht₂']

lemma IndepSets.congr_comap {S : Set (Set Ω)} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
    {X₁ X₂ : Ω → 𝓧} (h : IndepSets S {s | MeasurableSet[m𝓧.comap X₁] s} P) (hX : X₁ =ᵐ[P] X₂) :
    IndepSets S {s | MeasurableSet[m𝓧.comap X₂] s} P := by
  apply h.congr_set (fun s hs ↦ ⟨s, hs, .rfl⟩)
  rintro - ⟨s, hs, rfl⟩
  exact ⟨X₁ ⁻¹' s, hs.preimage (comap_measurable _), (hX.preimage s).symm⟩

lemma Indep.congr_comap {m : MeasurableSpace Ω} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
    {X₁ X₂ : Ω → 𝓧} (h : Indep m (m𝓧.comap X₁) P) (hX : X₁ =ᵐ[P] X₂) :
    Indep m (m𝓧.comap X₂) P := IndepSets.congr_comap h hX

/-- If the indicator of a set `A` is independent from a variable `X`, then the set `A` is
independent from the sigma algebra generated by `X`. -/
lemma IndepFun.singleton_indepSets_of_indicator' {𝓧 M : Type*} [mX : MeasurableSpace 𝓧] {A : Set Ω}
    [Zero M] [MeasurableSpace M] [MeasurableSingletonClass M] (c : M) [hc : NeZero c]
    {X : Ω → 𝓧} (h : (A.indicator (fun _ ↦ c)) ⟂ᵢ[P] X) :
    IndepSets {A} {s | MeasurableSet[mX.comap X] s} P := by
  rw [IndepSets_iff]
  rintro s - hs ⟨t, ht, rfl⟩
  rw [Set.mem_singleton_iff.1 hs]
  have hA' : A = A.indicator (fun _ ↦ c) ⁻¹' {c} := by ext; simp [Set.indicator, hc.ne']
  rw [hA']
  exact h.measure_inter_preimage_eq_mul _ _ (by simp) ht

lemma singleton_indepSets_comap_iff {Ω M : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsZeroOrProbabilityMeasure P] {𝓧 : Type*}
    [Zero M] [MeasurableSpace M] [MeasurableSingletonClass M] (c : M) [NeZero c]
    {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧} (hX : Measurable X) (hA : MeasurableSet A) :
    IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} P ↔
      (A.indicator (fun _ ↦ c)) ⟂ᵢ[P] X where
  mp h := by
    rw [IndepFun_iff_Indep, ← MeasurableSpace.generateFrom_singleton_eq_comap_indicator_const c]
    exact h.indep (MeasurableSpace.generateFrom_le (by simpa)) hX.comap_le (by simp [IsPiSystem])
      (@MeasurableSpace.isPiSystem_measurableSet _ (m𝓧.comap X)) rfl (by simp)
  mpr h := h.singleton_indepSets_of_indicator' c

lemma Indep.indicator_indepFun {Ω M : Type*} {m mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓧 : Type*} [Zero M] [MeasurableSpace M] [MeasurableSingletonClass M] (c : M)
    [NeZero c] {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧}
    (hA : MeasurableSet[m] A) (h : Indep m (m𝓧.comap X) P) :
    (A.indicator (fun _ ↦ c)) ⟂ᵢ[P] X := by
  rw [IndepFun_iff_Indep, ← MeasurableSpace.generateFrom_singleton_eq_comap_indicator_const c]
  exact indep_of_indep_of_le_left h (MeasurableSpace.generateFrom_le (by simpa))

lemma singleton_indepSets_comap_iff₀ {Ω M : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsZeroOrProbabilityMeasure P] {𝓧 : Type*}
    [Zero M] [MeasurableSpace M] [MeasurableSingletonClass M] (c : M) [NeZero c]
    {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧} (hX : AEMeasurable X P)
    (hA : NullMeasurableSet A P) :
    IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} P ↔
      (A.indicator (fun _ ↦ c)) ⟂ᵢ[P] X where
  mp h := by
    refine IndepFun.congr ?_ (indicator_ae_eq_of_ae_eq_set hA.toMeasurable_ae_eq) hX.ae_eq_mk.symm
    rw [← singleton_indepSets_comap_iff _ hX.measurable_mk (measurableSet_toMeasurable P A)]
    refine (h.congr_set ?_ ?_).congr_comap hX.ae_eq_mk
    · simp [hA.toMeasurable_ae_eq]
    · simpa using fun t ht ↦ ⟨t, ht, .rfl⟩
  mpr h := h.singleton_indepSets_of_indicator' c

lemma Indep.setIntegral_eq_smul {Ω 𝓧 E : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {μ : Measure Ω} [m𝓧 : MeasurableSpace 𝓧] {X : Ω → 𝓧}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : 𝓧 → E} {A : Set Ω} (hA1 : Indep m (m𝓧.comap X) μ)
    (hX : AEMeasurable X μ) (hA2 : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A • ∫ ω, f (X ω) ∂μ :=
  calc ∫ ω in A, f (X ω) ∂μ
    = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) • f (X ω) ∂μ := by
        rw [← integral_indicator (hm A hA2)]
        congr with ω
        by_cases hω : ω ∈ A <;> simp [hω]
  _ = μ.real A • ∫ ω, f (X ω) ∂μ := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_prop) hf]
    · simp [hm A hA2]
    · exact hA1.indicator_indepFun 1 hA2
    · exact (aemeasurable_indicator_const_iff 1).2 (hm A hA2).nullMeasurableSet

lemma IndepSets.setIntegral_eq_smul {Ω 𝓧 E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [m𝓧 : MeasurableSpace 𝓧] {X : Ω → 𝓧} [IsZeroOrProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : 𝓧 → E} {A : Set Ω} (hA1 : IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} μ)
    (hX : AEMeasurable X μ) (hA2 : NullMeasurableSet A μ)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A • ∫ ω, f (X ω) ∂μ :=
  calc ∫ ω in A, f (X ω) ∂μ
    = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) • f (X ω) ∂μ := by
        rw [← integral_indicator₀ hA2]
        congr with ω
        by_cases hω : ω ∈ A <;> simp [hω]
  _ = μ.real A • ∫ ω, f (X ω) ∂μ := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_prop) hf]
    · simp_all
    · exact (singleton_indepSets_comap_iff₀ 1 hX hA2).1 hA1
    · exact (aemeasurable_indicator_const_iff 1).2 hA2

lemma Indep.setIntegral_eq_mul {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {μ : Measure Ω} [m𝓧 : MeasurableSpace 𝓧] {X : Ω → 𝓧}
    {f : 𝓧 → ℝ} {A : Set Ω} (hA1 : Indep m (m𝓧.comap X) μ)
    (hX : AEMeasurable X μ) (hA2 : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A * ∫ ω, f (X ω) ∂μ :=
  hA1.setIntegral_eq_smul hm hX hA2 hf

lemma IndepSets.setIntegral_eq_mul {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [m𝓧 : MeasurableSpace 𝓧] {X : Ω → 𝓧} [IsZeroOrProbabilityMeasure μ]
    {f : 𝓧 → ℝ} {A : Set Ω} (hA1 : IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} μ)
    (hX : AEMeasurable X μ) (hA2 : NullMeasurableSet A μ)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A * ∫ ω, f (X ω) ∂μ :=
  IndepSets.setIntegral_eq_smul hA1 hX hA2 hf

lemma Indep.singleton_indepSets {Ω : Type*} {m1 m2 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (h : Indep m1 m2 P) {A : Set Ω}
    (hA : MeasurableSet[m1] A) : IndepSets {A} {s | MeasurableSet[m2] s} P := by
  have := (Indep_iff_IndepSets m1 m2 P).1 h
  apply indepSets_of_indepSets_of_le_left this
  simpa

end ProbabilityTheory
