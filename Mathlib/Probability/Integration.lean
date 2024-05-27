/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Probability.Independence.Basic

#align_import probability.integration from "leanprover-community/mathlib"@"2f8347015b12b0864dfaf366ec4909eb70c78740"

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

open Set MeasureTheory

open scoped ENNReal MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ≥0∞} {X Y : Ω → ℝ}

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
    rw [lintegral_indicator _ (MeasurableSet.inter (hMf _ h_meas_s') h_meas_T),
      lintegral_indicator _ (hMf _ h_meas_s'), lintegral_indicator _ h_meas_T]
    simp only [measurable_const, lintegral_const, univ_inter, lintegral_const_mul,
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
#align probability_theory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator ProbabilityTheory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
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
#align probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
   then `E[f * g] = E[f] * E[g]`. -/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : IndepFun f g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)
#align probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun

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
  exact h_indep_fun.ae_eq h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk
#align probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'

theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : IndepFun f g μ) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun
#align probability_theory.lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'' ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''

/-- The product of two independent, integrable, real-valued random variables is integrable. -/
theorem IndepFun.integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (hX : Integrable X μ)
    (hY : Integrable Y μ) : Integrable (X * Y) μ := by
  let nX : Ω → ENNReal := fun a => ‖X a‖₊
  let nY : Ω → ENNReal := fun a => ‖Y a‖₊
  have hXY' : IndepFun (fun a => ‖X a‖₊) (fun a => ‖Y a‖₊) μ :=
    hXY.comp measurable_nnnorm measurable_nnnorm
  have hXY'' : IndepFun nX nY μ :=
    hXY'.comp measurable_coe_nnreal_ennreal measurable_coe_nnreal_ennreal
  have hnX : AEMeasurable nX μ := hX.1.aemeasurable.nnnorm.coe_nnreal_ennreal
  have hnY : AEMeasurable nY μ := hY.1.aemeasurable.nnnorm.coe_nnreal_ennreal
  have hmul : ∫⁻ a, nX a * nY a ∂μ = (∫⁻ a, nX a ∂μ) * ∫⁻ a, nY a ∂μ :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' hnX hnY hXY''
  refine ⟨hX.1.mul hY.1, ?_⟩
  simp_rw [HasFiniteIntegral, Pi.mul_apply, nnnorm_mul, ENNReal.coe_mul, hmul]
  exact ENNReal.mul_lt_top hX.2.ne hY.2.ne
#align probability_theory.indep_fun.integrable_mul ProbabilityTheory.IndepFun.integrable_mul

/-- If the product of two independent real-valued random variables is integrable and
the second one is not almost everywhere zero, then the first one is integrable. -/
theorem IndepFun.integrable_left_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖₊ ∂μ) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖Y ω‖₊ : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.ennnorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
  refine lt_top_iff_ne_top.2 fun H => ?_
  have J : IndepFun (fun ω => ‖X ω‖₊ : Ω → ℝ≥0∞) (fun ω => ‖Y ω‖₊ : Ω → ℝ≥0∞) μ := by
    have M : Measurable fun x : β => (‖x‖₊ : ℝ≥0∞) := measurable_nnnorm.coe_nnreal_ennreal
    apply IndepFun.comp hXY M M
  have A : (∫⁻ ω, ‖X ω * Y ω‖₊ ∂μ) < ∞ := h'XY.2
  simp only [nnnorm_mul, ENNReal.coe_mul] at A
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.ennnorm hY.ennnorm J, H] at A
  simp only [ENNReal.top_mul I, lt_self_iff_false] at A
#align probability_theory.indep_fun.integrable_left_of_integrable_mul ProbabilityTheory.IndepFun.integrable_left_of_integrable_mul

/-- If the product of two independent real-valued random variables is integrable and the
first one is not almost everywhere zero, then the second one is integrable. -/
theorem IndepFun.integrable_right_of_integrable_mul {β : Type*} [MeasurableSpace β] {X Y : Ω → β}
    [NormedDivisionRing β] [BorelSpace β] (hXY : IndepFun X Y μ) (h'XY : Integrable (X * Y) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  refine ⟨hY, ?_⟩
  have I : (∫⁻ ω, ‖X ω‖₊ ∂μ) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖X ω‖₊ : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hX.ennnorm).1 H
    apply h'X
    filter_upwards [I] with ω hω
    simpa using hω
  refine lt_top_iff_ne_top.2 fun H => ?_
  have J : IndepFun (fun ω => ‖X ω‖₊ : Ω → ℝ≥0∞) (fun ω => ‖Y ω‖₊ : Ω → ℝ≥0∞) μ := by
    have M : Measurable fun x : β => (‖x‖₊ : ℝ≥0∞) := measurable_nnnorm.coe_nnreal_ennreal
    apply IndepFun.comp hXY M M
  have A : (∫⁻ ω, ‖X ω * Y ω‖₊ ∂μ) < ∞ := h'XY.2
  simp only [nnnorm_mul, ENNReal.coe_mul] at A
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.ennnorm hY.ennnorm J, H] at A
  simp only [ENNReal.mul_top I, lt_self_iff_false] at A
#align probability_theory.indep_fun.integrable_right_of_integrable_mul ProbabilityTheory.IndepFun.integrable_right_of_integrable_mul

/-- The (Bochner) integral of the product of two independent, nonnegative random
  variables is the product of their integrals. The proof is just plumbing around
  `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'`. -/
theorem IndepFun.integral_mul_of_nonneg (hXY : IndepFun X Y μ) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ) :
    integral μ (X * Y) = integral μ X * integral μ Y := by
  have h1 : AEMeasurable (fun a => ENNReal.ofReal (X a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hXm
  have h2 : AEMeasurable (fun a => ENNReal.ofReal (Y a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hYm
  have h3 : AEMeasurable (X * Y) μ := hXm.mul hYm
  have h4 : 0 ≤ᵐ[μ] X * Y := ae_of_all _ fun ω => mul_nonneg (hXp ω) (hYp ω)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hXp) hXm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hYp) hYm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae h4 h3.aestronglyMeasurable]
  simp_rw [← ENNReal.toReal_mul, Pi.mul_apply, ENNReal.ofReal_mul (hXp _)]
  congr
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h1 h2
  exact hXY.comp ENNReal.measurable_ofReal ENNReal.measurable_ofReal
#align probability_theory.indep_fun.integral_mul_of_nonneg ProbabilityTheory.IndepFun.integral_mul_of_nonneg

/-- The (Bochner) integral of the product of two independent, integrable random
  variables is the product of their integrals. The proof is pedestrian decomposition
  into their positive and negative parts in order to apply `IndepFun.integral_mul_of_nonneg`
  four times. -/
theorem IndepFun.integral_mul_of_integrable (hXY : IndepFun X Y μ) (hX : Integrable X μ)
    (hY : Integrable Y μ) : integral μ (X * Y) = integral μ X * integral μ Y := by
  let pos : ℝ → ℝ := fun x => max x 0
  let neg : ℝ → ℝ := fun x => max (-x) 0
  have posm : Measurable pos := measurable_id'.max measurable_const
  have negm : Measurable neg := measurable_id'.neg.max measurable_const
  let Xp := pos ∘ X
  -- `X⁺` would look better but it makes `simp_rw` below fail
  let Xm := neg ∘ X
  let Yp := pos ∘ Y
  let Ym := neg ∘ Y
  have hXpm : X = Xp - Xm := funext fun ω => (max_zero_sub_max_neg_zero_eq_self (X ω)).symm
  have hYpm : Y = Yp - Ym := funext fun ω => (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm
  have hp1 : 0 ≤ Xm := fun ω => le_max_right _ _
  have hp2 : 0 ≤ Xp := fun ω => le_max_right _ _
  have hp3 : 0 ≤ Ym := fun ω => le_max_right _ _
  have hp4 : 0 ≤ Yp := fun ω => le_max_right _ _
  have hm1 : AEMeasurable Xm μ := hX.1.aemeasurable.neg.max aemeasurable_const
  have hm2 : AEMeasurable Xp μ := hX.1.aemeasurable.max aemeasurable_const
  have hm3 : AEMeasurable Ym μ := hY.1.aemeasurable.neg.max aemeasurable_const
  have hm4 : AEMeasurable Yp μ := hY.1.aemeasurable.max aemeasurable_const
  have hv1 : Integrable Xm μ := hX.neg_part
  have hv2 : Integrable Xp μ := hX.pos_part
  have hv3 : Integrable Ym μ := hY.neg_part
  have hv4 : Integrable Yp μ := hY.pos_part
  have hi1 : IndepFun Xm Ym μ := hXY.comp negm negm
  have hi2 : IndepFun Xp Ym μ := hXY.comp posm negm
  have hi3 : IndepFun Xm Yp μ := hXY.comp negm posm
  have hi4 : IndepFun Xp Yp μ := hXY.comp posm posm
  have hl1 : Integrable (Xm * Ym) μ := hi1.integrable_mul hv1 hv3
  have hl2 : Integrable (Xp * Ym) μ := hi2.integrable_mul hv2 hv3
  have hl3 : Integrable (Xm * Yp) μ := hi3.integrable_mul hv1 hv4
  have hl4 : Integrable (Xp * Yp) μ := hi4.integrable_mul hv2 hv4
  have hl5 : Integrable (Xp * Yp - Xm * Yp) μ := hl4.sub hl3
  have hl6 : Integrable (Xp * Ym - Xm * Ym) μ := hl2.sub hl1
  rw [hXpm, hYpm, mul_sub, sub_mul, sub_mul]
  rw [integral_sub' hl5 hl6, integral_sub' hl4 hl3, integral_sub' hl2 hl1, integral_sub' hv2 hv1,
    integral_sub' hv4 hv3, hi1.integral_mul_of_nonneg hp1 hp3 hm1 hm3,
    hi2.integral_mul_of_nonneg hp2 hp3 hm2 hm3, hi3.integral_mul_of_nonneg hp1 hp4 hm1 hm4,
    hi4.integral_mul_of_nonneg hp2 hp4 hm2 hm4]
  ring
#align probability_theory.indep_fun.integral_mul_of_integrable ProbabilityTheory.IndepFun.integral_mul_of_integrable

/-- The (Bochner) integral of the product of two independent random
  variables is the product of their integrals. -/
theorem IndepFun.integral_mul (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : integral μ (X * Y) = integral μ X * integral μ Y := by
  by_cases h'X : X =ᵐ[μ] 0
  · have h' : X * Y =ᵐ[μ] 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp only [integral_congr_ae h'X, integral_congr_ae h', Pi.zero_apply, integral_const,
      Algebra.id.smul_eq_mul, mul_zero, zero_mul]
  by_cases h'Y : Y =ᵐ[μ] 0
  · have h' : X * Y =ᵐ[μ] 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp only [integral_congr_ae h'Y, integral_congr_ae h', Pi.zero_apply, integral_const,
      Algebra.id.smul_eq_mul, mul_zero, zero_mul]
  by_cases h : Integrable (X * Y) μ
  · have HX : Integrable X μ := hXY.integrable_left_of_integrable_mul h hX hY h'Y
    have HY : Integrable Y μ := hXY.integrable_right_of_integrable_mul h hX hY h'X
    exact hXY.integral_mul_of_integrable HX HY
  · rw [integral_undef h]
    have I : ¬(Integrable X μ ∧ Integrable Y μ) := by
      rintro ⟨HX, HY⟩
      exact h (hXY.integrable_mul HX HY)
    rw [not_and_or] at I
    cases' I with I I <;> simp [integral_undef I]
#align probability_theory.indep_fun.integral_mul ProbabilityTheory.IndepFun.integral_mul

theorem IndepFun.integral_mul' (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) :
    (integral μ fun ω => X ω * Y ω) = integral μ X * integral μ Y :=
  hXY.integral_mul hX hY
#align probability_theory.indep_fun.integral_mul' ProbabilityTheory.IndepFun.integral_mul'

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
#align probability_theory.indep_fun_iff_integral_comp_mul ProbabilityTheory.indepFun_iff_integral_comp_mul

end ProbabilityTheory
