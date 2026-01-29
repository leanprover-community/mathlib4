/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.DeGrootInfo
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Total variation distance

## Main definitions

* `tvDist μ ν`: the total variation distance between two measures `μ` and `ν`.

## Main statements

* `fooBar_unique`

-/

@[expose] public section

open MeasureTheory Bool

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma withDensity_mono_measure (h : μ ≤ ν) {f : α → ℝ≥0∞} : μ.withDensity f ≤ ν.withDensity f := by
  refine Measure.le_intro fun s hs _ ↦ ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  gcongr

lemma rnDeriv_add_self_right (ν μ : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x + 1)⁻¹ := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [μ.rnDeriv_add' ν ν, ν.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply, h1, Pi.add_apply, h2, inv_eq_iff_eq_inv] at h3
  rw [h3]

lemma rnDeriv_add_self_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x ↦ 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self_right ν μ] with a h4 h5 h6
    rw [h5, Pi.add_apply] at h4
    nth_rewrite 1 [h4]
    simp [h6]
  filter_upwards [this, μ.rnDeriv_lt_top ν] with a ha ha_lt_top
  rw [ha, div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rwa [ENNReal.mul_inv_cancel] at h
  · simp
  · simp [ha_lt_top.ne]

lemma rnDeriv_eq_div (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  filter_upwards [rnDeriv_add_self_right ν μ, rnDeriv_add_self_left μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1, ha2, ENNReal.div_eq_inv_mul, inv_inv, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel, one_mul]
  · simp
  · simp [ha_lt_top.ne]

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧}

lemma mutuallySingular_iff_rnDeriv_eq_zero [SigmaFinite μ] [SigmaFinite ν] :
    μ ⟂ₘ ν ↔ ∀ᵐ x ∂(μ + ν), μ.rnDeriv (μ + ν) x = 0 ∨ ν.rnDeriv (μ + ν) x = 0 := by
  have hμ_ac : μ ≪ μ + ν := (Measure.AbsolutelyContinuous.refl _).add_right _
  have hν_ac : ν ≪ μ + ν := by
    rw [add_comm]
    exact (Measure.AbsolutelyContinuous.refl _).add_right _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [ae_add_measure_iff]
    suffices h1 : ∀ (μ : Measure 𝓧) (ν) [SigmaFinite μ] [SigmaFinite ν] (h : μ ⟂ₘ ν),
        ∀ᵐ x ∂ν, (∂μ/∂(μ + ν)) x = 0 ∨ (∂ν/∂(μ + ν)) x = 0 by
      refine ⟨?_, h1 μ ν h⟩
      rw [add_comm μ]
      convert h1 ν μ h.symm using 2
      rw [_root_.or_comm]
    intro μ ν _ _ h
    rw [← Measure.rnDeriv_eq_zero] at h
    have hν_ac : ν ≪ μ + ν := by
      rw [add_comm]
      exact (Measure.AbsolutelyContinuous.refl _).add_right _
    filter_upwards [μ.rnDeriv_eq_div ν, h, Measure.rnDeriv_pos hν_ac,
      hν_ac (Measure.rnDeriv_ne_top ν (μ+ ν))] with x hx_div hx_zero hx_pos hx_ne_top
    rw [hx_div] at hx_zero
    simp only [Pi.zero_apply, ENNReal.div_eq_zero_iff, hx_ne_top, _root_.or_false] at hx_zero
    simp [hx_zero]
  · rw [← Measure.rnDeriv_eq_zero]
    filter_upwards [μ.rnDeriv_eq_div ν, Measure.rnDeriv_pos hν_ac, hν_ac h]
      with x hx_div hx_pos hx_min
    rw [hx_div]
    simp only [Pi.zero_apply, ENNReal.div_eq_zero_iff]
    left
    simpa [hx_pos.ne'] using hx_min

lemma mutuallySingular_dirac_of_ne [MeasurableSingletonClass 𝓧] {x y : 𝓧} (h : x ≠ y) :
    Measure.dirac x ⟂ₘ Measure.dirac y := ⟨{y}, measurableSet_singleton y, by simp [h]⟩

/-- Total variation distance between two measures. -/
noncomputable def tvDist (μ ν : Measure 𝓧) : ℝ := (deGrootInfo μ ν (boolMeasure 1 1)).toReal

instance : IsFiniteMeasure (boolMeasure 1 1) := by constructor; simp

@[simp] lemma tvDist_zero_left : tvDist (0 : Measure 𝓧) ν = 0 := by simp [tvDist]

@[simp] lemma tvDist_zero_right : tvDist μ (0 : Measure 𝓧) = 0 := by simp [tvDist]

@[simp] lemma tvDist_self : tvDist μ μ = 0 := by simp [tvDist]

lemma tvDist_nonneg : 0 ≤ tvDist μ ν := ENNReal.toReal_nonneg

lemma tvDist_comm : tvDist μ ν = tvDist ν μ := by
  rw [tvDist, tvDist, deGrootInfo_comm]
  simp

lemma tvDist_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν ≤ min (μ.real .univ) (ν.real .univ) := by
  rw [Measure.real, Measure.real, ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _)]
  refine ENNReal.toReal_mono ?_ ?_
  · simp
  · have h := deGrootInfo_le_min (μ := μ) (ν := ν) (π := boolMeasure 1 1)
    simpa only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] using h

lemma tvDist_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := tvDist_le.trans_eq (by simp)

/-- **Data processing inequality** for the total variation distance. -/
lemma tvDist_comp_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν :=
  ENNReal.toReal_mono deGrootInfo_ne_top (deGrootInfo_comp_le _ _ _ _)

/-- **Data processing inequality** for the total variation distance. -/
lemma tvDist_map_le (μ ν : Measure 𝓧) [IsFiniteMeasure μ] {f : 𝓧 → 𝓨} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν :=
  ENNReal.toReal_mono deGrootInfo_ne_top (deGrootInfo_map_le _ _ _ hf)

lemma tvDist_eq_min_sub_lintegral {ζ : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = min (μ.real .univ) (ν.real .univ)
      - (∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ).toReal := by
  have h := deGrootInfo_eq_min_sub_lintegral' (boolMeasure 1 1) hμζ hνζ
  simp only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] at h
  rw [tvDist, h, Measure.real, Measure.real,
    ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le _ (by simp)]
  calc ∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ
  _ ≤ min (∫⁻ x, (∂μ/∂ζ) x ∂ζ) (∫⁻ x, (∂ν/∂ζ) x ∂ζ) := by
    refine le_min ?_ ?_
    · exact lintegral_mono fun _ ↦ min_le_left _ _
    · exact lintegral_mono fun _ ↦ min_le_right _ _
  _ = min (μ .univ) (ν .univ) := by
    rw [Measure.lintegral_rnDeriv hμζ, Measure.lintegral_rnDeriv hνζ]

lemma tvDist_eq_one_sub_lintegral {ζ : Measure 𝓧} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    tvDist μ ν = 1 - (∫⁻ x, min ((∂μ/∂ζ) x) ((∂ν/∂ζ) x) ∂ζ).toReal := by
  simp [tvDist_eq_min_sub_lintegral hμζ hνζ]

lemma tvDist_eq_min_sub_integral' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = min (μ.real .univ) (ν.real .univ)
      - ∫ x, min ((∂μ/∂(μ + ν)) x).toReal ((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν) := by
  rw [tvDist, toReal_deGrootInfo_eq_min_sub_integral, add_comm μ]
  simp [Measure.real, boolKernel_comp_measure]

lemma tvDist_eq_one_sub_integral' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 1 - ∫ x, min ((∂μ/∂(μ + ν)) x).toReal ((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν) := by
  simp [tvDist_eq_min_sub_integral']

lemma tvDist_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν = min (μ.real .univ) (ν.real .univ)
      - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  have h := deGrootInfo_eq_min_sub_iInf_measurableSet μ ν (boolMeasure 1 1)
  simp only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] at h
  rw [tvDist, h, Measure.real, Measure.real,
    ← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le _ (by simp)]
  · congr
    rw [iInf_subtype']
    rw [← ENNReal.toReal_ofReal (r := ⨅ (E : {E //  MeasurableSet E}), μ.real E + ν.real E.1ᶜ)]
    swap; · exact le_ciInf fun E ↦ by positivity
    simp_rw [ENNReal.ofReal_iInf]
    congr with E
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  · simp only [le_inf_iff]
    constructor
    · exact (iInf_le _ .univ).trans (by simp)
    · exact (iInf_le _ ∅).trans (by simp)

lemma tvDist_eq_one_sub_iInf_measurableSet (μ ν : Measure 𝓧) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν = 1 - ⨅ (E : {E // MeasurableSet E}), μ.real E + ν.real E.1ᶜ := by
  simp [tvDist_eq_min_sub_iInf_measurableSet]

lemma tvDist_eq_iSup_measurableSet_of_measure_univ_le [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ν .univ ≤ μ .univ) :
    tvDist μ ν = (⨆ E, ⨆ (_ : MeasurableSet E), ν E - μ E).toReal := by
  rw [tvDist, deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le]
  · simp
  · simpa

lemma tvDist_eq_iSup_measurableSet_of_measure_univ_le' [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ .univ ≤ ν .univ) :
    tvDist μ ν = (⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E).toReal := by
  rw [tvDist, deGrootInfo_eq_iSup_measurableSet_of_measure_univ_le']
  · simp
  · simpa

lemma tvDist_eq_iSup_measurableSet [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = (⨆ E, ⨆ (_ : MeasurableSet E), ν E - μ E).toReal :=
  tvDist_eq_iSup_measurableSet_of_measure_univ_le (by simp)

lemma tvDist_eq_iSup_measurableSet' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = (⨆ E, ⨆ (_ : MeasurableSet E), μ E - ν E).toReal :=
  tvDist_eq_iSup_measurableSet_of_measure_univ_le' (by simp)

lemma tvDist_eq_zero_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≤ μ) :
    tvDist μ ν = 0 := by
  rw [tvDist, ENNReal.toReal_eq_zero_iff]
  exact Or.inl <| deGrootInfo_eq_zero_of_le (by simpa)

/-- The total variation between two probability measures is zero iff the measures are equal. -/
@[simp]
lemma tvDist_eq_zero_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 0 ↔ μ = ν := by
  rw [tvDist, ENNReal.toReal_eq_zero_iff]
  simp [deGrootInfo_ne_top, deGrootInfo_eq_zero_iff]

/-- The total variation between two probability measures is one iff the measures are mutually
singular. -/
lemma tvDist_eq_one_iff_mutuallySingular [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 1 ↔ μ ⟂ₘ ν := by
  rw [mutuallySingular_iff_rnDeriv_eq_zero]
  have hμ_ac : μ ≪ μ + ν := (Measure.AbsolutelyContinuous.refl _).add_right _
  have hν_ac : ν ≪ μ + ν := by
    rw [add_comm]
    exact (Measure.AbsolutelyContinuous.refl _).add_right _
  rw [tvDist_eq_one_sub_lintegral (ζ := μ + ν) hμ_ac hν_ac, sub_eq_self,
      ENNReal.toReal_eq_zero_iff]
  have : ∫⁻ x, min ((∂μ/∂(μ + ν)) x) ((∂ν/∂(μ + ν)) x) ∂(μ + ν) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := 1) (by simp) ?_
    calc ∫⁻ x, min ((∂μ/∂(μ + ν)) x) ((∂ν/∂(μ + ν)) x) ∂(μ + ν)
    _ ≤ ∫⁻ x, (∂μ/∂(μ + ν)) x ∂(μ + ν) := by
      gcongr with x
      exact min_le_left _ _
    _ ≤ μ Set.univ := Measure.lintegral_rnDeriv_le
    _ = 1 := by simp
  simp only [this, _root_.or_false]
  rw [lintegral_eq_zero_iff (by fun_prop)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    <;> filter_upwards [h]
    <;> simp_rw [Pi.zero_apply, ← bot_eq_zero, min_eq_bot, bot_eq_zero]
    <;> exact fun x hx ↦ hx

/-- The total variation between two Dirac distributions at different points is one. -/
lemma tvDist_dirac_of_ne [MeasurableSingletonClass 𝓧] {x y : 𝓧} (h : x ≠ y) :
    tvDist (Measure.dirac x) (Measure.dirac y) = 1 := by
  rw [tvDist_eq_one_iff_mutuallySingular]
  exact mutuallySingular_dirac_of_ne h

lemma tvDist_eq_half_integral_abs_sub [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 2⁻¹ * ∫ x, |((∂μ/∂(μ + ν)) x).toReal - ((∂ν/∂(μ + ν)) x).toReal| ∂(μ + ν) := by
  rw [tvDist, toReal_deGrootInfo_eq_integral_abs_boolKernel, add_comm μ ν]
  simp [boolKernel_comp_measure, Measure.real]

-- the l.h.s. is the Hellinger distance squared
lemma hellinger_le_tvDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    1 - ∫ x, √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν) ≤ tvDist μ ν := by
  have h_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
    calc (a - b) ^ 2
    _ = |a - b| * |a - b| := by rw [← pow_two, sq_abs]
    _ ≤ |a - b| * (a + b) := by
      gcongr
      wlog hab : a ≤ b
      · rw [abs_sub_comm, add_comm]
        exact this (μ := μ) (ν := ν) hb ha (by linarith)
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith
    _ = |a ^ 2 - b ^ 2| := by
      rw [sq_sub_sq, abs_mul, mul_comm, abs_of_nonneg (a := a + b) (by positivity)]
  have h_le_rnDeriv x : (√((∂μ/∂(μ + ν)) x).toReal - √((∂ν/∂(μ + ν)) x).toReal) ^ 2
      ≤ |((∂μ/∂(μ + ν)) x).toReal - ((∂ν/∂(μ + ν)) x).toReal| := by
    refine (h_le (by positivity) (by positivity)).trans_eq ?_
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc 1 - ∫ x, √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν)
  _ = 2⁻¹ * (1 + 1 - ∫ x, 2 * √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν)) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  _ = 2⁻¹ * (∫ x, ((∂μ/∂(μ + ν)) x).toReal ∂(μ + ν) + ∫ x, ((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν)
        - ∫ x, 2 * √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν)) := by
    congr
    · rw [Measure.integral_toReal_rnDeriv]
      · simp
      · exact (Measure.AbsolutelyContinuous.refl _).add_right _
    · rw [Measure.integral_toReal_rnDeriv]
      · simp
      · rw [add_comm]
        exact (Measure.AbsolutelyContinuous.refl _).add_right _
  _ = 2⁻¹ * ∫ x, (√((∂μ/∂(μ + ν)) x).toReal - √((∂ν/∂(μ + ν)) x).toReal) ^ 2 ∂(μ + ν) := by
    rw [← integral_add (by fun_prop) (by fun_prop), ← integral_sub (by fun_prop)]
    swap
    · refine integrable_of_le_of_le (g₁ := fun _ ↦ 0)
        (g₂ := fun x ↦ ((∂μ/∂(μ + ν)) x).toReal + ((∂ν/∂(μ + ν)) x).toReal) (by fun_prop) ?_ ?_
        (by fun_prop) (by fun_prop)
      · exact ae_of_all _ fun _ ↦ by positivity
      · refine ae_of_all _ fun x ↦ ?_
        simp only
        refine (two_mul_le_add_sq _ _).trans_eq ?_
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    congr with x
    rw [sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  _ ≤ 2⁻¹ * ∫ x, |((∂μ/∂(μ + ν)) x).toReal - ((∂ν/∂(μ + ν)) x).toReal| ∂(μ + ν) := by
    gcongr
    · refine integrable_of_le_of_le (g₁ := fun _ ↦ 0)
        (g₂ := fun x ↦ |((∂μ/∂(μ + ν)) x).toReal - ((∂ν/∂(μ + ν)) x).toReal|) (by fun_prop) ?_ ?_
        (by fun_prop) (by fun_prop)
      · exact ae_of_all _ fun _ ↦ by positivity
      · exact ae_of_all _ h_le_rnDeriv
    · fun_prop
    intro x
    exact h_le_rnDeriv x
  _ = tvDist μ ν := tvDist_eq_half_integral_abs_sub.symm

lemma hellinger_le_tvDist' {ζ : Measure 𝓧} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SigmaFinite ζ] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    1 - ∫ x, √((∂μ/∂ζ) x).toReal * √((∂ν/∂ζ) x).toReal ∂ζ ≤ tvDist μ ν := by
  refine le_trans (le_of_eq ?_) hellinger_le_tvDist
  -- extract lemma
  simp only [sub_right_inj]
  symm
  calc ∫ x, √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂(μ + ν)
  _ = ∫ x, ((∂(μ + ν)/∂ζ) x).toReal
      * √((∂μ/∂(μ + ν)) x).toReal * √((∂ν/∂(μ + ν)) x).toReal ∂ζ := by
    rw [← integral_rnDeriv_smul (μ := μ + ν) (ν := ζ)]
    · simp only [smul_eq_mul]
      simp_rw [mul_assoc]
    · exact Measure.AbsolutelyContinuous.add_left hμζ hνζ
  _ = ∫ x, √((∂μ/∂(μ + ν)) x * (∂(μ + ν)/∂ζ) x).toReal
      * √((∂ν/∂(μ + ν)) x * (∂(μ + ν)/∂ζ) x).toReal ∂ζ := by
    congr with x
    simp only [ENNReal.toReal_mul, ENNReal.toReal_nonneg, Real.sqrt_mul]
    conv_lhs => rw [← Real.sq_sqrt (x := ((∂(μ + ν)/∂ζ) x).toReal) (by positivity)]
    ring
  _ = ∫ x, √((∂μ/∂ζ) x).toReal * √((∂ν/∂ζ) x).toReal ∂ζ := by
    refine integral_congr_ae ?_
    have h1 := Measure.rnDeriv_mul_rnDeriv (μ := μ) (ν := μ + ν) (κ := ζ) ?_
    swap; · exact (Measure.AbsolutelyContinuous.refl _).add_right _
    have h2 := Measure.rnDeriv_mul_rnDeriv (μ := ν) (ν := μ + ν) (κ := ζ) ?_
    swap
    · rw [add_comm]
      exact (Measure.AbsolutelyContinuous.refl _).add_right _
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Pi.mul_apply] at hx1 hx2
    rw [hx1, hx2]

open Real

-- todo: extract lemma about the hellinger dist
lemma one_sub_exp_le_tvDist_gaussianReal (μ₁ μ₂ : ℝ) :
    1 - exp (-((μ₁ - μ₂) ^ 2) / 8) ≤ tvDist (gaussianReal μ₁ 1) (gaussianReal μ₂ 1) := by
  refine le_trans (le_of_eq ?_) (hellinger_le_tvDist' (ζ := ℙ) ?_ ?_)
  rotate_left
  · exact gaussianReal_absolutelyContinuous _ (by simp)
  · exact gaussianReal_absolutelyContinuous _ (by simp)
  simp only [sub_right_inj]
  symm
  calc ∫ x, √((∂gaussianReal μ₁ 1/∂ℙ) x).toReal * √((∂gaussianReal μ₂ 1/∂ℙ) x).toReal
  _ = ∫ x, √(gaussianPDFReal μ₁ 1 x) * √(gaussianPDFReal μ₂ 1 x) := by
    refine integral_congr_ae ?_
    filter_upwards [rnDeriv_gaussianReal μ₁ 1, rnDeriv_gaussianReal μ₂ 1] with x h1 h2
    rw [h1, h2, toReal_gaussianPDF, toReal_gaussianPDF]
  _ = ∫ x, √((√(2 * π))⁻¹ * exp (- (x - μ₁) ^ 2 / 2))
      * √((√(2 * π))⁻¹ * exp (- (x - μ₂) ^ 2 / 2)) := by simp [gaussianPDFReal]
  _ = ∫ x, (√(2 * π))⁻¹ * √(exp (- (x - μ₁) ^ 2 / 2)) * √(exp (- (x - μ₂) ^ 2 / 2)) := by
    congr with x
    conv_rhs => rw [← Real.sq_sqrt (x := √(2 * π)) (by positivity), ← inv_pow, ← sqrt_inv]
    simp
    ring
  _ = ∫ x, (√(2 * π))⁻¹ * exp (- (x - μ₁) ^ 2 / 4 - (x - μ₂) ^ 2 / 4) := by
    congr with x
    rw [mul_assoc]
    congr
    simp_rw [sqrt_eq_rpow, ← exp_mul, ← exp_add]
    ring_nf
  _ = ∫ x, (√(2 * π))⁻¹ * exp (- (x - (μ₁ + μ₂) / 2) ^ 2 / 2 - (μ₁ - μ₂) ^ 2 / 8) := by
    congr with x
    congr 2
    ring
  _ = exp (- (μ₁ - μ₂) ^ 2 / 8) * ∫ x, gaussianPDFReal ((μ₁ + μ₂) / 2) 1 x := by
    simp_rw [sub_eq_add_neg, exp_add, ← sub_eq_add_neg, ← mul_assoc]
    rw [integral_mul_const, mul_comm (exp _), neg_div]
    congr with x
    simp [gaussianPDFReal]
  _ = exp (-(μ₁ - μ₂) ^ 2 / 8) := by
    rw [integral_gaussianPDFReal_eq_one _ (by simp), mul_one]

end ProbabilityTheory
