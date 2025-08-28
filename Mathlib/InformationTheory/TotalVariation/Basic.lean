/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Decision.DeGrootInfo

/-!
# Total variation distance

## Main definitions

* `tvDist μ ν`: the total variation distance between two measures `μ` and `ν`.

## Main statements

* `fooBar_unique`

-/

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

@[simp]
lemma tvDist_eq_zero_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 0 ↔ μ = ν := by
  rw [tvDist, ENNReal.toReal_eq_zero_iff]
  simp [deGrootInfo_ne_top, deGrootInfo_eq_zero_iff]

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

end ProbabilityTheory
