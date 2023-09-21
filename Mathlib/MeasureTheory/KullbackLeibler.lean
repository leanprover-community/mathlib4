/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Analysis.Convex.Integral

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

lemma withDensity_mono {μ : Measure α} {f g : α → ℝ≥0∞} (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    μ.withDensity f ≤ μ.withDensity g := by
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  refine set_lintegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ ↦ h_le

lemma withDensity_inv_same_le (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).withDensity f⁻¹ ≤ μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) ≤ μ
  rw [← withDensity_mul _ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) ≤ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  refine ae_of_all _ (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.one_apply]
  by_cases hx_top : f x = ∞
  · simp only [hx_top, ENNReal.inv_top, mul_zero, zero_le]
  by_cases hx_zero : f x = 0
  · simp only [hx_zero, ENNReal.inv_zero, zero_mul, zero_le]
  rw [ENNReal.mul_inv_cancel hx_zero hx_top]

lemma withDensity_inv_same (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity f⁻¹ = μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ
  rw [← withDensity_mul _ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this, withDensity_one]
  filter_upwards [hf_pos, hf_ne_top] with x hf_pos hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_pos.ne' hf_ne_top, Pi.one_apply]

lemma Measure.rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

lemma Measure.rnDeriv_pos {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    ∀ᵐ x ∂ν, 0 < μ.rnDeriv ν x := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun x hx ↦ hx
  have hs_meas : MeasurableSet s := Measure.measurable_rnDeriv _ _ (measurableSet_singleton 0)
  suffices ν s = 0 by
    rw [ae_iff]
    simpa only [not_lt, nonpos_iff_eq_zero] using this
  have hμs : μ s = 0 := by
    rw [← Measure.withDensity_rnDeriv_eq _ _  hμν, withDensity_apply _ hs_meas,
      set_lintegral_congr_fun hs_meas (ae_of_all _ hs), lintegral_zero]
  exact hνμ hμs

lemma inv_rnDeriv {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  rw [Measure.withDensity_rnDeriv_eq _ _ hνμ]
  have : μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq _ _  hμν).symm
  rw [this]
  conv in (Measure.rnDeriv (Measure.withDensity ν (Measure.rnDeriv μ ν)) ν)⁻¹ => rw [← this]
  rw [withDensity_inv_same]
  · exact Measure.measurable_rnDeriv _ _
  · exact Measure.rnDeriv_pos hμν hνμ
  · exact Measure.rnDeriv_ne_top _ _

lemma Measure.mutuallySingular_self {μ : Measure α} (h : μ ⟂ₘ μ) : μ = 0 := by
  obtain ⟨s, hs, hμs, hμs_compl⟩ := h
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s, measure_union disjoint_compl_right hs.compl, hμs, hμs_compl,
    add_zero]

lemma withDensity_rnDeriv_eq_zero {μ ν : Measure α} [Measure.HaveLebesgueDecomposition ν μ] :
    μ.withDensity (ν.rnDeriv μ) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := Measure.haveLebesgueDecomposition_add ν μ
  constructor
  · intro h
    rw [h, add_zero] at h_dec
    rw [h_dec]
    exact (Measure.mutuallySingular_singularPart ν μ).symm
  · intro h
    rw [h_dec] at h
    rw [Measure.MutuallySingular.add_right_iff] at h
    refine Measure.mutuallySingular_self ?_
    refine Measure.MutuallySingular.mono_ac h.2 ?_ Measure.AbsolutelyContinuous.rfl
    exact withDensity_absolutelyContinuous _ _

section x_log_x

namespace Real

lemma continuous_id_mul_log : Continuous (fun x ↦ x * Real.log x) := by
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * Real.log x) := by
  sorry

lemma measurable_id_mul_log : Measurable (fun x ↦ x * Real.log x) :=
  measurable_id'.mul Real.measurable_log

end Real

end x_log_x

section definition

-- TODO: this should be in EReal?
-- TODO: should also take value ∞ when the log is not integrable
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)] : ℝ≥0∞ :=
  if μ ≪ ν then ENNReal.ofReal (∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ) else ∞

-- todo: extract useful lemmas then delete this
lemma integral_log_rnDeriv_nonneg_aux' {μ ν : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (hμ : μ ≠ 0) :
    - Real.log (ν Set.univ).toReal ≤ ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
  have hν : ν ≠ 0 := by
    refine fun hν_zero ↦ hμ ?_
    ext1 s hs
    refine hμν ?_
    simp only [hν_zero, Measure.zero_toOuterMeasure, OuterMeasure.coe_zero, Pi.zero_apply]
  calc - Real.log (ν Set.univ).toReal
    ≤ - Real.log (μ.withDensity (ν.rnDeriv μ) Set.univ).toReal := by
        have h_zero : μ.withDensity (ν.rnDeriv μ) ≠ 0 := by
          rw [Ne.def, withDensity_rnDeriv_eq_zero]
          refine fun h_sing ↦ hμ ?_
          suffices μ ⟂ₘ μ by exact Measure.mutuallySingular_self this
          exact h_sing.mono_ac Measure.AbsolutelyContinuous.rfl hμν
        gcongr
        · rw [ENNReal.toReal_pos_iff]
          constructor
          · rwa [Measure.measure_univ_pos]
          · exact measure_lt_top _ _
        · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
          exact Measure.withDensity_rnDeriv_le _ _ _ MeasurableSet.univ
  _ = - Real.log (∫⁻ x, ν.rnDeriv μ x ∂μ).toReal := by
        congr
        conv_lhs => rw [withDensity_apply _ MeasurableSet.univ]
        simp only [Measure.restrict_univ]
  _ = - Real.log (∫ x, (ν.rnDeriv μ x).toReal ∂μ) := by
        rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]
        exact Measure.rnDeriv_lt_top _ _
  _ ≤ - ∫ x, Real.log (ν.rnDeriv μ x).toReal ∂μ := by
    gcongr
    -- todo: false if μ is not a probability measure
    sorry
  _ = ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [inv_rnDeriv hμν hνμ] with x hx
    rw [← hx]
    simp only [Pi.inv_apply]
    rw [← Real.log_inv, ENNReal.toReal_inv, inv_inv]

lemma integrable_toReal_rnDeriv {μ ν : Measure α} [IsFiniteMeasure μ] [SigmaFinite ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma integral_log_rnDeriv_nonneg_aux {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    (μ Set.univ).toReal * Real.log (μ Set.univ).toReal
      ≤ ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
  have h_eq_int : (μ Set.univ).toReal = ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
    rw [integral_toReal]
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact Measure.rnDeriv_lt_top _ _
  let φ : ℝ → ℝ := fun x ↦ x * Real.log x
  calc (μ Set.univ).toReal * Real.log (μ Set.univ).toReal
    = φ (μ Set.univ).toReal := rfl
  _ = φ (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [h_eq_int]
  _ ≤ ∫ x, φ (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    refine ConvexOn.map_average_le Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
      isClosed_Ici ?_ ?_ ?_
    · simp
    · exact integrable_toReal_rnDeriv
    · sorry
  _ = ∫ x, (μ.rnDeriv ν x).toReal * Real.log (μ.rnDeriv ν x).toReal ∂ν := rfl
  _ = ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
    conv_rhs =>
      rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
      conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
        rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
    have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      rw [ENNReal.coe_toNNReal]
      exact hx.ne
    have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
        = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
    conv_rhs => rw [h_ν_eq]
    rw [integral_withDensity_eq_integral_smul]
    swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
    congr

end definition

end MeasureTheory
