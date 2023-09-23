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

open Real

open scoped ENNReal NNReal

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

lemma Measure.rnDeriv_pos {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _  hμν,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _  hμν]
  exact ae_of_all _ (fun x hx ↦ lt_of_le_of_ne (zero_le _) hx.symm)

lemma Measure.rnDeriv_pos' {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
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
  · exact Measure.rnDeriv_pos' hμν hνμ
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

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  sorry

lemma id_mul_log_ge {x : ℝ} (hx : 0 ≤ x) : log (exp 1) / (exp 1) ≤ x * log x := by
  sorry

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

end x_log_x

section tilted

noncomputable
def Λ (μ : Measure α) (f : α → ℝ) : ℝ := log (∫ x, exp (f x) ∂μ)

@[simp]
lemma Λ_zero_right (μ : Measure α) [IsProbabilityMeasure μ] : Λ μ 0 = 0 := by simp [Λ]

noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x - Λ μ f)))

lemma tilted_absolutelyContinuous {μ : Measure α} {f : α → ℝ} : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

@[simp]
lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by
  simp only [Measure.tilted, Λ, Pi.zero_apply, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, log_one, sub_self, ENNReal.ofReal_one]
  exact withDensity_one

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity
      (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞) (⟨exp (f x - Λ μ f), (exp_pos _).le⟩ : ℝ≥0)) := by
  rw [Measure.tilted]
  congr
  ext1 x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a - Λ μ f)) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]

lemma tilted_apply_eq_ofreal_integral (μ : Measure α)
    {f : α → ℝ} (hf : Integrable (fun x ↦ exp (f x)) μ)
    {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a - Λ μ f) ∂μ) := by
  rw [tilted_apply _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [exp_sub, div_eq_mul_inv]
    refine Integrable.integrableOn ?_
    exact hf.mul_const _
  · exact ae_of_all _ (fun x ↦ (exp_pos _).le)

lemma lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f) = ∫⁻ x, ENNReal.ofReal (exp (f x - Λ μ f)) * (g x) ∂μ := by
  rw [Measure.tilted, lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const))
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma set_lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f) = ∫⁻ x in s, ENNReal.ofReal (exp (f x - Λ μ f)) * (g x) ∂μ := by
  rw [Measure.tilted, set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine AEMeasurable.restrict ?_
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)
  · exact hs
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, exp (f x - Λ μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, integral_withDensity_eq_integral_smul₀]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - Λ μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma set_integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, exp (f x - Λ μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, set_integral_withDensity_eq_set_integral_smul₀ _ _ hs]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - Λ μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      refine AEMeasurable.restrict ?_
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    0 < ∫ x, exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg]
  · suffices (Function.support fun x ↦ exp (f x)) = Set.univ by
      rw [this]
      simp only [Measure.measure_univ_pos, ne_eq]
      exact hμ.out
    ext1 x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (exp_pos _).ne'
  · exact fun x ↦ (exp_pos _).le
  · exact hf

lemma isProbabilityMeasure_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp only [Measure.tilted, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  simp_rw [exp_sub]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · suffices ∫ x, exp (f x) / exp (Λ μ f) ∂μ = 1 by
      simp only [this, ENNReal.ofReal_one]
    rw [Λ, exp_log]
    · simp_rw [div_eq_mul_inv]
      rw [integral_mul_right, mul_inv_cancel]
      refine (ne_of_lt ?_).symm
      exact integral_exp_pos hf
    · exact integral_exp_pos hf
  · exact hf.div_const _
  · exact ae_of_all _ (fun x ↦ div_nonneg (exp_pos _).le (exp_pos _).le)

lemma Λ_tilted {μ : Measure α} [NeZero μ] {f g : α → ℝ} (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    Λ (μ.tilted f) g = Λ μ (f + g) - Λ μ f := by
  rw [Λ, integral_tilted hf]
  simp_rw [smul_eq_mul, ← exp_add]
  have : (fun x ↦ exp (f x - Λ μ f + g x)) = fun x ↦ exp ((f + g) x) * exp (- Λ μ f) := by
    ext x
    rw [Pi.add_apply, ← exp_add]
    congr 1
    abel
  simp_rw [this]
  rw [integral_mul_right, log_mul (integral_exp_pos hfg).ne' (exp_pos _).ne', log_exp,
    ← sub_eq_add_neg]
  rfl

lemma tilted_tilted {μ : Measure α} {f g : α → ℝ} [NeZero μ] (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  ext1 s hs
  rw [tilted_apply _ _ hs, tilted_apply _ _ hs, set_lintegral_tilted hf _ hs]
  congr with x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← exp_add, Λ_tilted hf hfg, Pi.add_apply]
  congr 2
  abel

lemma absolutelyContinuous_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) :
    μ ≪ μ.tilted f := by
  have : μ = (μ.tilted f).tilted (-f) := by
    rw [tilted_tilted hf ?_, add_right_neg, tilted_zero]
    simp only [Pi.add_apply, Pi.neg_apply, add_right_neg, exp_zero, integrable_const]
  nth_rw 1 [this]
  exact tilted_absolutelyContinuous

lemma rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x - Λ μ f)) :=
  Measure.rnDeriv_withDensity μ (hf.sub measurable_const).exp.ennreal_ofReal

lemma log_rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - Λ μ f := by
  filter_upwards [rnDeriv_tilted_left_self μ hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

lemma rnDeriv_tilted_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x - Λ μ f) * (μ.rnDeriv ν x).toReal := by
  sorry

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + Λ ν f) * (μ.rnDeriv ν x).toReal := by
  sorry

end tilted

section definition

-- TODO: this should be in EReal?
-- TODO: should also take value ∞ when the log is not integrable
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)]
    [Decidable (Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ
    then ENNReal.ofReal (∫ x, log (μ.rnDeriv ν x).toReal ∂μ) else ∞

lemma integrable_toReal_rnDeriv {μ ν : Measure α} [IsFiniteMeasure μ] [SigmaFinite ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma integrable_aux {μ ν : Measure α}
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    Integrable
      (fun x ↦ (Measure.rnDeriv μ ν x).toReal * log (Measure.rnDeriv μ ν x).toReal) ν := by
  rw [← memℒp_one_iff_integrable]
  constructor
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    refine (Measure.measurable_rnDeriv _ _).ennreal_toReal.mul ?_
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log
  rw [snorm_one_eq_lintegral_nnnorm]
  sorry

lemma integral_log_rnDeriv_nonneg_aux {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal
      ≤ ∫ x, log (μ.rnDeriv ν x).toReal ∂μ := by
  have h_eq_int : (μ Set.univ).toReal = ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
    rw [integral_toReal]
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact Measure.rnDeriv_lt_top _ _
  let φ : ℝ → ℝ := fun x ↦ x * log x
  calc (μ Set.univ).toReal * log (μ Set.univ).toReal
    = φ (μ Set.univ).toReal := rfl
  _ = φ (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [h_eq_int]
  _ ≤ ∫ x, φ (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    refine ConvexOn.map_average_le Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
      isClosed_Ici ?_ integrable_toReal_rnDeriv ?_
    · simp
    · exact integrable_aux hμν h_int
  _ = ∫ x, (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal ∂ν := rfl
  _ = ∫ x, log (μ.rnDeriv ν x).toReal ∂μ := by
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

lemma integral_log_rnDeriv_nonneg
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    0 ≤ ∫ x, log (μ.rnDeriv ν x).toReal ∂μ := by
  refine le_trans ?_ (integral_log_rnDeriv_nonneg_aux hμν h_int)
  simp only [measure_univ, ENNReal.one_toReal, log_one, mul_zero, le_refl]

end definition

lemma aemeasurable_of_aemeasurable_exp {μ : Measure α} {f : α → ℝ}
    (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

lemma log_rnDeriv_tilted_ae_eq {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ log ((μ.rnDeriv (ν.tilted f) x).toReal))
      =ᵐ[μ] fun x ↦ - f x + Λ ν f + log (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
  rw [hx, log_mul (exp_pos _).ne']
  · rw [log_exp]
  · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    simp only [hx_pos.ne', hx_lt_top.ne, or_self, not_false_eq_true]

lemma integrable_log_rnDeriv_tilted
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : Measurable f) (hfμ : Integrable f μ)
    (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    Integrable (fun x ↦ log ((μ.rnDeriv (ν.tilted f) x).toReal)) μ := by
  rw [integrable_congr (log_rnDeriv_tilted_ae_eq hμν hf)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma todo_aux {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    ∫ x, log (μ.rnDeriv ν x).toReal ∂μ - ∫ x, log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ
      = ∫ x, f x ∂μ - Λ ν f := by
  calc ∫ x, log (Measure.rnDeriv μ ν x).toReal ∂μ
        - ∫ x, log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ
    = ∫ x, log (Measure.rnDeriv μ ν x).toReal ∂μ
          - ∫ x, - f x + Λ ν f + log (μ.rnDeriv ν x).toReal ∂μ := by
        refine congr_arg₂ _ rfl ?_
        refine integral_congr_ae (log_rnDeriv_tilted_ae_eq hμν ?_)
        -- generalize `log_rnDeriv_tilted_ae_eq, rnDeriv_tilted_right` to require only AEMeasurable
        -- do the same in `Measure.rnDeriv_withDensity`
        suffices AEMeasurable f μ by sorry
        refine aemeasurable_of_aemeasurable_exp ?_
        refine AEStronglyMeasurable.aemeasurable ?_
        exact ⟨hfν.1.mk, hfν.1.stronglyMeasurable_mk, hμν.ae_le hfν.1.ae_eq_mk⟩
  _ = ∫ x, log (Measure.rnDeriv μ ν x).toReal ∂μ
          - (- ∫ x, f x ∂μ + Λ ν f + ∫ x, log ((μ.rnDeriv ν x).toReal) ∂μ) := by
        congr
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, f x ∂μ - Λ ν f := by ring

lemma todo_aux' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ)
    [Decidable (μ ≪ ν)] [Decidable (μ ≪ (ν.tilted f))]
    [Decidable (Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ)]
    [Decidable (Integrable (fun x ↦ log (μ.rnDeriv (ν.tilted f) x).toReal) μ)] :
    (KL μ ν - KL μ (ν.tilted f)).toReal = ∫ x, f x ∂μ - Λ ν f := by
  have hf : Measurable f := sorry
  have h_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hf.aemeasurable
  simp [KL, hμν, h_int, hμν.trans h_ac,
    integrable_log_rnDeriv_tilted hμν hf hfμ h_int]
  sorry

lemma todo' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    ⨆ (f : α → ℝ) (hfμ : Integrable f μ)
        (hfν : Integrable (fun x ↦ exp (f x)) ν), ∫ x, f x ∂μ - Λ ν f
      ≤ ∫ x, log (μ.rnDeriv ν x).toReal ∂μ := by
  have : ∀ (f : α → ℝ) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν),
      ∫ x, f x ∂μ - Λ ν f
        = ∫ x, log (μ.rnDeriv ν x).toReal ∂μ - ∫ x, log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ :=
    fun f hfμ hfν ↦ (todo_aux hμν hfμ hfν h_int).symm
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · rw [this f hfμ hf]
      simp only [hf, ciSup_unique, tsub_le_iff_right, le_add_iff_nonneg_right]
      have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
      have hf_m : Measurable f := sorry
      have h_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hf_m.aemeasurable
      refine integral_log_rnDeriv_nonneg (hμν.trans h_ac) ?_
      exact integrable_log_rnDeriv_tilted hμν hf_m hfμ h_int
    · simp only [hf]
      rw [ciSup_empty]
      exact integral_log_rnDeriv_nonneg hμν h_int
  · simp only [hfμ]
    rw [ciSup_empty]
    exact integral_log_rnDeriv_nonneg hμν h_int

lemma todo {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ log (μ.rnDeriv ν x).toReal) μ) :
    ∫ x, log (μ.rnDeriv ν x).toReal ∂μ
      ≤ ⨆ (f : α → ℝ) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - Λ ν f := by
  refine le_ciSup_of_le ?_ (fun x ↦ log (μ.rnDeriv ν x).toReal) ?_
  · refine ⟨max 0 (∫ x, log (μ.rnDeriv ν x).toReal ∂μ), ?_⟩
    rw [mem_upperBounds]
    intro x
    simp only [Set.mem_range, ge_iff_le, le_max_iff, forall_exists_index]
    rintro f rfl
    by_cases hfμ : Integrable f μ
    · simp only [hfμ, ciSup_unique]
      by_cases hf : Integrable (fun x ↦ exp (f x)) ν
      · simp only [hf, ciSup_unique]
        right
        rw [← todo_aux hμν hfμ hf h_int]
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
        have hf_m : Measurable f := sorry
        have h_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hf_m.aemeasurable
        refine integral_log_rnDeriv_nonneg (hμν.trans h_ac) ?_
        exact integrable_log_rnDeriv_tilted hμν hf_m hfμ h_int
      · simp only [hf, ciSup_empty, le_refl, true_or]
    · simp only [hfμ, ciSup_empty, le_refl, true_or]
  · simp only
    rw [ciSup_pos h_int]
    rw [ciSup_pos]
    swap
    · sorry
    simp only [le_sub_self_iff, Λ]
    suffices ∫ x, exp (log (μ.rnDeriv ν x).toReal) ∂ν = 1 by
      simp [this]
    have : (fun x ↦ exp (log (μ.rnDeriv ν x).toReal))
        =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
      sorry
    rw [integral_congr_ae this]
    sorry

end MeasureTheory
