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

lemma continuous_id_mul_log : Continuous (fun x ↦ x * Real.log x) := by
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * Real.log x) := by
  sorry

lemma id_mul_log_ge {x : ℝ} (hx : 0 ≤ x) :
    Real.log (Real.exp 1) / (Real.exp 1) ≤ x * Real.log x := by
  sorry

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * Real.log x :=
  mul_nonneg (zero_le_one.trans hx) (Real.log_nonneg hx)

lemma measurable_id_mul_log : Measurable (fun x ↦ x * Real.log x) :=
  measurable_id'.mul Real.measurable_log

end Real

end x_log_x

section definition

-- TODO: this should be in EReal?
-- TODO: should also take value ∞ when the log is not integrable
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)]
    [Decidable (Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ
    then ENNReal.ofReal (∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ) else ∞

lemma integrable_toReal_rnDeriv {μ ν : Measure α} [IsFiniteMeasure μ] [SigmaFinite ν] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma integrable_aux {μ ν : Measure α}
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    Integrable
      (fun x ↦ (Measure.rnDeriv μ ν x).toReal * Real.log (Measure.rnDeriv μ ν x).toReal) ν := by
  rw [← memℒp_one_iff_integrable]
  constructor
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    refine (Measure.measurable_rnDeriv _ _).ennreal_toReal.mul ?_
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log
  rw [snorm_one_eq_lintegral_nnnorm]
  sorry

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
      isClosed_Ici ?_ integrable_toReal_rnDeriv ?_
    · simp
    · exact integrable_aux hμν h_int
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

lemma integral_log_rnDeriv_nonneg
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    0 ≤ ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
  refine le_trans ?_ (integral_log_rnDeriv_nonneg_aux hμν h_int)
  simp only [measure_univ, ENNReal.one_toReal, Real.log_one, mul_zero, le_refl]

end definition

section tilted

noncomputable
def Λ (μ : Measure α) (f : α → ℝ) : ℝ := Real.log (∫ x, Real.exp (f x) ∂μ)

@[simp]
lemma Λ_zero_right (μ : Measure α) [IsProbabilityMeasure μ] : Λ μ 0 = 0 := by simp [Λ]

noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) :
    Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (f x - Λ μ f)))

lemma tilted_absolutelyContinuous {μ : Measure α} {f : α → ℝ} :
    μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

@[simp]
lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by
  simp only [Measure.tilted, Λ, Pi.zero_apply, Real.exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, Real.log_one, sub_self, ENNReal.ofReal_one]
  exact withDensity_one

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    0 < ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg]
  · suffices (Function.support fun x ↦ Real.exp (f x)) = Set.univ by
      rw [this]
      simp only [Measure.measure_univ_pos, ne_eq]
      exact hμ.out
    ext1 x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (Real.exp_pos _).ne'
  · exact fun x ↦ (Real.exp_pos _).le
  · exact hf

lemma isProbabilityMeasure_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp only [Measure.tilted, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
  simp_rw [Real.exp_sub]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · suffices ∫ x, Real.exp (f x) / Real.exp (Λ μ f) ∂μ = 1 by
      simp only [this, ENNReal.ofReal_one]
    rw [Λ, Real.exp_log]
    · simp_rw [div_eq_mul_inv]
      rw [integral_mul_right, mul_inv_cancel]
      refine (ne_of_lt ?_).symm
      exact integral_exp_pos hf
    · exact integral_exp_pos hf
  · exact hf.div_const _
  · exact ae_of_all _ (fun x ↦ div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)

lemma tilted_tilted (μ : Measure α) (f g : α → ℝ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  sorry

lemma absolutelyContinuous_tilted {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} :
    μ ≪ μ.tilted f := by
  have : μ = (μ.tilted f).tilted (-f) := by
    rw [tilted_tilted, add_right_neg, tilted_zero]
  nth_rw 1 [this]
  exact tilted_absolutelyContinuous

lemma rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (Real.exp (f x - Λ μ f)) :=
  Measure.rnDeriv_withDensity μ (hf.sub measurable_const).exp.ennreal_ofReal

lemma log_rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ Real.log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - Λ μ f := by
  filter_upwards [rnDeriv_tilted_left_self μ hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

lemma rnDeriv_tilted_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ Real.exp (f x - Λ μ f) * (μ.rnDeriv ν x).toReal := by
  sorry

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ Real.exp (- f x + Λ ν f) * (μ.rnDeriv ν x).toReal := by
  sorry

end tilted

lemma todo_aux {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν)
    (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ - ∫ x, Real.log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ
      = ∫ x, f x ∂μ - Λ ν f := by
  calc ∫ x, Real.log (Measure.rnDeriv μ ν x).toReal ∂μ
        - ∫ x, Real.log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ
    = ∫ x, Real.log (Measure.rnDeriv μ ν x).toReal ∂μ
          - ∫ x, Real.log (Real.exp (- f x + Λ ν f) * (μ.rnDeriv ν x).toReal) ∂μ := by
        refine congr_arg₂ _ rfl ?_
        refine integral_congr_ae (hμν.ae_eq ?_)
        have hf' : Measurable f := by
          -- generalize `rnDeriv_tilted_right` to require only AEMeasurable
          -- do the same in `Measure.rnDeriv_withDensity`
          suffices AEMeasurable f μ by sorry
          have : f = fun x ↦ Real.log (Real.exp (f x)) := by
            ext
            rw [Real.log_exp]
          rw [this]
          refine Real.measurable_log.comp_aemeasurable ?_
          have h' := hfν.1
          sorry
        filter_upwards [rnDeriv_tilted_right μ ν hf'] with x hx
        rw [hx]
  _ = ∫ x, Real.log (Measure.rnDeriv μ ν x).toReal ∂μ
          - ∫ x, - f x + Λ ν f + Real.log (μ.rnDeriv ν x).toReal ∂μ := by
        refine congr_arg₂ _ rfl ?_
        refine integral_congr_ae ?_
        have h_lt_top : ∀ᵐ x ∂μ, Measure.rnDeriv μ ν x < ∞ := hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
        filter_upwards [Measure.rnDeriv_pos hμν, h_lt_top] with x hx_rnDeriv_pos hx_lt_top
        rw [Real.log_mul (Real.exp_pos _).ne']
        · rw [Real.log_exp]
        · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
          simp [hx_rnDeriv_pos.ne', hx_lt_top.ne]
  _ = ∫ x, Real.log (Measure.rnDeriv μ ν x).toReal ∂μ
          - (- ∫ x, f x ∂μ + Λ ν f + ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ) := by
        congr
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, f x ∂μ - Λ ν f := by ring

lemma todo' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    ⨆ (f : α → ℝ) (hfμ : Integrable f μ)
        (hfν : Integrable (fun x ↦ Real.exp (f x)) ν), ∫ x, f x ∂μ - Λ ν f
      ≤ ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ := by
  have : ∀ (f : α → ℝ) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν),
      ∫ x, f x ∂μ - Λ ν f
        = ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ
          - ∫ x, Real.log (μ.rnDeriv (ν.tilted f) x).toReal ∂μ :=
    fun f hfμ hfν ↦ (todo_aux hμν hfμ hfν h_int).symm
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ Real.exp (f x)) ν
    · rw [this f hfμ hf]
      simp only [hf, ciSup_unique, tsub_le_iff_right, le_add_iff_nonneg_right]
      have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
      refine integral_log_rnDeriv_nonneg (hμν.trans absolutelyContinuous_tilted) ?_
      sorry
    · simp only [hf]
      rw [Real.ciSup_empty]
      exact integral_log_rnDeriv_nonneg hμν h_int
  · simp only [hfμ]
    rw [Real.ciSup_empty]
    exact integral_log_rnDeriv_nonneg hμν h_int

lemma todo {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) μ) :
    ∫ x, Real.log (μ.rnDeriv ν x).toReal ∂μ
      ≤ ⨆ (f : α → ℝ) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ Real.exp (f x)) ν),
        ∫ x, f x ∂μ - Λ ν f := by
  refine le_ciSup_of_le ?_ (fun x ↦ Real.log (μ.rnDeriv ν x).toReal) ?_
  · sorry
  · simp only
    rw [ciSup_pos h_int]
    rw [ciSup_pos]
    swap
    · sorry
    simp only [le_sub_self_iff, Λ]
    suffices ∫ x, Real.exp (Real.log (μ.rnDeriv ν x).toReal) ∂ν = 1 by
      simp [this]
    have : (fun x ↦ Real.exp (Real.log (μ.rnDeriv ν x).toReal))
        =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
      sorry
    rw [integral_congr_ae this]
    sorry

end MeasureTheory
