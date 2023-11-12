/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Log-likelihood Ratio

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

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

section move_this

lemma absolutelyContinuous_withDensity_rnDeriv {μ ν : Measure α} [SigmaFinite ν] [SigmaFinite μ]
    (hμν : μ ≪ ν) :
    μ ≪ μ.withDensity (ν.rnDeriv μ) := by
  rw [Measure.haveLebesgueDecomposition_add ν μ] at hμν
  refine Measure.AbsolutelyContinuous.mk (fun s _ hνs ↦ ?_)
  have h_sing := Measure.mutuallySingular_singularPart ν μ
  obtain ⟨t, _, ht1, ht2⟩ := h_sing -- todo: provide API
  have hs_eq_union : s = s ∩ t ∪ s ∩ tᶜ := by ext x; simp
  rw [hs_eq_union]
  refine le_antisymm ((measure_union_le (s ∩ t) (s ∩ tᶜ)).trans ?_) (zero_le _)
  simp only [nonpos_iff_eq_zero, add_eq_zero]
  constructor
  · refine hμν ?_
    simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply, add_eq_zero]
    constructor
    · exact measure_mono_null (Set.inter_subset_right _ _) ht1
    · exact measure_mono_null (Set.inter_subset_left _ _) hνs
  · exact measure_mono_null (Set.inter_subset_right _ _) ht2

lemma rnDeriv_pos' {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < ν.rnDeriv μ x := by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx hx2
  rwa [← hx2]

lemma rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ ↦ 1 :=
  (Measure.eq_rnDeriv (measurable_const) Measure.MutuallySingular.zero_left (by simp)).symm

lemma Measure.AbsolutelyContinuous.add {μ μ' ν ν' : Measure α} (h1 : μ ≪ ν) (h2 : μ' ≪ ν') :
    μ + μ' ≪ ν + ν' := by
  intro s hs
  simp only [add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩

lemma Measure.AbsolutelyContinuous.add_right {μ ν : Measure α} (h1 : μ ≪ ν) (ν' : Measure α) :
    μ ≪ ν + ν' := by
  intro s hs
  simp only [add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

lemma Measure.AbsolutelyContinuous.restrict {μ ν : Measure α} (h : μ ≪ ν) (s : Set α) :
    μ.restrict s ≪ ν.restrict s := by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν ↦ ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

lemma rnDeriv_add_right_of_mutuallySingular {μ ν ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν']
    (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  sorry -- proved in another branch

lemma inv_rnDeriv' {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  sorry -- proved in another branch

lemma todo_div {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have hν_ac : ν ≪ μ + ν := by
    rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h_pos := Measure.rnDeriv_pos hν_ac
  have h := rnDeriv_mul_rnDeriv hμν hν_ac
  filter_upwards [hν_ac.ae_le h, h_pos, hν_ac.ae_le (Measure.rnDeriv_ne_top ν (μ + ν))]
    with x hx hx_pos hx_ne_top
  rw [Pi.mul_apply] at hx
  rwa [ENNReal.eq_div_iff hx_pos.ne' hx_ne_top, mul_comm]

end move_this

@[measurability]
lemma measurable_toReal_rnDeriv (μ ν : Measure α) : Measurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal

lemma stronglyMeasurable_toReal_rnDeriv (μ ν : Measure α) :
    StronglyMeasurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (measurable_toReal_rnDeriv μ ν).stronglyMeasurable

/-- Log-Likelihood Ratio. -/
noncomputable
def LLR (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma llr_def (μ ν : Measure α) : LLR μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl

lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (LLR μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [LLR, h_zero, ENNReal.zero_toReal, log_zero, exp_zero, ite_true]
  rw [LLR, exp_log, if_neg h_zero]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm h_zero), hx⟩

lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (LLR μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']

@[measurability]
lemma measurable_llr (μ ν : Measure α) : Measurable (LLR μ ν) :=
  (measurable_toReal_rnDeriv μ ν).log

@[measurability]
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (LLR μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable

lemma llr_smul_left {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR (c • μ) ν =ᵐ[μ] fun x ↦ LLR μ ν x + log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  ring

lemma llr_smul_right {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR μ (c • ν) =ᵐ[μ] fun x ↦ LLR μ ν x - log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  rw [ENNReal.toReal_inv, log_inv]
  ring

lemma integrable_toReal_rnDeriv_mul {μ ν : Measure α} {f : α → ℝ} [SigmaFinite μ]
    [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (h_int : Integrable f μ) (hf : AEStronglyMeasurable f ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * f x) ν := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨(stronglyMeasurable_toReal_rnDeriv μ ν).aestronglyMeasurable.mul hf, ?_⟩
  simp only [snorm_one_eq_lintegral_nnnorm, nnnorm_mul, ENNReal.coe_mul]
  simp_rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg ENNReal.toReal_nonneg,
    ofReal_norm_eq_coe_nnnorm]
  have h : ∀ᵐ x ∂ν, ENNReal.ofReal (μ.rnDeriv ν x).toReal * ‖f x‖₊ = μ.rnDeriv ν x * ‖f x‖₊ := by
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx using by rw [ENNReal.ofReal_toReal hx]
  rw [lintegral_congr_ae h]
  change ∫⁻ a, (μ.rnDeriv ν * (fun a ↦ (‖f a‖₊ : ℝ≥0∞))) a ∂ν < ⊤
  rw [← lintegral_withDensity_eq_lintegral_mul_non_measurable]
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
    exact h_int.2
  · exact Measure.measurable_rnDeriv _ _
  · exact Measure.rnDeriv_lt_top _ _

section llr_tilted

variable {μ ν : Measure α} [IsFiniteMeasure ν]

lemma llr_tilted_ae_eq [IsFiniteMeasure μ]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : AEMeasurable f ν) :
    (LLR μ (ν.tilted f)) =ᵐ[μ] fun x ↦ - f x + logIntegralExp ν f + LLR μ ν x := by
  filter_upwards [hμν.ae_le (ofReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
  rw [LLR, hx, log_mul (exp_pos _).ne']
  · rw [log_exp, LLR]
  · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    simp only [hx_pos.ne', hx_lt_top.ne, or_self, not_false_eq_true]

lemma integrable_llr_tilted [IsFiniteMeasure μ]
    (hμν : μ ≪ ν) {f : α → ℝ} (hfμ : Integrable f μ)
    (hfν : AEMeasurable f ν) (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LLR μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_ae_eq hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma integral_llr_tilted [IsProbabilityMeasure μ]
    {f : α → ℝ} (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : AEMeasurable f ν)
    (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + logIntegralExp ν f := by
  calc ∫ x, LLR μ (ν.tilted f) x ∂μ
    = ∫ x, - f x + logIntegralExp ν f + LLR μ ν x ∂μ := integral_congr_ae (llr_tilted_ae_eq hμν hfν)
  _ = - ∫ x, f x ∂μ + logIntegralExp ν f + ∫ x, LLR μ ν x ∂μ := by
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + logIntegralExp ν f := by abel

end llr_tilted

lemma neg_llr {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    - LLR μ ν =ᵐ[μ] LLR ν μ := by
  filter_upwards [inv_rnDeriv' hμν] with x hx
  rw [Pi.neg_apply, LLR, LLR, ← log_inv, ← ENNReal.toReal_inv]
  congr

lemma exp_neg_llr {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (- LLR μ ν x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr ν μ, rnDeriv_pos' hμν] with x hx hx_exp_log hx_pos
  rw [Pi.neg_apply] at hx
  rw [hx, hx_exp_log]
  simp [hx_pos.ne']

lemma set_lintegral_rnDeriv_le {μ ν : Measure α} (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s := by
  let t := toMeasurable μ s
  calc ∫⁻ x in s, μ.rnDeriv ν x ∂ν
    ≤ ∫⁻ x in t, μ.rnDeriv ν x ∂ν := lintegral_mono_set (subset_toMeasurable μ s)
  _ ≤ μ t := by
        rw [← withDensity_apply _ (measurableSet_toMeasurable μ s)]
        exact Measure.withDensity_rnDeriv_le _ _ _ (measurableSet_toMeasurable μ s)
  _ = μ s := by rw [← measure_toMeasurable s]

lemma integrableOn_exp_neg_llr {μ ν : Measure α} [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν)
    (s : Set α) (hνs : ν s ≠ ∞) :
    IntegrableOn (fun x ↦ exp (- LLR μ ν x)) s μ := by
  constructor
  · refine AEStronglyMeasurable.restrict ?_
    refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (measurable_llr _ _).neg.exp.stronglyMeasurable
  · rw [hasFiniteIntegral_def]
    set t := toMeasurable ν s with ht_eq
    have ht : MeasurableSet t := measurableSet_toMeasurable ν s
    have hνt : ν t ≠ ∞ := by rwa [ht_eq, measure_toMeasurable s]
    calc ∫⁻ a in s, ‖rexp (-LLR μ ν a)‖₊ ∂μ
      ≤ ∫⁻ a in t, ‖rexp (-LLR μ ν a)‖₊ ∂μ := lintegral_mono_set (subset_toMeasurable ν s)
    _ = ∫⁻ a in t, ‖(ν.rnDeriv μ a).toReal‖₊ ∂μ := by
        refine set_lintegral_congr_fun ht ?_
        filter_upwards [exp_neg_llr hμν] with x hx _
        rw [hx]
    _ = ∫⁻ a in t, ν.rnDeriv μ a ∂μ := by
        refine set_lintegral_congr_fun ht ?_
        filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx _
        rw [← ofReal_norm_eq_coe_nnnorm]
        simp [hx]
    _ ≤ ν t := set_lintegral_rnDeriv_le t
    _ < ∞ := hνt.lt_top


end MeasureTheory
