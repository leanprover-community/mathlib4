/-
Copyright (c) 20XX WHO WHO??. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO NAME
-/
--import Mathlib.Data.Set.Intervals.Disjoint
import Mathlib.MeasureTheory.Integral.SetIntegral
--import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- TODO: minimize imports!

/-!
## TODO a docstring

-/


-- from Bochner
-- TODO: minimise opens and variables

open scoped Topology BigOperators NNReal ENNReal MeasureTheory

open Set Filter TopologicalSpace ENNReal EMetric

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

open ContinuousLinearMap MeasureTheory.SimpleFunc

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [hE : CompleteSpace E] [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {f g : α → E} {m : MeasurableSpace α} {μ : Measure α}


/-- **Lebesgue dominated convergence theorem** provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound F_measurable bound_integrable h_bound h_lim
  · simp [integral, hG]
#align measure_theory.tendsto_integral_of_dominated_convergence MeasureTheory.tendsto_integral_of_dominated_convergence

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} {f : α → G} (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound hF_meas h_bound bound_integrable h_lim
  · simp [integral, hG, tendsto_const_nhds]
#align measure_theory.tendsto_integral_filter_of_dominated_convergence MeasureTheory.tendsto_integral_filter_of_dominated_convergence

/-- Lebesgue dominated convergence theorem for series. -/
theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → α → G} {f : α → G}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) := by
  have hb_nonneg : ∀ᵐ a ∂μ, ∀ n, 0 ≤ bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : ∀ n, bound n ≤ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using le_tsum ha_sum _ fun i _ => ha0 i
  have hF_integrable : ∀ n, Integrable (F n) μ := by
    refine' fun n => bound_integrable.mono' (hF_meas n) _
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← integral_finset_sum _ fun n _ => hF_integrable n]
  refine' tendsto_integral_filter_of_dominated_convergence
      (fun a => ∑' n, bound n a) _ _ bound_integrable h_lim
  · exact eventually_of_forall fun s => s.aestronglyMeasurable_sum fun n _ => hF_meas n
  · refine' eventually_of_forall fun s => _
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n in s, F n a‖ ≤ ∑ n in s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ ≤ ∑' n, bound n a := sum_le_tsum _ (fun n _ => ha0 n) has
#align measure_theory.has_sum_integral_of_dominated_convergence MeasureTheory.hasSum_integral_of_dominated_convergence

theorem integral_tsum {ι} [Countable ι] {f : ι → α → G} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖₊ ∂μ ≠ ∞) :
    ∫ a : α, ∑' i, f i a ∂μ = ∑' i, ∫ a : α, f i a ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hf'' : ∀ i, AEMeasurable (fun x => (‖f i x‖₊ : ℝ≥0∞)) μ := fun i => (hf i).ennnorm
  have hhh : ∀ᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine' (ae_lt_top' (AEMeasurable.ennreal_tsum hf'') hf').mono _
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert (MeasureTheory.hasSum_integral_of_dominated_convergence (fun i a => ‖f i a‖₊) hf _ hhh
          ⟨_, _⟩ _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · simp_rw [← NNReal.coe_tsum]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.coe_nnreal_real
    apply AEMeasurable.nnreal_tsum
    exact fun i => (hf i).nnnorm.aemeasurable
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖₊ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum
#align measure_theory.integral_tsum MeasureTheory.integral_tsum

lemma hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀  i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ) := by
  rw [integral_tsum (fun i ↦ (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded _ fun i ↦ norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ (a : α), ‖F i a‖₊ ∂μ = ‖(∫ a : α, ‖F i a‖ ∂μ)‖₊ := by
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    rfl
  rw [funext this, ← ENNReal.coe_tsum]
  · apply coe_ne_top
  · simp_rw [← NNReal.summable_coe, coe_nnnorm]
    exact hF_sum.abs

lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀  i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

end MeasureTheory

section TendstoMono -- from SetIntegral

open MeasureTheory

variable {α E : Type*} [MeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ → Set α}
  {f : α → E}

theorem _root_.Antitone.tendsto_set_integral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine' tendsto_integral_of_dominated_convergence bound _ _ _ _
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti (zero_le n))).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine' fun n => eventually_of_forall fun x => _
    exact indicator_le_indicator_of_subset (h_anti (zero_le n)) (fun a => norm_nonneg _) _
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)
#align antitone.tendsto_set_integral Antitone.tendsto_set_integral

end TendstoMono
