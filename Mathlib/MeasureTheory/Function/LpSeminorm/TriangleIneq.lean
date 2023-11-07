import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.MeanInequalities

open TopologicalSpace MeasureTheory Filter Function ENNReal
open scoped NNReal BigOperators Topology MeasureTheory

variable {ι α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup E] {f g : α → E}

namespace MeasureTheory

/-- `L^∞` norm of the sum of two functions is at most the sum of their `L^∞` norms.
This is a special case of `MeasureTheory.snorm_add_le`
that doesn't require the functions to be `AEStronglyMeasurable`. -/
lemma snorm_add_top_le : snorm (f + g) ∞ μ ≤ snorm f ∞ μ + snorm g ∞ μ := by
  simp only [snorm_exponent_top]
  refine' le_trans (essSup_mono_ae (eventually_of_forall fun x => _)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact nnnorm_add_le _ _
#align measure_theory.snorm_ess_sup_add_le MeasureTheory.snorm_add_top_le

/-- `L⁰` norm of the sum of two functions is at most the sum of their `L⁻` norms.
This is a special case of `MeasureTheory.snorm_add_le`
that doesn't require the functions to be `AEStronglyMeasurable`. -/
lemma snorm_add_zero_le : snorm (f + g) 0 μ ≤ snorm f 0 μ + snorm g 0 μ := by
  simp only [snorm_exponent_zero]
  calc
    μ (support (f + g)) ≤ μ (support f ∪ support g) := measure_mono <| support_add _ _
    _ ≤ μ (support f) + μ (support g) := measure_union_le _ _

theorem snorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ := by
  rcases eq_or_ne p ∞ with rfl | hp_ne_infty; · exact snorm_add_top_le
  lift p to ℝ≥0 using hp_ne_infty
  rcases eq_or_ne p 0 with rfl | hp_ne_zero; · exact snorm_add_zero_le
  cases' le_total p 1 with hp_le_one hone_le_p
  · simp only [snorm_coe_of_ne_zero_le_one _ hp_ne_zero hp_le_one]
    rw [← lintegral_add_left']
    · refine lintegral_mono fun x ↦ ?_
      calc
        (‖f x + g x‖₊ : ℝ≥0∞) ^ (p : ℝ) ≤ (‖f x‖₊ + ‖g x‖₊ : ℝ≥0∞) ^ (p : ℝ) := by
          gcongr; exact coe_le_coe.2 (nnnorm_add_le _ _)
        _ ≤ (‖f x‖₊ : ℝ≥0∞) ^ (p : ℝ) + (‖g x‖₊ : ℝ≥0∞) ^ (p : ℝ) :=
          rpow_add_le_add_rpow _ _ p.2 hp_le_one
    · exact hf.ennnorm.pow_const _
  · simp only [snorm_coe_of_one_le _ hone_le_p]
    refine le_trans ?_ (ENNReal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hone_le_p)
    gcongr
    exact coe_le_coe.2 (nnnorm_add_le _ _)
#align measure_theory.snorm_add_le MeasureTheory.snorm_add_le

#noalign measure_theory.Lp_add_const
#noalign measure_theory.Lp_add_const_of_one_le
#noalign measure_theory.Lp_add_const_zero
#noalign measure_theory.Lp_add_const_lt_top
#noalign measure_theory.snorm_add_le'
#noalign measure_theory.exists_Lp_half
#noalign measure_theory.snorm_sub_le'

theorem snorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    snorm (f - g) p μ ≤ snorm f p μ + snorm g p μ := by
  simpa only [sub_eq_add_neg, snorm_neg] using snorm_add_le hf hg.neg
#align measure_theory.snorm_sub_le MeasureTheory.snorm_sub_le

theorem snorm_add_lt_top {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    snorm (f + g) p μ < ∞ :=
  (snorm_add_le hf.1 hg.1).trans_lt <| add_lt_top.2 ⟨hf.2, hg.2⟩
#align measure_theory.snorm_add_lt_top MeasureTheory.snorm_add_lt_top

theorem Memℒp.add {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩
#align measure_theory.mem_ℒp.add MeasureTheory.Memℒp.add

theorem Memℒp.sub {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
#align measure_theory.mem_ℒp.sub MeasureTheory.Memℒp.sub

lemma Memℒp.max {f g : α → ℝ} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    Memℒp (fun x ↦ max (f x) (g x)) p μ :=
  (hf.norm.add hg.norm).mono_real (hf.1.sup hg.1) <| eventually_of_forall fun _ ↦
    abs_max_le_max_abs_abs.trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))

lemma Memℒp.min {f g : α → ℝ} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    Memℒp (fun x ↦ min (f x) (g x)) p μ :=
  (hf.norm.add hg.norm).mono_real (hf.1.inf hg.1) <| eventually_of_forall fun _ ↦
    abs_min_le_max_abs_abs.trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
#noalign measure_theory.snorm'_sum_le

theorem snorm_sum_le {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) :
    snorm (∑ i in s, f i) p μ ≤ ∑ i in s, snorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm f p μ)
    (fun f => AEStronglyMeasurable f μ) snorm_zero (fun _f _g hf hg => snorm_add_le hf hg)
    (fun _f _g hf hg => hf.add hg) _ hfs
#align measure_theory.snorm_sum_le MeasureTheory.snorm_sum_le

theorem memℒp_finset_sum' (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (∑ i in s, f i) p μ :=
  Finset.sum_induction f (Memℒp · p μ) (fun _ _ ↦ Memℒp.add) zero_memℒp hf
#align measure_theory.mem_ℒp_finset_sum' MeasureTheory.memℒp_finset_sum'

theorem memℒp_finset_sum (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (fun a => ∑ i in s, f i a) p μ := by
  simpa only [← Finset.sum_apply] using memℒp_finset_sum' s hf
#align measure_theory.mem_ℒp_finset_sum MeasureTheory.memℒp_finset_sum
