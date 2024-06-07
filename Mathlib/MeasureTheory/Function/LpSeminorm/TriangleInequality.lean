/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# Triangle inequality for `Lp`-seminorm

In this file we prove several versions of the triangle inequality for the `Lp` seminorm,
as well as simple corollaries.
-/

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {q : ℝ} {μ : Measure α} {f g : α → E}

theorem snorm'_add_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 ≤ q) : snorm' (f + g) q μ ≤ snorm' f q μ + snorm' g q μ :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ snorm' f q μ + snorm' g q μ := ENNReal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hq1
#align measure_theory.snorm'_add_le MeasureTheory.snorm'_add_le

theorem snorm'_add_le_of_le_one {f g : α → E} (hf : AEStronglyMeasurable f μ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : snorm' (f + g) q μ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (snorm' f q μ + snorm' g q μ) :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (snorm' f q μ + snorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.ennnorm hq0 hq1
#align measure_theory.snorm'_add_le_of_le_one MeasureTheory.snorm'_add_le_of_le_one

theorem snormEssSup_add_le {f g : α → E} :
    snormEssSup (f + g) μ ≤ snormEssSup f μ + snormEssSup g μ := by
  refine le_trans (essSup_mono_ae (eventually_of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact nnnorm_add_le _ _
#align measure_theory.snorm_ess_sup_add_le MeasureTheory.snormEssSup_add_le

theorem snorm_add_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) : snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, snormEssSup_add_le]
  have hp1_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.one_toReal, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [snorm_eq_snorm' hp0 hp_top]
  exact snorm'_add_le hf hg hp1_real
#align measure_theory.snorm_add_le MeasureTheory.snorm_add_le

/-- A constant for the inequality `‖f + g‖_{L^p} ≤ C * (‖f‖_{L^p} + ‖g‖_{L^p})`. It is equal to `1`
for `p ≥ 1` or `p = 0`, and `2^(1/p-1)` in the more tricky interval `(0, 1)`. -/
noncomputable def LpAddConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p ∈ Set.Ioo (0 : ℝ≥0∞) 1 then (2 : ℝ≥0∞) ^ (1 / p.toReal - 1) else 1
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_add_const MeasureTheory.LpAddConst

theorem LpAddConst_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) : LpAddConst p = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ (h.2.trans_le hp)
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_add_const_of_one_le MeasureTheory.LpAddConst_of_one_le

theorem LpAddConst_zero : LpAddConst 0 = 1 := by
  rw [LpAddConst, if_neg]
  intro h
  exact lt_irrefl _ h.1
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_add_const_zero MeasureTheory.LpAddConst_zero

theorem LpAddConst_lt_top (p : ℝ≥0∞) : LpAddConst p < ∞ := by
  rw [LpAddConst]
  split_ifs with h
  · apply ENNReal.rpow_lt_top_of_nonneg _ ENNReal.two_ne_top
    simp only [one_div, sub_nonneg]
    apply one_le_inv (ENNReal.toReal_pos h.1.ne' (h.2.trans ENNReal.one_lt_top).ne)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h.2.le
  · exact ENNReal.one_lt_top
set_option linter.uppercaseLean3 false in
#align measure_theory.Lp_add_const_lt_top MeasureTheory.LpAddConst_lt_top

theorem snorm_add_le' {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp only [snorm_exponent_zero, add_zero, mul_zero, le_zero_iff]
  rcases lt_or_le p 1 with (h'p | h'p)
  · simp only [snorm_eq_snorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert snorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p ∈ Set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simp [LpAddConst_of_one_le h'p]
    exact snorm_add_le hf hg h'p
#align measure_theory.snorm_add_le' MeasureTheory.snorm_add_le'

variable (μ E)

/-- Technical lemma to control the addition of functions in `L^p` even for `p < 1`: Given `δ > 0`,
there exists `η` such that two functions bounded by `η` in `L^p` have a sum bounded by `δ`. One
could take `η = δ / 2` for `p ≥ 1`, but the point of the lemma is that it works also for `p < 1`.
-/
theorem exists_Lp_half (p : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ η : ℝ≥0∞,
      0 < η ∧
        ∀ (f g : α → E), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
          snorm f p μ ≤ η → snorm g p μ ≤ η → snorm (f + g) p μ < δ := by
  have :
    Tendsto (fun η : ℝ≥0∞ => LpAddConst p * (η + η)) (𝓝[>] 0) (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := snorm_add_le' hf hg p
    _ ≤ LpAddConst p * (η + η) := by gcongr
    _ < δ := hη
set_option linter.uppercaseLean3 false in
#align measure_theory.exists_Lp_half MeasureTheory.exists_Lp_half

variable {μ E}

theorem snorm_sub_le' {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : snorm (f - g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := by
  simpa only [sub_eq_add_neg, snorm_neg] using snorm_add_le' hf hg.neg p
#align measure_theory.snorm_sub_le' MeasureTheory.snorm_sub_le'

theorem snorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) : snorm (f - g) p μ ≤ snorm f p μ + snorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using snorm_sub_le' hf hg p
#align measure_theory.snorm_sub_le MeasureTheory.snorm_sub_le

theorem snorm_add_lt_top {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    snorm (f + g) p μ < ∞ :=
  calc
    snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) :=
      snorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p).ne
      exact (ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩).ne
#align measure_theory.snorm_add_lt_top MeasureTheory.snorm_add_lt_top

theorem snorm'_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hq1 : 1 ≤ q) :
    snorm' (∑ i ∈ s, f i) q μ ≤ ∑ i ∈ s, snorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (snorm'_zero (zero_lt_one.trans_le hq1))
    (fun _f _g hf hg => snorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs
#align measure_theory.snorm'_sum_le MeasureTheory.snorm'_sum_le

theorem snorm_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hp1 : 1 ≤ p) :
    snorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, snorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm f p μ)
    (fun f => AEStronglyMeasurable f μ) snorm_zero (fun _f _g hf hg => snorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs
#align measure_theory.snorm_sum_le MeasureTheory.snorm_sum_le

theorem Memℒp.add {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩
#align measure_theory.mem_ℒp.add MeasureTheory.Memℒp.add

theorem Memℒp.sub {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
#align measure_theory.mem_ℒp.sub MeasureTheory.Memℒp.sub

theorem memℒp_finset_sum {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (fun a => ∑ i ∈ s, f i a) p μ := by
  haveI : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp only [zero_mem_ℒp', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
#align measure_theory.mem_ℒp_finset_sum MeasureTheory.memℒp_finset_sum

theorem memℒp_finset_sum' {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (∑ i ∈ s, f i) p μ := by
  convert memℒp_finset_sum s hf using 1
  ext x
  simp
#align measure_theory.mem_ℒp_finset_sum' MeasureTheory.memℒp_finset_sum'
