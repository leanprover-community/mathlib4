/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Triangle inequality for `Lp`-seminorm

In this file we prove several versions of the triangle inequality for the `Lp` seminorm,
as well as simple corollaries.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

variable {α E ε ε' : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  {p : ℝ≥0∞} {q : ℝ} {μ : Measure α} {f g : α → ε}

theorem eLpNorm'_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 ≤ q) : eLpNorm' (f + g) q μ ≤ eLpNorm' f q μ + eLpNorm' g q μ :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (∫⁻ a, ((‖f ·‖ₑ) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ ≤ eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.enorm hg.enorm hq1

theorem eLpNorm'_add_le_of_le_one (hf : AEStronglyMeasurable f μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    eLpNorm' (f + g) q μ ≤ 2 ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (∫⁻ a, (((‖f ·‖ₑ)) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.enorm hq0 hq1

theorem eLpNormEssSup_add_le :
    eLpNormEssSup (f + g) μ ≤ eLpNormEssSup f μ + eLpNormEssSup g μ := by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply]
  exact enorm_add_le _ _

theorem eLpNorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) : eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real

theorem eLpNorm_add_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) :
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
  rcases lt_or_ge p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p ∈ Set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

variable (μ ε) in
/-- Technical lemma to control the addition of functions in `L^p` even for `p < 1`: Given `δ > 0`,
there exists `η` such that two functions bounded by `η` in `L^p` have a sum bounded by `δ`. One
could take `η = δ / 2` for `p ≥ 1`, but the point of the lemma is that it works also for `p < 1`.
-/
theorem exists_Lp_half (p : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ η : ℝ≥0∞,
      0 < η ∧
        ∀ (f g : α → ε), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
          eLpNorm f p μ ≤ η → eLpNorm g p μ ≤ η → eLpNorm (f + g) p μ < δ := by
  have :
    Tendsto (fun η : ℝ≥0∞ => LpAddConst p * (η + η)) (𝓝[>] 0)
        (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf hg p
    _ ≤ LpAddConst p * (η + η) := by gcongr
    _ < δ := hη

theorem eLpNorm_sub_le' {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) :
    eLpNorm (f - g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p

theorem eLpNorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) : eLpNorm (f - g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p

theorem eLpNorm_add_lt_top (hf : MemLp f p μ) (hg : MemLp g p μ) :
    eLpNorm (f + g) p μ < ∞ :=
  calc
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

theorem eLpNorm'_sum_le [ContinuousAdd ε'] {ι} {f : ι → α → ε'} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hq1 : 1 ≤ q) :
    eLpNorm' (∑ i ∈ s, f i) q μ ≤ ∑ i ∈ s, eLpNorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → ε' => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1)).le
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs

theorem eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f : ι → α → ε'} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hp1 : 1 ≤ p) :
    eLpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, eLpNorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → ε' => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero.le
    (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

-- TODO: We can prove `eLpNorm_expect_le` once we have `Module ℚ≥0 ℝ≥0∞`

theorem MemLp.add [ContinuousAdd ε] (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩

theorem MemLp.sub {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem memLp_finsetSum [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι → α → ε'} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun a => ∑ i ∈ s, f i a) p μ := by
  haveI : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp only [MemLp.zero', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum := memLp_finsetSum

theorem memLp_finsetSum' [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι → α → ε'} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (∑ i ∈ s, f i) p μ := by
  convert memLp_finsetSum s hf using 1
  ext x
  simp

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum' := memLp_finsetSum'

end MeasureTheory
