/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-!
# Pointwise convergence of infinite sums in `Lᵖ`

If a series in `Lᵖ` is converging in norm, then the series also converges pointwise
almost everywhere.
-/

public section

open Finset Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {X E : Type*} {_ : MeasurableSpace X} {μ : Measure X} [NormedAddCommGroup E]

/-- If a series of functions has summable `L^p` norms for some `1 ≤ p`, then the norms are ae
pointwise summable. -/
theorem summable_norm_of_tsum_eLpNorm_ne_top {ι : Type*} [Countable ι]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → X → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h'f : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
  suffices H : ∀ᵐ a ∂μ, ∑' n, ‖f n a‖ₑ < ∞ by
    filter_upwards [H] with x hx using tsum_enorm_ne_top_iff_summable_norm.1 hx.ne
  -- the result is straightforward in `L^∞`.
  rcases eq_top_or_lt_top p with rfl | h'p
  · have : ∀ᵐ x ∂μ, ∀ n, ‖f n x‖ₑ ≤ eLpNorm (f n) ∞ μ := ae_all_iff.2 (fun n ↦ ae_le_eLpNormEssSup)
    filter_upwards [this] with x hx
    apply lt_of_le_of_lt ?_ h'f.lt_top
    gcongr with i
    exact hx i
  /- Let us now consider `p < ∞`. In a measurable set `s` of finite measure, the `L^1` norm is
  controlled by a multiple of the `L^p` norm, so the `L^1` norms are summable, i.e.,
  `∫ x ∈ s, ∑ ‖f n x‖ₑ ∂μ < ∞`. This forces the sum to be finite ae. -/
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
      ∀ᵐ x ∂μ, x ∈ s → ∑' n, ‖f n x‖ₑ < ∞ := by
    rw [← ae_restrict_iff' hs]
    apply ae_lt_top' (AEMeasurable.tsum (fun i ↦ (hf i).restrict.enorm))
    rw [lintegral_tsum (fun i ↦ (hf i).restrict.enorm)]
    apply ne_of_lt
    have : ∑' n, eLpNorm (f n) p (μ.restrict s) *
        (μ.restrict s) Set.univ ^ (1 / ENNReal.toReal 1 - 1 / p.toReal) < ∞ := by
      rw [ENNReal.tsum_mul_right]
      apply ENNReal.mul_lt_top ?_ ?_
      · apply lt_of_le_of_lt ?_ h'f.lt_top
        gcongr
        exact Measure.restrict_le_self
      · simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, ENNReal.toReal_one,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, one_div]
        apply ENNReal.rpow_lt_top_of_nonneg _ h's
        simp only [sub_nonneg]
        apply inv_le_one_of_one_le₀
        rw [← ENNReal.ofReal_le_iff_le_toReal h'p.ne]
        simpa
    apply lt_of_le_of_lt ?_ this
    gcongr with i
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hf i).restrict
  /- We wish now to reduce to finite measure sets to apply the above. The function `f n` in `L^p`
  has a sigma-finite support, that we denote by `s n`. -/
  have B n : ∃ s, MeasurableSet s ∧ (f n =ᵐ[μ.restrict sᶜ] 0) ∧ SigmaFinite (μ.restrict s) := by
    apply AEFinStronglyMeasurable.exists_set_sigmaFinite
    have : MemLp (f n) p μ := by
      simpa [MemLp, hf] using lt_of_le_of_lt (ENNReal.le_tsum n) h'f.lt_top
    exact this.aefinStronglyMeasurable (zero_lt_one.trans_le hp).ne' h'p.ne
  choose! s s_meas hs h's using B
  /- Covering `s n` by countably many sets of finite measure, we deduce using the above that
  the series of norms is ae finite on `s n`. -/
  have C : ∀ᵐ x ∂μ, ∀ n, x ∈ s n → ∑' n, ‖f n x‖ₑ < ∞ := by
    apply ae_all_iff.2 (fun n ↦ ?_)
    have : ∀ᵐ x ∂μ, ∀ i, x ∈ s n ∩ spanningSets (μ.restrict (s n)) i → ∑' n, ‖f n x‖ₑ < ∞ := by
      apply ae_all_iff.2 (fun i ↦ ?_)
      apply A _ ((s_meas n).inter (measurableSet_spanningSets _ _))
      rw [Set.inter_comm, ← Measure.restrict_apply' (s_meas n)]
      exact (measure_spanningSets_lt_top _ _).ne
    filter_upwards [this] with x hx h'x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ spanningSets (μ.restrict (s n)) i := ⟨_, mem_spanningSetsIndex _ _⟩
    exact hx i ⟨h'x, hi⟩
  /- Finally, we get the result in `⋃ n, s n`. Outside of this set, all the functions are ae
  zero, so the result is trivial there. -/
  have D : ∀ᵐ x ∂μ, ∀ n, x ∉ s n → f n x = 0 :=
    ae_all_iff.2 (fun n ↦ (ae_restrict_iff' (s_meas n).compl).1 (hs n))
  filter_upwards [C, D] with x hx h'x
  by_cases! h : ∃ n, x ∈ s n
  · rcases h with ⟨n, hn⟩
    exact hx n hn
  · have E n : f n x = 0 := h'x n (h n)
    simp [E]

namespace Lp

private theorem hasSum_coeFn_tsum_nat {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [CompleteSpace E] {f : ℕ → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ∀ᵐ a ∂μ, HasSum (fun n ↦ f n a) (⇑(∑' n, f n) a) := by
  have A : ∀ᵐ a ∂μ, Summable (fun n ↦ ‖f n a‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top hp.out (fun n ↦ Lp.aestronglyMeasurable (f n))
    simpa [enorm_def] using hf
  have B : ∀ᵐ x ∂μ, ∀ n, ⇑(∑ i ∈ range n, f i) x = ∑ i ∈ range n, f i x := by
    rw [ae_all_iff]
    exact fun i ↦ coeFn_fun_finsetSum _ _
  obtain ⟨ns, hns, nslim⟩ : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Tendsto (fun i ↦ (∑ j ∈ range (ns i), f j : Lp E p μ) x) atTop (𝓝 ((∑' n, f n) x)) := by
    have : Tendsto (fun i ↦ (∑ j ∈ range i, f j)) atTop (𝓝 (∑' n, f n)) :=
      Summable.tendsto_sum_tsum_nat (Summable.of_enorm hf)
    exact (tendstoInMeasure_of_tendsto_Lp this).exists_seq_tendsto_ae
  filter_upwards [A, B, nslim] with x S h'x h''x
  apply hasSum_of_subseq_of_summable S (tendsto_finset_range.comp hns.tendsto_atTop)
  simpa only [h'x, Function.comp] using h''x

/-- If a series is converging in `L^p`, then it also converges pointwise almost everywhere. -/
theorem hasSum_coeFn_tsum {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {ι : Type*} [Countable ι]
    [CompleteSpace E] {f : ι → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ∀ᵐ a ∂μ, HasSum (fun n ↦ f n a) (⇑(∑' n, f n) a) := by
  classical
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    filter_upwards [coeFn_fun_finsetSum univ f] with x hx
    rw [tsum_fintype, hx]
    exact hasSum_fintype _
  · obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := ι)
    have : ∀ᵐ a ∂μ, HasSum (fun n ↦ f (e n) a) (⇑(∑' n, f (e n)) a) := by
      apply Lp.hasSum_coeFn_tsum_nat
      convert hf
      exact e.tsum_eq (fun i ↦ ‖f i‖ₑ)
    filter_upwards [this] with x hx
    rw [e.tsum_eq] at hx
    exact e.hasSum_iff.1 hx

theorem coeFn_tsum {ι : Type*} [Countable ι] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [CompleteSpace E] {f : ι → Lp E p μ} (hf : ∑' n, ‖f n‖ₑ ≠ ∞) :
    ⇑(∑' n, f n) =ᵐ[μ] fun x ↦ ∑' n, f n x := by
  filter_upwards [Lp.hasSum_coeFn_tsum hf] with x hx using hx.tsum_eq.symm

end Lp

end MeasureTheory
