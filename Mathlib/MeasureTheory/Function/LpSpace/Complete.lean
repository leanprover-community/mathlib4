/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `Lp` is a complete space

In this file we show that `Lp` is a complete space for `1 ≤ p`,
in `MeasureTheory.Lp.instCompleteSpace`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [SeminormedAddGroup E]

namespace MeasureTheory.Lp

theorem eLpNorm'_lim_eq_lintegral_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → E} {p : ℝ}
    {f_lim : α → E} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ = (∫⁻ a, atTop.liminf (‖f · a‖ₑ ^ p) ∂μ) ^ (1 / p) := by
  suffices h_no_pow : (∫⁻ a, ‖f_lim a‖ₑ ^ p ∂μ) = ∫⁻ a, atTop.liminf fun m => ‖f m a‖ₑ ^ p ∂μ by
    rw [eLpNorm'_eq_lintegral_enorm, h_no_pow]
  refine lintegral_congr_ae (h_lim.mono fun a ha => ?_)
  dsimp only
  rw [Tendsto.liminf_eq]
  refine (ENNReal.continuous_rpow_const.tendsto ‖f_lim a‖₊).comp ?_
  exact (continuous_enorm.tendsto (f_lim a)).comp ha

theorem eLpNorm'_lim_le_liminf_eLpNorm' {f : ℕ → α → E} {p : ℝ}
    (hp_pos : 0 < p) (hf : ∀ n, AEStronglyMeasurable (f n) μ) {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ ≤ atTop.liminf fun n => eLpNorm' (f n) p μ := by
  rw [eLpNorm'_lim_eq_lintegral_liminf h_lim]
  rw [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  refine (lintegral_liminf_le' fun m => (hf m).enorm.pow_const _).trans_eq ?_
  have h_pow_liminf :
    atTop.liminf (fun n ↦ eLpNorm' (f n) p μ) ^ p
      = atTop.liminf fun n ↦ eLpNorm' (f n) p μ ^ p := by
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_pow_liminf]
  simp_rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hp_pos.ne.symm, ENNReal.rpow_one]

theorem eLpNorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → E}
    {f_lim : α → E} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ = essSup (fun x => atTop.liminf fun m => ‖f m x‖ₑ) μ := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  refine essSup_congr_ae (h_lim.mono fun x hx => ?_)
  dsimp only
  apply (Tendsto.liminf_eq ..).symm
  exact (continuous_enorm.tendsto (f_lim x)).comp hx

theorem eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top {ι} [Nonempty ι] [Countable ι]
    [LinearOrder ι] {f : ι → α → E} {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ ≤ atTop.liminf fun n => eLpNorm (f n) ∞ μ := by
  rw [eLpNorm_exponent_top_lim_eq_essSup_liminf h_lim]
  simp_rw [eLpNorm_exponent_top, eLpNormEssSup]
  exact ENNReal.essSup_liminf_le _

theorem eLpNorm_lim_le_liminf_eLpNorm {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (f_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim p μ ≤ atTop.liminf fun n => eLpNorm (f n) p μ := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  by_cases hp_top : p = ∞
  · simp_rw [hp_top]
    exact eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top h_lim
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  exact eLpNorm'_lim_le_liminf_eLpNorm' hp_pos hf h_lim

/-- If the `eLpNorm` of a collection of `AEStronglyMeasurable` functions that converges almost
everywhere is bounded by some constant `C`, then the `eLpNorm` of its limit is also bounded by
`C`. -/
theorem eLpNorm_le_of_ae_tendsto {ι : Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} {C : ℝ≥0∞} (bound : ∀ᶠ n in u, eLpNorm (f n) p μ ≤ C)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ (x : α) ∂μ, Tendsto (f · x) u (𝓝 (g x))) :
    eLpNorm g p μ ≤ C := by
  obtain ⟨v, hv⟩ := exists_seq_tendsto u
  have : ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f (v n) x) atTop (𝓝 (g x)) := by
    filter_upwards [h_tendsto] with x hx
    exact hx.comp hv
  calc
  _ ≤ atTop.liminf (fun (n : ℕ) => eLpNorm (f (v n)) p μ) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf (v n)) g this
  _ ≤ C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := (hb.and (hv.eventually bound)).exists
    exact hn.1.trans hn.2

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/

variable {E : Type*} [NormedAddCommGroup E]

theorem tendsto_Lp_iff_tendsto_eLpNorm' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : Lp E p μ) :
    fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n => eLpNorm (⇑(f n) - ⇑f_lim) p μ) (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _

theorem tendsto_Lp_iff_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0) := by
  rw [tendsto_Lp_iff_tendsto_eLpNorm']
  suffices h_eq :
      (fun n => eLpNorm (⇑(f n) - ⇑(MemLp.toLp f_lim f_lim_ℒp)) p μ) =
        (fun n => eLpNorm (⇑(f n) - f_lim) p μ) by
    rw [h_eq]
  exact funext fun n => eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp f_lim_ℒp))

theorem tendsto_Lp_iff_tendsto_eLpNorm'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E)
    (f_ℒp : ∀ n, MemLp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)]
  refine Filter.tendsto_congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coeFn_toLp,
    Lp.coeFn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)] with _ hx₁ hx₂
  rw [← hx₂]
  exact hx₁

theorem tendsto_Lp_of_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] {f : ι → Lp E p μ}
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ)
    (h_tendsto : fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) :=
  (tendsto_Lp_iff_tendsto_eLpNorm f f_lim f_lim_ℒp).mpr h_tendsto

theorem cauchySeq_Lp_iff_cauchySeq_eLpNorm {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)]
    (f : ι → Lp E p μ) :
    CauchySeq f ↔ Tendsto (fun n : ι × ι => eLpNorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) atTop (𝓝 0) := by
  simp_rw [cauchySeq_iff_tendsto_dist_atTop_0, dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact eLpNorm_ne_top _

theorem completeSpace_lp_of_cauchy_complete_eLpNorm [hp : Fact (1 ≤ p)]
    (H :
      ∀ (f : ℕ → α → E) (_ : ∀ n, MemLp (f n) p μ) (B : ℕ → ℝ≥0∞) (_ : ∑' i, B i < ∞)
        (_ : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N),
        ∃ (f_lim : α → E), MemLp f_lim p μ ∧
          atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) :
    CompleteSpace (Lp E p μ) := by
  let B := fun n : ℕ => ((1 : ℝ) / 2) ^ n
  have hB_pos : ∀ n, 0 < B n := fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n
  refine Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => ?_
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)
  · exact ⟨hf_lim_meas.toLp f_lim, tendsto_Lp_of_tendsto_eLpNorm f_lim hf_lim_meas h_tendsto⟩
  obtain ⟨M, hB⟩ : Summable B := summable_geometric_two
  let B1 n := ENNReal.ofReal (B n)
  have hB1_has : HasSum B1 (ENNReal.ofReal M) := by
    have h_tsum_B1 : ∑' i, B1 i = ENNReal.ofReal M := by
      change (∑' n : ℕ, ENNReal.ofReal (B n)) = ENNReal.ofReal M
      rw [← hB.tsum_eq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => le_of_lt (hB_pos n)) hB.summable).symm
    have h_sum := (CompleteLattice.summable (f := B1)).hasSum
    rwa [h_tsum_B1] at h_sum
  have hB1 : ∑' i, B1 i < ∞ := by
    rw [hB1_has.tsum_eq]
    exact ENNReal.ofReal_lt_top
  let f1 : ℕ → α → E := fun n => f n
  refine H f1 (fun n => Lp.memLp (f n)) B1 hB1 fun N n m hn hm => ?_
  specialize hf N n m hn hm
  rw [dist_def] at hf
  dsimp only [f1]
  rwa [ENNReal.lt_ofReal_iff_toReal_lt]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/

private theorem eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) (n : ℕ) :
    eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i := by
  let f_norm_diff i x := ‖f (i + 1) x - f i x‖
  have hgf_norm_diff :
    ∀ n,
      (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) =
        ∑ i ∈ Finset.range (n + 1), f_norm_diff i :=
    fun n => funext fun x => by simp [f_norm_diff]
  rw [hgf_norm_diff]
  refine (eLpNorm'_sum_le (fun i _ => ((hf (i + 1)).sub (hf i)).norm) hp1).trans ?_
  simp_rw [eLpNorm'_norm]
  refine (Finset.sum_le_sum ?_).trans <| sum_le_tsum _
  exact fun m _ => (h_cau m (m + 1) m (Nat.le_succ m) (le_refl m)).le

private theorem lintegral_rpow_sum_enorm_sub_le_rpow_tsum
    {f : ℕ → α → E} {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
    (hn : eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
    (∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  rw [← inv_inv p, @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [hp_pos]), inv_inv p]
  simp_rw [eLpNorm'_eq_lintegral_enorm, one_div] at hn
  have h_nnnorm_nonneg :
    (fun a => ‖∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖‖ₑ ^ p) = fun a =>
      (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p := by
    ext1 a
    congr
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Real.norm_of_nonneg _]
      exact Finset.sum_nonneg fun x _ => norm_nonneg _
    · exact fun x _ => norm_nonneg _
  rwa [h_nnnorm_nonneg] at hn

private theorem lintegral_rpow_tsum_coe_enorm_sub_le_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h : ∀ n, ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p) :
    (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  suffices h_pow : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p by
      rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  have h_tsum_1 :
    ∀ g : ℕ → ℝ≥0∞, ∑' i, g i = atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), g i := by
    intro g
    rw [ENNReal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1]
  simp_rw [h_tsum_1 _]
  rw [← h_tsum_1]
  have h_liminf_pow :
    ∫⁻ a, (atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ =
      ∫⁻ a, atTop.liminf fun n => (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (zero_lt_one.trans_le hp1)
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_liminf_pow]
  refine (lintegral_liminf_le' fun n ↦ ?_).trans <| liminf_le_of_frequently_le' <| .of_forall h
  exact ((Finset.range _).aemeasurable_fun_sum fun i _ ↦ ((hf _).sub (hf i)).enorm).pow_const _

private theorem tsum_enorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i) :
    ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  have h_integral : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ < ∞ := by
    have h_tsum_lt_top : (∑' i, B i) ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_pos.le hB
    refine lt_of_le_of_lt ?_ h_tsum_lt_top
    rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv] at h
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖ₑ) ^ p < ∞ := by
    refine ae_lt_top' (AEMeasurable.pow_const ?_ _) h_integral.ne
    exact AEMeasurable.ennreal_tsum fun n => ((hf (n + 1)).sub (hf n)).enorm
  refine rpow_ae_lt_top.mono fun x hx => ?_
  rwa [← ENNReal.lt_rpow_inv_iff hp_pos,
    ENNReal.top_rpow_of_pos (by simp [hp_pos] : 0 < p⁻¹)] at hx

theorem ae_tendsto_of_cauchy_eLpNorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  have h_summable : ∀ᵐ x ∂μ, Summable fun i : ℕ => f (i + 1) x - f i x := by
    have h1 :
      ∀ n, eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
      eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' hf hp1 h_cau
    have h2 n :
        ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p :=
      lintegral_rpow_sum_enorm_sub_le_rpow_tsum hp1 n (h1 n)
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
      lintegral_rpow_tsum_coe_enorm_sub_le_tsum hf hp1 h2
    have h4 : ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ :=
      tsum_enorm_sub_ae_lt_top hf hp1 hB h3
    exact h4.mono fun x hx => .of_nnnorm <| ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne
  have h :
    ∀ᵐ x ∂μ, ∃ l : E,
      atTop.Tendsto (fun n => ∑ i ∈ Finset.range n, (f (i + 1) x - f i x)) (𝓝 l) := by
    refine h_summable.mono fun x hx => ?_
    let hx_sum := hx.hasSum.tendsto_sum_nat
    exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩
  refine h.mono fun x hx => ?_
  obtain ⟨l, hx⟩ := hx
  have h_rw_sum :
      (fun n => ∑ i ∈ Finset.range n, (f (i + 1) x - f i x)) = fun n => f n x - f 0 x := by
    ext1 n
    change
      (∑ i ∈ Finset.range n, ((fun m => f m x) (i + 1) - (fun m => f m x) i)) = f n x - f 0 x
    rw [Finset.sum_range_sub (fun m => f m x)]
  rw [h_rw_sum] at hx
  have hf_rw : (fun n => f n x) = fun n => f n x - f 0 x + f 0 x := by
    ext1 n
    abel
  rw [hf_rw]
  exact ⟨l + f 0 x, Tendsto.add_const _ hx⟩

theorem ae_tendsto_of_cauchy_eLpNorm [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top] at *
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → ‖(f n - f m) x‖ₑ < B N := by
      simp_rw [ae_all_iff]
      exact fun N n m hnN hmN => ae_lt_of_essSup_lt (h_cau N n m hnN hmN)
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup] at h_cau
    refine h_cau_ae.mono fun x hx => cauchySeq_tendsto_of_complete ?_
    refine cauchySeq_of_le_tendsto_0 (fun n => (B n).toReal) ?_ ?_
    · intro n m N hnN hmN
      specialize hx N n m hnN hmN
      rw [_root_.dist_eq_norm,
        ← ENNReal.ofReal_le_iff_le_toReal (ne_top_of_tsum_ne_top hB N),
        ofReal_norm_eq_enorm]
      exact hx.le
    · rw [← ENNReal.toReal_zero]
      exact
        Tendsto.comp (g := ENNReal.toReal) (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
          (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)
  have hp1 : 1 ≤ p.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hp_top, ENNReal.ofReal_one]
    exact hp
  have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p.toReal μ < B N := by
    intro N n m hn hm
    specialize h_cau N n m hn hm
    rwa [eLpNorm_eq_eLpNorm' (zero_lt_one.trans_le hp).ne.symm hp_top] at h_cau
  exact ae_tendsto_of_cauchy_eLpNorm' hf hp1 hB h_cau'

theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (f_lim : α → E) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have h_B : ∃ N : ℕ, B N ≤ ε := by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε from
      ⟨h_tendsto_zero.choose, h_tendsto_zero.choose_spec _ le_rfl⟩
    exact (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  obtain ⟨N, h_B⟩ := h_B
  refine ⟨N, fun n hn => ?_⟩
  have h_sub : eLpNorm (f n - f_lim) p μ ≤ atTop.liminf fun m => eLpNorm (f n - f m) p μ := by
    refine eLpNorm_lim_le_liminf_eLpNorm (fun m => (hf n).sub (hf m)) (f n - f_lim) ?_
    refine h_lim.mono fun x hx => ?_
    simp_rw [sub_eq_add_neg]
    exact Tendsto.add tendsto_const_nhds (Tendsto.neg hx)
  refine h_sub.trans ?_
  refine liminf_le_of_frequently_le' (frequently_atTop.mpr ?_)
  refine fun N1 => ⟨max N N1, le_max_right _ _, ?_⟩
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B

theorem memLp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, MemLp (f n) p μ)
    (f_lim : α → E) (h_lim_meas : AEStronglyMeasurable f_lim μ)
    (h_tendsto : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) : MemLp f_lim p μ := by
  refine ⟨h_lim_meas, ?_⟩
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  obtain ⟨N, h_tendsto_1⟩ := h_tendsto 1 zero_lt_one
  specialize h_tendsto_1 N (le_refl N)
  have h_add : f_lim = f_lim - f N + f N := by abel
  rw [h_add]
  refine lt_of_le_of_lt (eLpNorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) ?_
  rw [ENNReal.add_lt_top]
  constructor
  · refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
    have h_neg : f_lim - f N = -(f N - f_lim) := by simp
    rwa [h_neg, eLpNorm_neg]
  · exact (hf N).2

theorem cauchy_complete_eLpNorm [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
      ∃ f_lim : α → E, StronglyMeasurable f_lim ∧
        ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) :=
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => (hf n).1)
      (ae_tendsto_of_cauchy_eLpNorm (fun n => (hf n).1) hp hB h_cau)
  have h_tendsto' : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) :=
    cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim
  have h_ℒp_lim : MemLp f_lim p μ :=
    memLp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.aestronglyMeasurable h_tendsto'
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩

/-- `Lp` is complete for `1 ≤ p`. -/
instance instCompleteSpace [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ) :=
  completeSpace_lp_of_cauchy_complete_eLpNorm fun _f hf _B hB h_cau =>
    cauchy_complete_eLpNorm hp.elim hf hB.ne h_cau

end MeasureTheory.Lp
