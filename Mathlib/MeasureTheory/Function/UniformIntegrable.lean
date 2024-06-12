/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space

#align_import measure_theory.function.uniform_integrable from "leanprover-community/mathlib"@"57ac39bd365c2f80589a700f9fbb664d3a1a30c2"

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which establishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales most notably is used to
formulate the martingale convergence theorem.

## Main definitions

* `MeasureTheory.UnifIntegrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted `s` is smaller than `ε` for all `i`.
* `MeasureTheory.UniformIntegrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

# Main results

* `MeasureTheory.unifIntegrable_finite`: a finite sequence of Lp functions is uniformly
  integrable.
* `MeasureTheory.tendsto_Lp_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniform integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted on `s` is less than `ε`.

Uniform integrability is also known as uniformly absolutely continuous integrals. -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ⦄ (_ : 0 < ε), ∃ (δ : ℝ) (_ : 0 < δ), ∀ i s,
    MeasurableSet s → μ s ≤ ENNReal.ofReal δ → snorm (s.indicator (f i)) p μ ≤ ENNReal.ofReal ε
#align measure_theory.unif_integrable MeasureTheory.UnifIntegrable

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, snorm (f i) p μ ≤ C
#align measure_theory.uniform_integrable MeasureTheory.UniformIntegrable

namespace UniformIntegrable

protected theorem aeStronglyMeasurable {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ)
    (i : ι) : AEStronglyMeasurable (f i) μ :=
  hf.1 i
#align measure_theory.uniform_integrable.ae_strongly_measurable MeasureTheory.UniformIntegrable.aeStronglyMeasurable

protected theorem unifIntegrable {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ) :
    UnifIntegrable f p μ :=
  hf.2.1
#align measure_theory.uniform_integrable.unif_integrable MeasureTheory.UniformIntegrable.unifIntegrable

protected theorem memℒp {f : ι → α → β} {p : ℝ≥0∞} (hf : UniformIntegrable f p μ) (i : ι) :
    Memℒp (f i) p μ :=
  ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) ENNReal.coe_lt_top⟩
#align measure_theory.uniform_integrable.mem_ℒp MeasureTheory.UniformIntegrable.memℒp

end UniformIntegrable

section UnifIntegrable

/-! ### `UnifIntegrable`

This section deals with uniform integrability in the measure theory sense. -/


namespace UnifIntegrable

variable {f g : ι → α → β} {p : ℝ≥0∞}

protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f + g) p μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁, hδ₁_pos, hfδ₁⟩ := hf hε2
  obtain ⟨δ₂, hδ₂_pos, hgδ₂⟩ := hg hε2
  refine ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun i s hs hμs => ?_⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine (snorm_add_le ((hf_meas i).indicator hs) ((hg_meas i).indicator hs) hp).trans ?_
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  rw [hε_halves]
  exact add_le_add (hfδ₁ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    (hgδ₂ i s hs (hμs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))))
#align measure_theory.unif_integrable.add MeasureTheory.UnifIntegrable.add

protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  simp_rw [UnifIntegrable, Pi.neg_apply, Set.indicator_neg', snorm_neg]
  exact hf
#align measure_theory.unif_integrable.neg MeasureTheory.UnifIntegrable.neg

protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg
#align measure_theory.unif_integrable.sub MeasureTheory.UnifIntegrable.sub

protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifIntegrable g p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hfδ⟩ := hf hε
  refine ⟨δ, hδ_pos, fun n s hs hμs => (le_of_eq <| snorm_congr_ae ?_).trans (hfδ n s hs hμs)⟩
  filter_upwards [hfg n] with x hx
  simp_rw [Set.indicator_apply, hx]
#align measure_theory.unif_integrable.ae_eq MeasureTheory.UnifIntegrable.ae_eq

end UnifIntegrable

theorem unifIntegrable_zero_meas [MeasurableSpace α] {p : ℝ≥0∞} {f : ι → α → β} :
    UnifIntegrable f p (0 : Measure α) :=
  fun ε _ => ⟨1, one_pos, fun i s _ _ => by simp⟩
#align measure_theory.unif_integrable_zero_meas MeasureTheory.unifIntegrable_zero_meas

theorem unifIntegrable_congr_ae {p : ℝ≥0∞} {f g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩
#align measure_theory.unif_integrable_congr_ae MeasureTheory.unifIntegrable_congr_ae

theorem tendsto_indicator_ge (f : α → β) (x : α) :
    Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : ℝ) + 1) fun n hn => ?_
  rw [Set.indicator_of_not_mem]
  simp only [not_le, Set.mem_setOf_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast
#align measure_theory.tendsto_indicator_ge MeasureTheory.tendsto_indicator_ge

variable {p : ℝ≥0∞}

section

variable {f : α → β}

/-- This lemma is weaker than `MeasureTheory.Memℒp.integral_indicator_norm_ge_nonneg_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`. -/
theorem Memℒp.integral_indicator_norm_ge_le (hf : Memℒp f 1 μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ENNReal.ofReal ε := by
  have htendsto :
      ∀ᵐ x ∂μ, Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable ({ x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memℒp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖{ x | n ≤ ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    refine fun n => univ_mem' (id fun x => ?_)
    by_cases hx : (n : ℝ) ≤ ‖f x‖
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_not_mem, norm_zero]
      · exact norm_nonneg _
      · assumption
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [true_and_iff, ge_iff_le, zero_tsub, zero_le, sub_zero, zero_add, coe_nnnorm,
    Set.mem_Icc] at hM
  refine ⟨M, ?_⟩
  convert hM M le_rfl
  simp only [coe_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl
#align measure_theory.mem_ℒp.integral_indicator_norm_ge_le MeasureTheory.Memℒp.integral_indicator_norm_ge_le

/-- This lemma is superceded by `MeasureTheory.Memℒp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability. -/
theorem Memℒp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : Memℒp f 1 μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ENNReal.ofReal ε :=
  let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩
#align measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le_of_meas MeasureTheory.Memℒp.integral_indicator_norm_ge_nonneg_le_of_meas

theorem Memℒp.integral_indicator_norm_ge_nonneg_le (hf : Memℒp f 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ENNReal.ofReal ε := by
  have hf_mk : Memℒp (hf.1.mk f) 1 μ := (memℒp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_setOf_eq, ENNReal.coe_inj, hx.symm]
#align measure_theory.mem_ℒp.integral_indicator_norm_ge_nonneg_le MeasureTheory.Memℒp.integral_indicator_norm_ge_nonneg_le

theorem Memℒp.snormEssSup_indicator_norm_ge_eq_zero (hf : Memℒp f ∞ μ)
    (hmeas : StronglyMeasurable f) :
    ∃ M : ℝ, snormEssSup ({ x | M ≤ ‖f x‖₊ }.indicator f) μ = 0 := by
  have hbdd : snormEssSup f μ < ∞ := hf.snorm_lt_top
  refine ⟨(snorm f ∞ μ + 1).toReal, ?_⟩
  rw [snormEssSup_indicator_eq_snormEssSup_restrict]
  · have : μ.restrict { x : α | (snorm f ⊤ μ + 1).toReal ≤ ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, snorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (snormEssSup f μ + 1).toReal ≤ ‖f x‖ } ⊆
          { x : α | snormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_setOf_eq, ← ENNReal.toReal_lt_toReal hbdd.ne ENNReal.coe_lt_top.ne,
          ENNReal.coe_toReal, coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [ENNReal.toReal_lt_toReal hbdd.ne]
        · exact ENNReal.lt_add_right hbdd.ne one_ne_zero
        · exact (ENNReal.add_lt_top.2 ⟨hbdd, ENNReal.one_lt_top⟩).ne
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := coe_nnnorm_ae_le_snormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this, snormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe
#align measure_theory.mem_ℒp.snorm_ess_sup_indicator_norm_ge_eq_zero MeasureTheory.Memℒp.snormEssSup_indicator_norm_ge_eq_zero

/- This lemma is slightly weaker than `MeasureTheory.Memℒp.snorm_indicator_norm_ge_pos_le` as the
latter provides `0 < M`. -/
theorem Memℒp.snorm_indicator_norm_ge_le (hf : Memℒp f p μ) (hmeas : StronglyMeasurable f) {ε : ℝ}
    (hε : 0 < ε) : ∃ M : ℝ, snorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ENNReal.ofReal ε := by
  by_cases hp_ne_zero : p = 0
  · refine ⟨1, hp_ne_zero.symm ▸ ?_⟩
    simp [snorm_exponent_zero]
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.snormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [snorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := Memℒp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top, ← ENNReal.rpow_one (ENNReal.ofReal ε)]
  conv_rhs => rw [← mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
  rw [ENNReal.rpow_mul,
    ENNReal.rpow_le_rpow_iff (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top),
    ENNReal.ofReal_rpow_of_pos hε]
  convert hM
  rename_i x
  rw [ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg, nnnorm_indicator_eq_indicator_nnnorm,
    nnnorm_indicator_eq_indicator_nnnorm]
  have hiff : M ^ (1 / p.toReal) ≤ ‖f x‖₊ ↔ M ≤ ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm, coe_nnnorm, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
      ← Real.rpow_le_rpow_iff hM' (Real.rpow_nonneg (norm_nonneg _) _)
        (one_div_pos.2 <| ENNReal.toReal_pos hp_ne_zero hp_ne_top), ← Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel (ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm, Real.rpow_one]
  by_cases hx : x ∈ { x : α | M ^ (1 / p.toReal) ≤ ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.nnnorm_of_nonneg]
    · rfl
    rw [Set.mem_setOf_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem]
    · simp [(ENNReal.toReal_pos hp_ne_zero hp_ne_top).ne.symm]
    · rw [Set.mem_setOf_eq]
      rwa [← hiff]
#align measure_theory.mem_ℒp.snorm_indicator_norm_ge_le MeasureTheory.Memℒp.snorm_indicator_norm_ge_le

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
theorem Memℒp.snorm_indicator_norm_ge_pos_le (hf : Memℒp f p μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ snorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨M, hM⟩ := hf.snorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (snorm_mono fun x => ?_) hM⟩
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  refine Set.indicator_le_indicator_of_subset (fun x hx => ?_) (fun x => norm_nonneg (f x)) x
  rw [Set.mem_setOf_eq] at hx -- removing the `rw` breaks the proof!
  exact (max_le_iff.1 hx).1
#align measure_theory.mem_ℒp.snorm_indicator_norm_ge_pos_le MeasureTheory.Memℒp.snorm_indicator_norm_ge_pos_le

end

theorem snorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) {M : ℝ}
    (hf : ∀ x, ‖f x‖ < M) :
    ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s,
      MeasurableSet s → μ s ≤ ENNReal.ofReal δ → snorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  by_cases hM : M ≤ 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp [hε.le]
    · ext x
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  rw [not_le] at hM
  refine ⟨(ε / M) ^ p.toReal, Real.rpow_pos_of_pos (div_pos hε hM) _, fun s hs hμ => ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [snorm_indicator_eq_snorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ M := by
    filter_upwards
    exact fun x => (hf x).le
  refine le_trans (snorm_le_of_ae_bound haebdd) ?_
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ← ENNReal.le_div_iff_mul_le (Or.inl _) (Or.inl ENNReal.ofReal_ne_top)]
  · rw [← one_div, ENNReal.rpow_one_div_le_iff (ENNReal.toReal_pos hp hp_top)]
    refine le_trans hμ ?_
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hε hM),
      ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp hp_top), ENNReal.ofReal_div_of_pos hM]
  · simpa only [ENNReal.ofReal_eq_zero, not_le, Ne]
#align measure_theory.snorm_indicator_le_of_bound MeasureTheory.snorm_indicator_le_of_bound

section

variable {f : α → β}

/-- Auxiliary lemma for `MeasureTheory.Memℒp.snorm_indicator_le`. -/
theorem Memℒp.snorm_indicator_le' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      snorm (s.indicator f) p μ ≤ 2 * ENNReal.ofReal ε := by
  obtain ⟨M, hMpos, hM⟩ := hf.snorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    snorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm, Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M ≤ ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [snorm_indicator_eq_snorm_restrict hs]
    refine le_trans (snorm_add_le ?_ ?_ hp_one) ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add (le_trans (snorm_mono_measure _ Measure.restrict_le_self) hM) ?_
      rw [← snorm_indicator_eq_snorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M ≤ ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_not_mem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_not_mem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx
#align measure_theory.mem_ℒp.snorm_indicator_le' MeasureTheory.Memℒp.snorm_indicator_le'

/-- This lemma is superceded by `MeasureTheory.Memℒp.snorm_indicator_le` which does not require
measurability on `f`. -/
theorem Memℒp.snorm_indicator_le_of_meas (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      snorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδpos, hδ⟩ := hf.snorm_indicator_le' hp_one hp_top hmeas (half_pos hε)
  refine ⟨δ, hδpos, fun s hs hμs => le_trans (hδ s hs hμs) ?_⟩
  rw [ENNReal.ofReal_div_of_pos zero_lt_two, (by norm_num : ENNReal.ofReal 2 = 2),
      ENNReal.mul_div_cancel'] <;>
    norm_num
#align measure_theory.mem_ℒp.snorm_indicator_le_of_meas MeasureTheory.Memℒp.snorm_indicator_le_of_meas

theorem Memℒp.snorm_indicator_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : Memℒp f p μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      snorm (s.indicator f) p μ ≤ ENNReal.ofReal ε := by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).snorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert hδ s hs hμs using 1
  rw [snorm_indicator_eq_snorm_restrict hs, snorm_indicator_eq_snorm_restrict hs]
  exact snorm_congr_ae heq.restrict
#align measure_theory.mem_ℒp.snorm_indicator_le MeasureTheory.Memℒp.snorm_indicator_le

/-- A constant function is uniformly integrable. -/
theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hgδ⟩ := hg.snorm_indicator_le hp hp_ne_top hε
  exact ⟨δ, hδ_pos, fun _ => hgδ⟩
#align measure_theory.unif_integrable_const MeasureTheory.unifIntegrable_const

/-- A single function is uniformly integrable. -/
theorem unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifIntegrable f p μ := by
  intro ε hε
  by_cases hι : Nonempty ι
  · cases' hι with i
    obtain ⟨δ, hδpos, hδ⟩ := (hf i).snorm_indicator_le hp_one hp_top hε
    refine ⟨δ, hδpos, fun j s hs hμs => ?_⟩
    convert hδ s hs hμs
  · exact ⟨1, zero_lt_one, fun i => False.elim <| hι <| Nonempty.intro i⟩
#align measure_theory.unif_integrable_subsingleton MeasureTheory.unifIntegrable_subsingleton

/-- This lemma is less general than `MeasureTheory.unifIntegrable_finite` which applies to
all sequences indexed by a finite type. -/
theorem unifIntegrable_fin (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifIntegrable f p μ := by
  revert f
  induction' n with n h
  · intro f hf
  -- Porting note (#10754): added this instance
    have : Subsingleton (Fin Nat.zero) := subsingleton_fin_zero
    exact unifIntegrable_subsingleton hp_one hp_top hf
  intro f hfLp ε hε
  let g : Fin n → α → β := fun k => f k
  have hgLp : ∀ i, Memℒp (g i) p μ := fun i => hfLp i
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := h hgLp hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := (hfLp n).snorm_indicator_le hp_one hp_top hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun i s hs hμs => ?_⟩
  by_cases hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · exact hδ₁ _ s hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_left _ _)
    · simp [g]
  · rw [(_ : i = n)]
    · exact hδ₂ _ hs (le_trans hμs <| ENNReal.ofReal_le_ofReal <| min_le_right _ _)
    · have hi' := Fin.is_lt i
      rw [Nat.lt_succ_iff] at hi'
      rw [not_lt] at hi
      simp [← le_antisymm hi' hi]
#align measure_theory.unif_integrable_fin MeasureTheory.unifIntegrable_fin

/-- A finite sequence of Lp functions is uniformly integrable. -/
theorem unifIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifIntegrable f p μ := by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  let g : Fin n → α → β := f ∘ hn.some.symm
  have hg : ∀ i, Memℒp (g i) p μ := fun _ => hf _
  obtain ⟨δ, hδpos, hδ⟩ := unifIntegrable_fin hp_one hp_top hg hε
  refine ⟨δ, hδpos, fun i s hs hμs => ?_⟩
  specialize hδ (hn.some i) s hs hμs
  simp_rw [g, Function.comp_apply, Equiv.symm_apply_apply] at hδ
  assumption
#align measure_theory.unif_integrable_finite MeasureTheory.unifIntegrable_finite

end

theorem snorm_sub_le_of_dist_bdd (μ : Measure α)
    {p : ℝ≥0∞} (hp' : p ≠ ∞) {s : Set α} (hs : MeasurableSet[m] s)
    {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
    snorm (s.indicator (f - g)) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x, ‖s.indicator (f - g) x‖ ≤ ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exact hf x hx
    · simp [Set.indicator_of_not_mem hx]
  refine le_trans (snorm_mono this) ?_
  rw [snorm_indicator_const hs hp hp']
  refine mul_le_mul_right' (le_of_eq ?_) _
  rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc]
#align measure_theory.snorm_sub_le_of_dist_bdd MeasureTheory.snorm_sub_le_of_dist_bdd

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases h : ε < ∞; swap
  · rw [not_lt, top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε.toReal / 3 :=
    div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (by norm_num)
  have hdivp : 0 ≤ 1 / p.toReal := by
    refine one_div_nonneg.2 ?_
    rw [← ENNReal.zero_toReal, ENNReal.toReal_le_toReal ENNReal.zero_ne_top hp']
    exact le_trans (zero_le _) hp
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, hsnorm₁⟩ := hui hε'
  obtain ⟨δ₂, hδ₂, hsnorm₂⟩ := hg'.snorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (ENNReal.toReal_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by norm_num) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  refine le_trans (snorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp) ?_
  rw [sub_eq_add_neg, Set.indicator_add' t, Set.indicator_neg']
  refine le_trans (add_le_add_right (snorm_add_le ((hf n).indicator htm).aestronglyMeasurable
    (hg.indicator htm).neg.aestronglyMeasurable hp) _) ?_
  have hnf : snorm (t.indicator (f n)) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    refine hsnorm₁ n t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₁.le]
    exact min_le_left _ _
  have hng : snorm (t.indicator g) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    refine hsnorm₂ t htm (le_trans ht₁ ?_)
    rw [ENNReal.ofReal_le_ofReal_iff hδ₂.le]
    exact min_le_right _ _
  have hlt : snorm (tᶜ.indicator (f n - g)) p μ ≤ ENNReal.ofReal (ε.toReal / 3) := by
    specialize hN n hn
    have : 0 ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have := snorm_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine le_trans this ?_
    rw [div_mul_eq_div_mul_one_div, ← ENNReal.ofReal_toReal (measure_lt_top μ tᶜ).ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hdivp, ← ENNReal.ofReal_mul, mul_assoc]
    · refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hε'.le ?_)
      rw [mul_comm, mul_one_div, div_le_one]
      · refine Real.rpow_le_rpow ENNReal.toReal_nonneg
          (ENNReal.toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_) hdivp
        rw [ENNReal.ofReal_coe_nnreal, coe_measureUnivNNReal]
        exact measure_mono (Set.subset_univ _)
      · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
    · positivity
  have : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 3 by norm_num), ENNReal.ofReal_toReal h.ne]
    simp
  rw [this] at hnf hng hlt
  rw [snorm_neg, ← ENNReal.add_thirds ε, ← sub_eq_add_neg]
  exact add_le_add_three hnf hng hlt
set_option linter.uppercaseLean3 false in
#align measure_theory.tendsto_Lp_of_tendsto_ae_of_meas MeasureTheory.tendsto_Lp_of_tendsto_ae_of_meas

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β}
    {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Memℒp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  have : ∀ n, snorm (f n - g) p μ = snorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => snorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm
set_option linter.uppercaseLean3 false in
#align measure_theory.tendsto_Lp_of_tendsto_ae MeasureTheory.tendsto_Lp_of_tendsto_ae

variable {f : ℕ → α → β} {g : α → β}

theorem unifIntegrable_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => snorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa)
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, Memℒp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_fin hp hp' hF hε
  refine ⟨δ₁, hδpos₁, fun n s hs hμs => ?_⟩
  by_cases hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hs hμs
  · exact (snorm_indicator_le _).trans (hN n (not_lt.1 hn))
set_option linter.uppercaseLean3 false in
#align measure_theory.unif_integrable_of_tendsto_Lp_zero MeasureTheory.unifIntegrable_of_tendsto_Lp_zero

/-- Convergence in Lp implies uniform integrability. -/
theorem unifIntegrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hg : Memℒp g p μ) (hfg : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg
set_option linter.uppercaseLean3 false in
#align measure_theory.unif_integrable_of_tendsto_Lp MeasureTheory.unifIntegrable_of_tendsto_Lp

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
theorem tendsto_Lp_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Memℒp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg (fun ε hε =>
      let ⟨δ, hδ, hδ'⟩ := hui hε
      ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      hms'⟩
set_option linter.uppercaseLean3 false in
#align measure_theory.tendsto_Lp_of_tendsto_in_measure MeasureTheory.tendsto_Lp_of_tendstoInMeasure

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
theorem tendstoInMeasure_iff_tendsto_Lp [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_snorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩
set_option linter.uppercaseLean3 false in
#align measure_theory.tendsto_in_measure_iff_tendsto_Lp MeasureTheory.tendstoInMeasure_iff_tendsto_Lp

/-- This lemma is superceded by `unifIntegrable_of` which do not require `C` to be positive. -/
theorem unifIntegrable_of' (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne.symm
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (half_pos hε)
  refine ⟨(ε / (2 * C)) ^ ENNReal.toReal p,
    Real.rpow_pos_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos))) _,
    fun i s hs hμs => ?_⟩
  by_cases hμs' : μ s = 0
  · rw [(snorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    set_option tactic.skipAssignedInstances false in norm_num
  calc
    snorm (Set.indicator s (f i)) p μ ≤
        snorm (Set.indicator (s ∩ { x | C ≤ ‖f i x‖₊ }) (f i)) p μ +
          snorm (Set.indicator (s ∩ { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (snorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s ∩ { x : α | C ≤ ‖f i x‖₊ }).indicator (f i) x +
        (s ∩ { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_lt] :
            { x : α | C ≤ ‖f i x‖₊ } ∪ { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_setOf_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ ≤ snorm (Set.indicator { x | C ≤ ‖f i x‖₊ } (f i)) p μ +
        (C : ℝ≥0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (snorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [snorm_indicator_eq_snorm_restrict hs]
      have : ∀ᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ ≤ C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (snorm_le_of_ae_bound this) ?_
      rw [mul_comm, Measure.restrict_apply' hs, Set.univ_inter, ENNReal.ofReal_coe_nnreal, one_div]
    _ ≤ ENNReal.ofReal (ε / 2) + C * ENNReal.ofReal (ε / (2 * C)) := by
      refine add_le_add (hC i) (mul_le_mul_left' ?_ _)
      rwa [ENNReal.rpow_one_div_le_iff (ENNReal.toReal_pos hpzero hp'),
        ENNReal.ofReal_rpow_of_pos (div_pos hε (mul_pos two_pos (NNReal.coe_pos.2 hCpos)))]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
      refine add_le_add_left ?_ _
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← div_div,
        mul_div_cancel₀ _ (NNReal.coe_pos.2 hCpos).ne.symm]
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
#align measure_theory.unif_integrable_of' MeasureTheory.unifIntegrable_of'

theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UnifIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : ∀ i, snorm ({ x | C ≤ ‖g i x‖₊ }.indicator (g i)) p μ ≤ ENNReal.ofReal ε := by
    intro i
    refine le_trans (le_of_eq <| snorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_setOf, hx] at hfx
    · rw [Set.indicator_of_not_mem hfx, Set.indicator_of_not_mem]
      rwa [Set.mem_setOf, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (snorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  exact Set.indicator_le_indicator_of_subset
    (fun x hx => Set.mem_setOf_eq ▸ le_trans (le_max_left _ _) hx) (fun _ => norm_nonneg _) _
#align measure_theory.unif_integrable_of MeasureTheory.unifIntegrable_of

end UnifIntegrable

section UniformIntegrable

/-! `UniformIntegrable`

In probability theory, uniform integrability normally refers to the condition that a sequence
of function `(fₙ)` satisfies for all `ε > 0`, there exists some `C ≥ 0` such that
`∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`.

In this section, we will develop some API for `UniformIntegrable` and prove that
`UniformIntegrable` is equivalent to this definition of uniform integrability.
-/


variable {p : ℝ≥0∞} {f : ι → α → β}

theorem uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0 : Measure α) :=
  ⟨fun _ => aestronglyMeasurable_zero_measure _, unifIntegrable_zero_meas, 0,
    fun _ => snorm_measure_zero.le⟩
#align measure_theory.uniform_integrable_zero_meas MeasureTheory.uniformIntegrable_zero_meas

theorem UniformIntegrable.ae_eq {g : ι → α → β} (hf : UniformIntegrable f p μ)
    (hfg : ∀ n, f n =ᵐ[μ] g n) : UniformIntegrable g p μ := by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← snorm_congr_ae (hfg i)]
  exact hC i
#align measure_theory.uniform_integrable.ae_eq MeasureTheory.UniformIntegrable.ae_eq

theorem uniformIntegrable_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩
#align measure_theory.uniform_integrable_congr_ae MeasureTheory.uniformIntegrable_congr_ae

/-- A finite sequence of Lp functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, Memℒp (f i) p μ) : UniformIntegrable f p μ := by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => snorm (f i) p μ).max'
      ⟨snorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal]
    · exact Finset.le_max' (α := ℝ≥0∞) _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    · refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
      rw [Finset.mem_image] at hy
      obtain ⟨i, -, rfl⟩ := hy
      exact hf i
  · exact ⟨0, fun i => False.elim <| hι <| Nonempty.intro i⟩
#align measure_theory.uniform_integrable_finite MeasureTheory.uniformIntegrable_finite

/-- A single function is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, Memℒp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp_one hp_top hf
#align measure_theory.uniform_integrable_subsingleton MeasureTheory.uniformIntegrable_subsingleton

/-- A constant sequence of functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  ⟨fun _ => hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(snorm g p μ).toNNReal, fun _ => le_of_eq (ENNReal.coe_toNNReal hg.2.ne).symm⟩⟩
#align measure_theory.uniform_integrable_const MeasureTheory.uniformIntegrable_const

/-- This lemma is superceded by `uniformIntegrable_of` which only requires
`AEStronglyMeasurable`. -/
theorem uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    snorm (f i) p μ ≤
        snorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          snorm ({ x : α | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (snorm_mono fun x => ?_) (snorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply, Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_not_mem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ ≤ (C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : ∀ᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ ≤ C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (snorm_le_of_ae_bound this) ?_) (ENNReal.ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ENNReal.ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : ℝ≥0∞).toNNReal := by
      rw [ENNReal.coe_toNNReal]
      exact ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg
          (inv_nonneg.2 ENNReal.toReal_nonneg) (measure_lt_top _ _).ne),
        ENNReal.one_ne_top⟩
#align measure_theory.uniform_integrable_of' MeasureTheory.uniformIntegrable_of'

/-- A sequence of functions `(fₙ)` is uniformly integrable in the probability sense if for all
`ε > 0`, there exists some `C` such that `∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`. -/
theorem uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
      ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) :
    UniformIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| snorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_setOf, hx] at hfx
  · rw [Set.indicator_of_not_mem hfx, Set.indicator_of_not_mem]
    rwa [Set.mem_setOf, hx] at hfx
#align measure_theory.uniform_integrable_of MeasureTheory.uniformIntegrable_of

/-- This lemma is superceded by `UniformIntegrable.spec` which does not require measurability. -/
theorem UniformIntegrable.spec' (hp : p ≠ 0) (hp' : p ≠ ∞) (hf : ∀ i, StronglyMeasurable (f i))
    (hfu : UniformIntegrable f p μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε := by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := hfu hε
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ i, μ { x | C ≤ ‖f i x‖₊ } ≤ ENNReal.ofReal δ := by
    by_contra hcon; push_neg at hcon
    choose ℐ hℐ using hcon
    lift δ to ℝ≥0 using hδpos.le
    have : ∀ C : ℝ≥0, C • (δ : ℝ≥0∞) ^ (1 / p.toReal) ≤ snorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : ℝ≥0∞) ^ (1 / p.toReal) ≤ C • μ { x | C ≤ ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
          simp_rw [ENNReal.ofReal_coe_nnreal] at hℐ
          refine mul_le_mul' le_rfl
            (ENNReal.rpow_le_rpow (hℐ C).le (one_div_nonneg.2 ENNReal.toReal_nonneg))
        _ ≤ snorm ({ x | C ≤ ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine snorm_indicator_ge_of_bdd_below hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (eventually_of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ ≤ snorm (f (ℐ C)) p μ := snorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal))
    rw [ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.coe_smul,
      smul_eq_mul, mul_assoc, NNReal.inv_rpow,
      inv_mul_cancel (NNReal.rpow_pos (NNReal.coe_pos.1 hδpos)).ne.symm, mul_one, ENNReal.coe_mul,
      ← NNReal.inv_rpow] at this
    refine (lt_of_le_of_lt (le_trans
      (hM <| ℐ <| 2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)) (le_max_left (M : ℝ≥0∞) 1))
        (lt_of_lt_of_le ?_ this)).ne rfl
    rw [← ENNReal.coe_one, ← ENNReal.coe_max, ← ENNReal.coe_mul, ENNReal.coe_lt_coe]
    exact lt_two_mul_self (lt_max_of_lt_right one_pos)
  exact ⟨C, fun i => hδ i _ (measurableSet_le measurable_const (hf i).nnnorm.measurable) (hC i)⟩
#align measure_theory.uniform_integrable.spec' MeasureTheory.UniformIntegrable.spec'

theorem UniformIntegrable.spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε := by
  set g : ι → α → β := fun i => (hfu.1 i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| snorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_setOf, hx] at hfx
  · rw [Set.indicator_of_not_mem hfx, Set.indicator_of_not_mem]
    rwa [Set.mem_setOf, hx] at hfx
#align measure_theory.uniform_integrable.spec MeasureTheory.UniformIntegrable.spec

/-- The definition of uniform integrable in mathlib is equivalent to the definition commonly
found in literature. -/
theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    UniformIntegrable f p μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
          ∀ i, snorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε :=
  ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne.symm hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩
#align measure_theory.uniform_integrable_iff MeasureTheory.uniformIntegrable_iff

/-- The averaging of a uniformly integrable sequence is also uniformly integrable. -/
theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, f i)) p μ := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n => ?_, fun ε hε => ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum' _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := hf₂ hε
    refine ⟨δ, hδ₁, fun n s hs hle => ?_⟩
    simp_rw [Finset.smul_sum, Finset.indicator_sum]
    refine le_trans (snorm_sum_le (fun i _ => ((hf₁ i).const_smul _).indicator hs) hp) ?_
    have : ∀ i, s.indicator ((n : ℝ) ⁻¹ • f i) = (↑n : ℝ)⁻¹ • s.indicator (f i) :=
      fun i ↦ indicator_const_smul _ _ _
    simp_rw [this, snorm_const_smul, ← Finset.mul_sum, nnnorm_inv, Real.nnnorm_natCast]
    by_cases hn : (↑(↑n : ℝ≥0)⁻¹ : ℝ≥0∞) = 0
    · simp only [hn, zero_mul, zero_le]
    refine le_trans ?_ (?_ : ↑(↑n : ℝ≥0)⁻¹ * n • ENNReal.ofReal ε ≤ ENNReal.ofReal ε)
    · refine (ENNReal.mul_le_mul_left hn ENNReal.coe_ne_top).2 ?_
      conv_rhs => rw [← Finset.card_range n]
      exact Finset.sum_le_card_nsmul _ _ _ fun i _ => hδ₂ _ _ hs hle
    · simp only [ENNReal.coe_eq_zero, inv_eq_zero, Nat.cast_eq_zero] at hn
      rw [nsmul_eq_mul, ← mul_assoc, ENNReal.coe_inv, ENNReal.coe_natCast,
        ENNReal.inv_mul_cancel _ (ENNReal.natCast_ne_top _), one_mul]
      all_goals simpa only [Ne, Nat.cast_eq_zero]
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (snorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    simp_rw [snorm_const_smul, ← Finset.mul_sum, nnnorm_inv, Real.nnnorm_natCast]
    by_cases hn : (↑(↑n : ℝ≥0)⁻¹ : ℝ≥0∞) = 0
    · simp only [hn, zero_mul, zero_le]
    refine le_trans ?_ (?_ : ↑(↑n : ℝ≥0)⁻¹ * (n • C : ℝ≥0∞) ≤ C)
    · refine (ENNReal.mul_le_mul_left hn ENNReal.coe_ne_top).2 ?_
      conv_rhs => rw [← Finset.card_range n]
      exact Finset.sum_le_card_nsmul _ _ _ fun i _ => hC i
    · simp only [ENNReal.coe_eq_zero, inv_eq_zero, Nat.cast_eq_zero] at hn
      rw [nsmul_eq_mul, ← mul_assoc, ENNReal.coe_inv, ENNReal.coe_natCast,
        ENNReal.inv_mul_cancel _ (ENNReal.natCast_ne_top _), one_mul]
      all_goals simpa only [Ne, Nat.cast_eq_zero]

/-- The averaging of a uniformly integrable real-valued sequence is also uniformly integrable. -/
theorem uniformIntegrable_average_real (hp : 1 ≤ p) {f : ℕ → α → ℝ} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i ∈ Finset.range n, f i) / (n : α → ℝ)) p μ := by
  convert uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]
#align measure_theory.uniform_integrable_average MeasureTheory.uniformIntegrable_average_real

end UniformIntegrable

end MeasureTheory
