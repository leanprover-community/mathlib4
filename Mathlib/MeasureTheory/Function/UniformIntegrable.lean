/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Uniform integrability

This file contains the definitions for uniform integrability (both in the measure theory sense
as well as the probability theory sense). This file also contains the Vitali convergence theorem
which establishes a relation between uniform integrability, convergence in measure and
Lp convergence.

Uniform integrability plays a vital role in the theory of martingales and most notably is used to
formulate the martingale convergence theorem.

## Main definitions

* `MeasureTheory.UnifIntegrable`: uniform integrability in the measure theory sense.
  In particular, a sequence of functions `f` is uniformly integrable if for all `ε > 0`, there
  exists some `δ > 0` such that for all sets `s` of smaller measure than `δ`, the Lp-norm of
  `f i` restricted to `s` is smaller than `ε` for all `i`.
* `MeasureTheory.UniformIntegrable`: uniform integrability in the probability theory sense.
  In particular, a sequence of measurable functions `f` is uniformly integrable in the
  probability theory sense if it is uniformly integrable in the measure theory sense and
  has uniformly bounded Lp-norm.

## Main results

* `MeasureTheory.unifIntegrable_finite`: a finite sequence of Lp functions is uniformly
  integrable.
* `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable converges in Lp if they converge almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable
  and converges in measure.

## Tags
uniformly integrable, uniformly absolutely continuous integral, Vitali convergence theorem
-/

@[expose] public section


noncomputable section

open scoped NNReal Topology

namespace MeasureTheory

open ENNReal Filter Set

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {f g : ι → α → β} {p : ℝ≥0∞}

/-- Uniform integrability in the measure theory sense.

A sequence of functions `f` is said to be uniformly integrable if for all `ε > 0`, there exists
some `δ > 0` such that for all sets `s` with measure less than `δ`, the Lp-norm of `f i`
restricted to `s` is less than `ε`.

Uniform integrability is also known as uniformly absolutely continuous integrals. -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  Tendsto (fun ε ↦ ⨆ (i : ι) (s : Set α) (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) (𝓝 0) (𝓝 0)

/-- In probability theory, a family of measurable functions is uniformly integrable if it is
uniformly integrable in the measure theory sense and is uniformly bounded. -/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  (∀ i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) p μ ≤ C

/-- A characterization of `UnifIntegrable` families. This version does not assume that the sets `s`
are measurable, and is convenient for applying the hypothesis that a family is `UnifIntegrable`.
See `unifIntegrable_iff'` for a version where the sets `s` are assumed measurable. -/
theorem unifIntegrable_iff :
  UnifIntegrable f p μ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  rw [UnifIntegrable, ENNReal.tendsto_nhds_zero]
  apply forall₂_congr fun ε hε ↦ ?_
  rw [nhds_zero_basis_Iic.eventually_iff]
  apply exists_congr fun δ ↦ and_congr_right fun hδ ↦ ?_
  simp only [mem_Iic, iSup_le_iff]
  exact ⟨fun h ↦ h (le_refl δ), fun h x hx i s hs ↦ h i s (hs.trans hx)⟩

namespace UniformIntegrable

protected theorem aestronglyMeasurable (hf : UniformIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.1 i

protected theorem unifIntegrable (hf : UniformIntegrable f p μ) :
    UnifIntegrable f p μ :=
  hf.2.1

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) :
    MemLp (f i) p μ :=
  ⟨hf.1 i,
    let ⟨_, _, hC⟩ := hf.2
    lt_of_le_of_lt (hC i) coe_lt_top⟩

end UniformIntegrable

section UnifIntegrable

/-! ### `UnifIntegrable`

This section deals with uniform integrability in the measure theory sense. -/

namespace UnifIntegrable

protected theorem mk_iff :
    UnifIntegrable f p μ ↔ Tendsto (fun ε ↦ ⨆ (i : ι) (s : Set α) (_ : MeasurableSet s)
      (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  rw [UnifIntegrable, iff_iff_eq]
  congrm Tendsto (fun ε ↦ ⨆ i, ?_) _ _
  refine le_antisymm (iSup₂_le fun s hsμ ↦ ?_) (iSup₂_le_iSup _ _)
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset μ s
  grw [← le_iSup₂ t ht, ← le_iSup _ (hμt ▸ hsμ), eLpNorm_mono_measure _ (μ.restrict_mono_set hst)]

protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f + g) p μ := by
  rw [UnifIntegrable.mk_iff]
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hf (ε / 2) (ε.half_pos hε.ne'),
    ENNReal.tendsto_nhds_zero.1 hg (ε / 2) (ε.half_pos hε.ne')] with δ hδf hδg
  simp only [iSup_le_iff, Pi.add_apply] at hδf hδg ⊢
  intro i s hs hsμ
  grw [eLpNorm_add_le (hf_meas i).restrict (hg_meas i).restrict hp, hδf i s hsμ, hδg i s hsμ,
    ε.add_halves]

protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hf ε hε] with s hs
  simpa only [Pi.neg_apply, eLpNorm_neg]

protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifIntegrable (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg

protected theorem ae_mono (hg : UnifIntegrable g p μ) (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifIntegrable f p μ := by
  refine tendsto_nhds_bot_mono hg (Eventually.of_forall fun ε ↦ ?_)
  simp only
  gcongr
  exact eLpNorm_mono_enorm_ae ((hfg i).filter_mono ae_restrict_le)

protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable g p μ :=
  hf.ae_mono fun i ↦ ((hfg i).symm.fun_comp _).le

/-- Uniform integrability is preserved by restriction of the functions to a set. -/
protected theorem indicator (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable (fun i ↦ s.indicator (f i)) p μ :=
  hf.ae_mono fun i ↦ Eventually.of_forall fun x ↦ enorm_indicator_le_enorm_self (f i) x

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
protected theorem restrict (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable f p (μ.restrict s) := by
  rw [UnifIntegrable.mk_iff]
  apply tendsto_nhds_bot_mono hf (nhds_zero_basis.eventually_iff.2 ?_)
  refine ⟨∞, zero_lt_top, fun ε hε ↦ iSup_mono fun i ↦ ?_⟩
  simp only [iSup_le_iff]
  intro t ht hμt
  grw [μ.restrict_restrict ht, ← le_iSup₂ (t ∩ s) (μ.restrict_apply ht ▸ hμt)]

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ := by
  refine tendsto_nhds_bot_mono hf (Eventually.of_forall fun ε ↦ ?_)
  simp only [Function.comp_apply]
  exact iSup_comp_le (f := fun i ↦  ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm (f i) p (μ.restrict s)) _

end UnifIntegrable

/-- A characterization of `UnifIntegrable` families. This version assumes that the sets `s` are
measurable, and is convenient for proving that a family is `UnifIntegrable`. See
`unifIntegrable_iff` for a version where the sets `s` are not assumed measurable. -/
theorem unifIntegrable_iff' :
  UnifIntegrable f p μ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  rw [UnifIntegrable.mk_iff, ENNReal.tendsto_nhds_zero]
  apply forall₂_congr fun ε hε ↦ ?_
  rw [nhds_zero_basis_Iic.eventually_iff]
  apply exists_congr fun δ ↦ and_congr_right fun hδ ↦ ?_
  simp only [mem_Iic, iSup_le_iff]
  exact ⟨fun h ↦ h (le_refl δ), fun h x hx i s hs hμs ↦ h i s hs (hμs.trans hx)⟩

theorem unifIntegrable_congr_ae (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

theorem unifIntegrable_of_isEmpty [IsEmpty ι] : UnifIntegrable f p μ := by simp [UnifIntegrable]

theorem unifIntegrable_zero_meas [MeasurableSpace α] :
    UnifIntegrable f p (0 : Measure α) := by
  simp [UnifIntegrable]

theorem tendsto_indicator_ge (f : α → β) (x : α) :
    Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (‖f x‖₊ : ℝ) + 1) fun n hn => ?_
  rw [Set.indicator_of_notMem]
  simp only [not_le, Set.mem_ofPred_eq]
  refine lt_of_le_of_lt (Nat.le_ceil _) ?_
  refine lt_of_lt_of_le (lt_add_one _) ?_
  norm_cast

section

variable {f : α → β}

/-- This lemma is weaker than `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
as the latter provides `0 ≤ M` and does not require the measurability of `f`. -/
theorem MemLp.integral_indicator_norm_ge_le (hf : MemLp f 1 μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖₊ ∂μ) ≤ ε := by
  have htendsto :
      ∀ᵐ x ∂μ, Tendsto (fun M : ℕ => { x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_indicator_ge f x)
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable ({ x | (M : ℝ) ≤ ‖f x‖₊ }.indicator f) μ := by
    intro M
    apply hf.1.indicator
    apply StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      hmeas.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hbound : HasFiniteIntegral (fun x => ‖f x‖) μ := by
    rw [memLp_one_iff_integrable] at hf
    exact hf.norm.2
  have : Tendsto (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖{ x | n ≤ ‖f x‖₊ }.indicator f a - 0‖ ∂μ)
      atTop (𝓝 0) := by
    refine tendsto_lintegral_norm_of_dominated_convergence hmeas hbound ?_ htendsto
    exact fun n => univ_mem' (id fun x ↦ norm_indicator_le_norm_self f x)
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this ε hε
  simp only [sub_zero] at hM
  refine ⟨M, ?_⟩
  convert! hM M le_rfl
  simp only [coe_nnnorm, ofReal_eq_coe_nnreal (norm_nonneg _)]
  rfl

/-- This lemma is superseded by `MeasureTheory.MemLp.integral_indicator_norm_ge_nonneg_le`
which does not require measurability. -/
theorem MemLp.integral_indicator_norm_ge_nonneg_le_of_meas (hf : MemLp f 1 μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ε :=
  let ⟨M, hM⟩ := hf.integral_indicator_norm_ge_le hmeas hε
  ⟨max M 0, le_max_right _ _, by simpa⟩

theorem MemLp.integral_indicator_norm_ge_nonneg_le (hf : MemLp f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫⁻ x, ‖{ x | M ≤ ‖f x‖₊ }.indicator f x‖ₑ ∂μ) ≤ ε := by
  have hf_mk : MemLp (hf.1.mk f) 1 μ := (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  obtain ⟨M, hM_pos, hfM⟩ :=
    hf_mk.integral_indicator_norm_ge_nonneg_le_of_meas hf.1.stronglyMeasurable_mk hε
  refine ⟨M, hM_pos, (le_of_eq ?_).trans hfM⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hf.1.ae_eq_mk] with x hx
  simp only [Set.indicator_apply, coe_nnnorm, Set.mem_ofPred_eq, hx.symm]

theorem MemLp.eLpNormEssSup_indicator_norm_ge_eq_zero (hf : MemLp f ∞ μ)
    (hmeas : StronglyMeasurable f) :
    ∃ M : ℝ, eLpNormEssSup ({ x | M ≤ ‖f x‖₊ }.indicator f) μ = 0 := by
  have hbdd : eLpNormEssSup f μ < ∞ := hf.eLpNorm_lt_top
  refine ⟨(eLpNorm f ∞ μ + 1).toReal, ?_⟩
  rw [eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict]
  · have : μ.restrict { x : α | (eLpNorm f ⊤ μ + 1).toReal ≤ ‖f x‖₊ } = 0 := by
      simp only [coe_nnnorm, eLpNorm_exponent_top, Measure.restrict_eq_zero]
      have : { x : α | (eLpNormEssSup f μ + 1).toReal ≤ ‖f x‖ } ⊆
          { x : α | eLpNormEssSup f μ < ‖f x‖₊ } := by
        intro x hx
        rw [Set.mem_ofPred_eq, ← toReal_lt_toReal hbdd.ne coe_lt_top.ne, coe_toReal, coe_nnnorm]
        refine lt_of_lt_of_le ?_ hx
        rw [toReal_lt_toReal hbdd.ne]
        · exact lt_add_right hbdd.ne one_ne_zero
        · finiteness
      rw [← nonpos_iff_eq_zero]
      refine (measure_mono this).trans ?_
      have hle := enorm_ae_le_eLpNormEssSup f μ
      simp_rw [ae_iff, not_le] at hle
      exact nonpos_iff_eq_zero.2 hle
    rw [this, eLpNormEssSup_measure_zero]
  exact measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe

/-- This lemma is slightly weaker than `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le` as the
latter provides `0 < M`. -/
theorem MemLp.eLpNorm_indicator_norm_ge_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ M : ℝ, eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ε := by
  by_cases hp_ne_zero : p = 0
  · exact ⟨1, by simp [hp_ne_zero]⟩
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    obtain ⟨M, hM⟩ := hf.eLpNormEssSup_indicator_norm_ge_eq_zero hmeas
    refine ⟨M, ?_⟩
    simp only [eLpNorm_exponent_top, hM, zero_le]
  obtain ⟨M, hM', hM⟩ := MemLp.integral_indicator_norm_ge_nonneg_le
    (μ := μ) (hf.norm_rpow hp_ne_zero hp_ne_top) (rpow_pos_of_nonneg hε toReal_nonneg)
  refine ⟨M ^ (1 / p.toReal), ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top, ← rpow_one ε]
  conv_rhs => rw [← mul_one_div_cancel (toReal_pos hp_ne_zero hp_ne_top).ne']
  rw [rpow_mul]
  gcongr
  convert! hM using 3 with x
  rw [enorm_indicator_eq_indicator_enorm, enorm_indicator_eq_indicator_enorm]
  have hiff : M ^ (1 / p.toReal) ≤ ‖f x‖₊ ↔ M ≤ ‖‖f x‖ ^ p.toReal‖₊ := by
    rw [coe_nnnorm, coe_nnnorm, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm,
      ← Real.rpow_le_rpow_iff hM' (by positivity)
        (one_div_pos.2 <| toReal_pos hp_ne_zero hp_ne_top), ← Real.rpow_mul (norm_nonneg _),
      mul_one_div_cancel (toReal_pos hp_ne_zero hp_ne_top).ne', Real.rpow_one]
  by_cases hx : x ∈ { x : α | M ^ (1 / p.toReal) ≤ ‖f x‖₊ }
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem, Real.enorm_of_nonneg (by positivity),
      ← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm]
    rw [Set.mem_ofPred_eq]
    rwa [← hiff]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    · simp [toReal_pos hp_ne_zero hp_ne_top]
    · rw [Set.mem_ofPred_eq]
      rwa [← hiff]

/-- This lemma implies that a single function is uniformly integrable (in the probability sense). -/
theorem MemLp.eLpNorm_indicator_norm_ge_pos_le (hf : MemLp f p μ) (hmeas : StronglyMeasurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ eLpNorm ({ x | M ≤ ‖f x‖₊ }.indicator f) p μ ≤ ε := by
  obtain ⟨M, hM⟩ := hf.eLpNorm_indicator_norm_ge_le hmeas hε
  refine
    ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_trans (eLpNorm_mono fun x => ?_) hM⟩
  simp only [norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

end

theorem eLpNorm_indicator_le_of_bound {f : α → β} (hp_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) {M : ℝ}
    (hf : ∀ x, ‖f x‖ < M) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε := by
  by_cases! hM : M ≤ 0
  · refine ⟨1, zero_lt_one, fun s _ _ => ?_⟩
    rw [(_ : f = 0)]
    · simp
    · ext x
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      exact (lt_of_lt_of_le (hf x) hM).le
  refine ⟨(ε / ENNReal.ofReal M) ^ p.toReal,
    rpow_pos_of_nonneg (ENNReal.div_pos hε.ne' coe_ne_top) toReal_nonneg, ?_⟩
  intro s hs hμ
  by_cases hp : p = 0
  · simp [hp]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have haebdd : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ M := by
    filter_upwards
    exact fun x ↦ (hf x).le
  refine (eLpNorm_le_of_ae_bound haebdd).trans ?_
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ← ENNReal.le_div_iff_mul_le (.inl _) (.inl ofReal_ne_top)]
  · rwa [rpow_inv_le_iff (toReal_pos hp hp_top)]
  · simpa only [ofReal_eq_zero, not_le, Ne]

section

variable {f : α → β}

/-- Auxiliary lemma for `MeasureTheory.MemLp.eLpNorm_indicator_le`. -/
theorem MemLp.eLpNorm_indicator_le' (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ 2 * ε := by
  obtain ⟨M, hMpos, hM⟩ := hf.eLpNorm_indicator_norm_ge_pos_le hmeas hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    eLpNorm_indicator_le_of_bound (f := { x | ‖f x‖ < M }.indicator f) hp_top hε (by
      intro x
      rw [norm_indicator_eq_indicator_norm, Set.indicator_apply]
      · split_ifs with h
        exacts [h, hMpos])
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  rw [(_ : f = { x : α | M ≤ ‖f x‖₊ }.indicator f + { x : α | ‖f x‖ < M }.indicator f)]
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    refine (eLpNorm_add_le ?_ ?_ hp_one).trans ?_
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_le measurable_const hmeas.nnnorm.measurable.subtype_coe))
    · exact StronglyMeasurable.aestronglyMeasurable
        (hmeas.indicator (measurableSet_lt hmeas.nnnorm.measurable.subtype_coe measurable_const))
    · rw [two_mul]
      refine add_le_add ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hM) ?_
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact hδ s hs hμs
  · ext x
    by_cases hx : M ≤ ‖f x‖
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, add_zero] <;> simpa
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem, zero_add] <;>
        simpa using hx

/-- This lemma is superseded by `MeasureTheory.MemLp.eLpNorm_indicator_le` which does not require
measurability on `f`. -/
theorem MemLp.eLpNorm_indicator_le_of_meas (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ)
    (hmeas : StronglyMeasurable f) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε := by
  obtain ⟨δ, hδpos, hδ⟩ := hf.eLpNorm_indicator_le' hp_one hp_top hmeas (ε.half_pos hε.ne')
  refine ⟨δ, hδpos, fun s hs hμs ↦ (hδ s hs hμs).trans_eq ?_⟩
  exact ENNReal.mul_div_cancel two_ne_zero ofNat_ne_top

theorem MemLp.eLpNorm_indicator_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, MeasurableSet s → μ s ≤ δ → eLpNorm (s.indicator f) p μ ≤ ε := by
  have hℒp := hf
  obtain ⟨⟨f', hf', heq⟩, _⟩ := hf
  obtain ⟨δ, hδpos, hδ⟩ := (hℒp.ae_eq heq).eLpNorm_indicator_le_of_meas hp_one hp_top hf' hε
  refine ⟨δ, hδpos, fun s hs hμs => ?_⟩
  convert! hδ s hs hμs using 1
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  exact eLpNorm_congr_ae heq.restrict

theorem MemLp.tendsto_eLpNorm_restrict_zero (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hf : MemLp f p μ) :
    Tendsto (fun ε ↦ ⨆ (s : Set α) (_ : μ s ≤ ε), eLpNorm f p (μ.restrict s)) (𝓝 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ nhds_zero_basis.eventually_iff.2 ?_
  obtain ⟨δ, hδ, hδf⟩ := hf.eLpNorm_indicator_le hp_one hp_top hε
  simp only [mem_Iio, iSup_le_iff]
  refine ⟨δ, hδ, fun γ hγ s hμs ↦ ?_⟩
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset μ s
  grw [← hδf t ht ((hμt ▸ hμs).trans hγ.le), eLpNorm_indicator_eq_eLpNorm_restrict ht,
    eLpNorm_mono_measure f (μ.restrict_mono_set hst)]

/-- A constant function is uniformly integrable. -/
theorem unifIntegrable_const {g : α → β} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι ↦ g) p μ := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact unifIntegrable_of_isEmpty
  rw [UnifIntegrable]
  simp only [ciSup_const]
  exact hg.tendsto_eLpNorm_restrict_zero hp_one hp_top

/-- A single function is uniformly integrable. -/
theorem unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · exact unifIntegrable_of_isEmpty
  rw [UnifIntegrable]
  simp only [ciSup_subsingleton i]
  exact (hf i).tendsto_eLpNorm_restrict_zero hp_one hp_top

/-- A finite sequence of Lp functions is uniformly integrable. -/
theorem unifIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  have key := fun i ↦ (hf i).tendsto_eLpNorm_restrict_zero hp_one hp_top
  simp only [ENNReal.tendsto_nhds_zero] at key
  filter_upwards [eventually_all.2 (fun i ↦ key i ε hε)] with a ha
  exact iSup_le ha

@[deprecated (since := "2026-07-24")] alias unifIntegrable_fin := unifIntegrable_finite

end

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases! h : ∞ ≤ ε
  · rw [top_le_iff] at h
    exact ⟨0, fun n _ => by simp [h]⟩
  by_cases hμ : μ = 0
  · exact ⟨0, fun n _ => by simp [hμ]⟩
  have hε' : 0 < ε / 3 := ε.div_pos hε.ne' ofNat_ne_top
  have hdivp : 0 ≤ 1 / p.toReal := by positivity
  have hpow : 0 < measureUnivNNReal μ ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  obtain ⟨δ₁, hδ₁, heLpNorm₁⟩ := unifIntegrable_iff.1 hui (ε / 3) hε'
  obtain ⟨δ₂, hδ₂, heLpNorm₂⟩ := hg'.eLpNorm_indicator_le hp hp' hε'
  obtain ⟨t, htm, ht₁, ht₂⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂)
  rw [Metric.tendstoUniformlyOn_iff] at ht₂
  specialize ht₂ (ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    (div_pos (toReal_pos (gt_iff_lt.1 hε).ne' h.ne) (mul_pos (by simp) hpow))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht₂; clear ht₂
  refine ⟨N, fun n hn => ?_⟩
  rw [← t.indicator_self_add_compl (f n - g)]
  grw [eLpNorm_add_le (((hf n).sub hg).indicator htm).aestronglyMeasurable
    (((hf n).sub hg).indicator htm.compl).aestronglyMeasurable hp, sub_eq_add_neg,
    Set.indicator_add' t, Set.indicator_neg', eLpNorm_add_le
    ((hf n).indicator htm).aestronglyMeasurable (hg.indicator htm).neg.aestronglyMeasurable hp]
  have hnf : eLpNorm (t.indicator (f n)) p μ ≤ ε / 3 := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict htm]
    exact heLpNorm₁ n t (ht₁.trans (min_le_left _ _))
  have hng : eLpNorm (t.indicator g) p μ ≤ ε / 3 :=
    heLpNorm₂ t htm (ht₁.trans (min_le_right _ _))
  have hlt : eLpNorm (tᶜ.indicator (f n - g)) p μ ≤ ε / 3 := by
    specialize hN n hn
    have : 0 ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)) := by positivity
    have hε₃ : ENNReal.ofReal (ε.toReal / 3) = ε / 3 := by
      rw [ofReal_div_of_pos (show (0 : ℝ) < 3 by simp), ofReal_toReal h.ne]
      simp
    have := eLpNorm_indicator_sub_le_of_dist_bdd μ hp' htm.compl this fun x hx =>
      (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.toReal / (3 * measureUnivNNReal μ ^ (1 / p.toReal)))
    refine this.trans ?_
    rw [div_mul_eq_div_mul_one_div, ← ofReal_toReal (measure_lt_top μ tᶜ).ne,
      ofReal_rpow_of_nonneg toReal_nonneg hdivp, ← ofReal_mul, mul_assoc]; swap
    · positivity
    rw [ofReal_mul (by positivity), hε₃]
    refine mul_le_of_le_one_right (by positivity) (ofReal_le_one.2 ?_)
    rw [mul_comm, mul_one_div, div_le_one]
    · gcongr
      refine (toReal_le_of_le_ofReal (measureUnivNNReal_pos hμ).le ?_)
      rw [ofReal_coe_nnreal, coe_measureUnivNNReal]
      exact measure_mono (Set.subset_univ _)
    · exact Real.rpow_pos_of_pos (measureUnivNNReal_pos hμ) _
  rw [eLpNorm_neg, ← add_thirds ε, ← sub_eq_add_neg]
  gcongr

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have : ∀ n, eLpNorm (f n - g) p μ = eLpNorm ((hf n).mk (f n) - hg.1.mk g) p μ :=
    fun n => eLpNorm_congr_ae ((hf n).ae_eq_mk.sub hg.1.ae_eq_mk)
  simp_rw [this]
  refine tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' (fun n => (hf n).stronglyMeasurable_mk)
    hg.1.stronglyMeasurable_mk (hg.ae_eq hg.1.ae_eq_mk) (hui.ae_eq fun n => (hf n).ae_eq_mk) ?_
  have h_ae_forall_eq : ∀ᵐ x ∂μ, ∀ n, f n x = (hf n).mk (f n) x := by
    rw [ae_all_iff]
    exact fun n => (hf n).ae_eq_mk
  filter_upwards [hfg, h_ae_forall_eq, hg.1.ae_eq_mk] with x hx_tendsto hxf_eq hxg_eq
  rw [← hxg_eq]
  convert! hx_tendsto using 1
  ext1 n
  exact (hxf_eq n).symm

variable {f : ℕ → α → β} {g : α → β}

theorem unifIntegrable_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n ↦ eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ := by
  apply unifIntegrable_iff.2 fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hN⟩ := hf_tendsto (ε) (by simpa)
  let F : Fin N → α → β := fun n ↦ f n
  have hF : ∀ n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨δ₁, hδpos₁, hδ₁⟩ := unifIntegrable_iff.1 (unifIntegrable_finite hp hp' hF) ε hε
  refine ⟨δ₁, hδpos₁, fun n s hμs ↦ ?_⟩
  by_cases! hn : n < N
  · exact hδ₁ ⟨n, hn⟩ s hμs
  · exact (eLpNorm_restrict_le (f n) p μ s).trans (hN n hn)

/-- Convergence in Lp implies uniform integrability. -/
theorem unifIntegrable_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifIntegrable f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifIntegrable.add ?_ ?_ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifIntegrable_const hp hp' hg
  · exact unifIntegrable_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg

/-- Forward direction of Vitali's convergence theorem: if `f` is a sequence of uniformly integrable
functions that converge in measure to some function `g` in a finite measure space, then `f`
converge in Lp to `g`. -/
theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms, tendsto_Lp_finite_of_tendsto_ae hp hp' (fun _ ↦ hf _) hg (hui.comp _) hms'⟩

/-- **Vitali's convergence theorem**: A sequence of functions `f` converges to `g` in Lp if and
only if it is uniformly integrable and converges to `g` in measure. -/
theorem tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  ⟨fun h => tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2 h.1, fun h =>
    ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h⟩⟩

/-- This lemma is superseded by `unifIntegrable_of` which do not require `C` to be positive. -/
theorem unifIntegrable_of' (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ := by
  have hpzero := (lt_of_lt_of_le zero_lt_one hp).ne'
  by_cases hμ : μ Set.univ = 0
  · rw [Measure.measure_univ_eq_zero] at hμ
    exact hμ.symm ▸ unifIntegrable_zero_meas
  refine unifIntegrable_iff'.2 fun ε hε ↦ ?_
  obtain ⟨C, hCpos, hC⟩ := h (ε / 2) (ε.half_pos hε.ne')
  refine ⟨(ε / (2 * C)) ^ p.toReal, ?_, ?_⟩
  · exact rpow_pos_of_nonneg (ε.div_pos hε.ne' (mul_ne_top ofNat_ne_top coe_ne_top))
      toReal_nonneg
  intro i s hs hμs
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  by_cases hμs' : μ s = 0
  · rw [(eLpNorm_eq_zero_iff ((hf i).indicator hs).aestronglyMeasurable hpzero).2
        (indicator_meas_zero hμs')]
    simp
  calc
    eLpNorm (Set.indicator s (f i)) p μ ≤
        eLpNorm (Set.indicator (s ∩ { x | C ≤ ‖f i x‖₊ }) (f i)) p μ +
          eLpNorm (Set.indicator (s ∩ { x | ‖f i x‖₊ < C }) (f i)) p μ := by
      refine le_trans (Eq.le ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (hs.inter ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const))))
        hp)
      congr
      change _ = fun x => (s ∩ { x : α | C ≤ ‖f i x‖₊ }).indicator (f i) x +
        (s ∩ { x : α | ‖f i x‖₊ < C }).indicator (f i) x
      rw [← Set.indicator_union_of_disjoint]
      · rw [← Set.inter_union_distrib_left, (by ext; simp [le_or_gt] :
            { x : α | C ≤ ‖f i x‖₊ } ∪ { x : α | ‖f i x‖₊ < C } = Set.univ),
          Set.inter_univ]
      · refine (Disjoint.inf_right' _ ?_).inf_left' _
        rw [disjoint_iff_inf_le]
        rintro x ⟨hx₁, hx₂⟩
        rw [Set.mem_ofPred_eq] at hx₁ hx₂
        exact False.elim (hx₂.ne (eq_of_le_of_not_lt hx₁ (not_lt.2 hx₂.le)).symm)
    _ ≤ eLpNorm (Set.indicator { x | C ≤ ‖f i x‖₊ } (f i)) p μ +
        (C : ℝ≥0∞) * μ s ^ (1 / ENNReal.toReal p) := by
      refine add_le_add
        (eLpNorm_mono fun x => norm_indicator_le_of_subset Set.inter_subset_right _ _) ?_
      rw [← Set.indicator_indicator]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have : ∀ᵐ x ∂μ.restrict s, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖ ≤ C := by
        filter_upwards
        simp_rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' (fun x (hx : _ < _) => hx.le) fun _ _ => NNReal.coe_nonneg _
      refine le_trans (eLpNorm_le_of_ae_bound this) ?_
      rw [mul_comm, Measure.restrict_apply' hs, Set.univ_inter, ofReal_coe_nnreal, one_div]
    _ ≤ (ε / 2) + C * (ε / (2 * C)) := by
      grw [hC i]
      gcongr
      rwa [one_div, rpow_inv_le_iff (toReal_pos hpzero hp')]
    _ ≤ (ε / 2) + (ε / 2) := by
      apply add_le_add_right
      rw [← ENNReal.mul_comm_div, ENNReal.le_div_iff_mul_le (.inr hε.ne') (.inl ofNat_ne_top),
        mul_comm _ 2, ← mul_assoc, ← mul_div_assoc]
      exact (mul_le_mul_left ENNReal.div_self_le_one ε).trans_eq (one_mul ε)
    _ = ε := ε.add_halves

theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  refine
    (unifIntegrable_of' hp hp' (fun i => (Exists.choose_spec <| hf i).1) fun ε hε => ?_).ae_eq
      fun i => (Exists.choose_spec <| hf i).2.symm
  obtain ⟨C, hC⟩ := h ε hε
  have hCg : ∀ i, eLpNorm ({ x | C ≤ ‖g i x‖₊ }.indicator (g i)) p μ ≤ ε := by
    intro i
    refine le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)
    filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
    by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
    · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
      rwa [Set.mem_ofPred, hx] at hfx
    · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
      rwa [Set.mem_ofPred, hx] at hfx
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun i => le_trans (eLpNorm_mono fun x => ?_) (hCg i)⟩
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  grw [← le_max_left]

/-- If `fn` is `UnifIntegrable`, then the family of limits in probability of sequences of `fn` is
`UnifIntegrable`. -/
lemma UnifIntegrable.unifIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine unifIntegrable_iff'.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδ'⟩ := (unifIntegrable_iff.1 hUI) ε hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht ht' ↦ ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict ht]
  apply eLpNorm_le_of_tendstoInMeasure _ (hs.indicator t) (fun n ↦ (hfn (s n)).indicator ht)
  apply Eventually.of_forall fun n ↦ ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict ht, Function.comp_apply]
  exact hδ' (s n) t ht'

/-- If `fn` is `UnifIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UnifIntegrable`. -/
lemma UnifIntegrable.unifIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine unifIntegrable_iff'.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδ'⟩ := (unifIntegrable_iff.1 hUI) ε hε
  refine ⟨δ, hδ, fun ⟨f, s, hs⟩ t ht hμt ↦ ?_⟩
  refine Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall (f := u) fun n ↦ hδ' (s n) t hμt) ?_ ?_
  · exact fun n ↦ (hfn (s n)).mono_measure μ.restrict_le_self
  · exact hs.filter_mono ae_restrict_le

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
    fun _ => eLpNorm_measure_zero.le⟩

theorem UniformIntegrable.ae_eq {g : ι → α → β} (hf : UniformIntegrable f p μ)
    (hfg : ∀ n, f n =ᵐ[μ] g n) : UniformIntegrable g p μ := by
  obtain ⟨hfm, hunif, C, hC⟩ := hf
  refine ⟨fun i => (hfm i).congr (hfg i), (unifIntegrable_congr_ae hfg).1 hunif, C, fun i => ?_⟩
  rw [← eLpNorm_congr_ae (hfg i)]
  exact hC i

theorem uniformIntegrable_congr_ae {g : ι → α → β} (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

/-- A finite sequence of Lp functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ := by
  cases nonempty_fintype ι
  refine ⟨fun n => (hf n).1, unifIntegrable_finite hp_one hp_top hf, ?_⟩
  by_cases hι : Nonempty ι
  · choose _ hf using hf
    set C := (Finset.univ.image fun i : ι => eLpNorm (f i) p μ).max'
      ⟨eLpNorm (f hι.some) p μ, Finset.mem_image.2 ⟨hι.some, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C.toNNReal, fun i => ?_⟩
    unfold C
    grw [coe_toNNReal ?_, ← Finset.le_max' _ _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]
    refine ne_of_lt ((Finset.max'_lt_iff _ _).2 fun y hy => ?_)
    rw [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hf i
  · exact ⟨0, fun i => False.elim <| hι <| Nonempty.intro i⟩

/-- A single function is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp_one hp_top hf

/-- A constant sequence of functions is uniformly integrable in the probability sense. -/
theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι ↦ g) p μ :=
  ⟨fun _ ↦ hg.1, unifIntegrable_const hp hp_ne_top hg,
    ⟨(eLpNorm g p μ).toNNReal, fun _ ↦ (coe_toNNReal hg.2.ne).symm.le⟩⟩

/-- This lemma is superseded by `uniformIntegrable_of` which only requires
`AEStronglyMeasurable`. -/
theorem uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ := by
  refine ⟨fun i => (hf i).aestronglyMeasurable,
    unifIntegrable_of hp hp' (fun i => (hf i).aestronglyMeasurable) h, ?_⟩
  obtain ⟨C, hC⟩ := h 1 one_pos
  refine ⟨((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1).toNNReal, fun i => ?_⟩
  calc
    eLpNorm (f i) p μ ≤
        eLpNorm ({ x : α | ‖f i x‖₊ < C }.indicator (f i)) p μ +
          eLpNorm ({ x : α | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ := by
      refine le_trans (eLpNorm_mono_enorm fun x => ?_) (eLpNorm_add_le
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator ((hf i).nnnorm.measurableSet_lt stronglyMeasurable_const)))
        (StronglyMeasurable.aestronglyMeasurable
          ((hf i).indicator (stronglyMeasurable_const.measurableSet_le (hf i).nnnorm))) hp)
      rw [Pi.add_apply, Set.indicator_apply]
      split_ifs with hx
      · rw [Set.indicator_of_notMem, add_zero]
        simpa using hx
      · rw [Set.indicator_of_mem, zero_add]
        simpa using hx
    _ ≤ (C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 := by
      have : ∀ᵐ x ∂μ, ‖{ x : α | ‖f i x‖₊ < C }.indicator (f i) x‖₊ ≤ C := by
        filter_upwards
        simp_rw [nnnorm_indicator_eq_indicator_nnnorm]
        exact Set.indicator_le fun x (hx : _ < _) => hx.le
      refine add_le_add (le_trans (eLpNorm_le_of_ae_bound this) ?_) (ofReal_one ▸ hC i)
      simp_rw [NNReal.val_eq_coe, ofReal_coe_nnreal, mul_comm]
      exact le_rfl
    _ = ((C : ℝ≥0∞) * μ Set.univ ^ p.toReal⁻¹ + 1 : ℝ≥0∞).toNNReal := by
      rw [coe_toNNReal (by finiteness)]

/-- A sequence of functions `(fₙ)` is uniformly integrable in the probability sense if for all
`ε > 0`, there exists some `C` such that `∫ x in {|fₙ| ≥ C}, fₙ x ∂μ ≤ ε` for all `n`. -/
theorem uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ := by
  set g : ι → α → β := fun i => (hf i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hf i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hf i).2.symm
  refine (uniformIntegrable_of' hp hp' hgmeas fun ε hε => ?_).ae_eq hgeq
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hf i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/-- This lemma is superseded by `UniformIntegrable.spec` which does not require measurability. -/
theorem UniformIntegrable.spec' (hp : p ≠ 0) (hp' : p ≠ ∞) (hf : ∀ i, StronglyMeasurable (f i))
    (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  obtain ⟨-, hfu, M, hM⟩ := hfu
  obtain ⟨δ, hδpos, hδ⟩ := (unifIntegrable_iff.1 hfu) ε hε
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, ∀ i, μ { x | C ≤ ‖f i x‖₊ } ≤ δ := by
    by_contra! hcon
    choose ℐ hℐ using hcon
    have : ∀ C : ℝ≥0, (ofNNReal C) * δ ^ (1 / p.toReal) ≤ eLpNorm (f (ℐ C)) p μ := by
      intro C
      calc
        C • (δ : ℝ≥0∞) ^ (1 / p.toReal) ≤ C • μ { x | C ≤ ‖f (ℐ C) x‖₊ } ^ (1 / p.toReal) := by
          rw [smul_def, smul_def, smul_eq_mul, smul_eq_mul]
          refine mul_le_mul' le_rfl
            (rpow_le_rpow (hℐ C).le (one_div_nonneg.2 toReal_nonneg))
        _ ≤ eLpNorm ({ x | C ≤ ‖f (ℐ C) x‖₊ }.indicator (f (ℐ C))) p μ := by
          refine le_eLpNorm_of_bddBelow hp hp' _
            (measurableSet_le measurable_const (hf _).nnnorm.measurable)
            (Eventually.of_forall fun x hx => ?_)
          rwa [nnnorm_indicator_eq_indicator_nnnorm, Set.indicator_of_mem hx]
        _ ≤ eLpNorm (f (ℐ C)) p μ := eLpNorm_indicator_le _
    specialize this (2 * max M 1 * δ⁻¹ ^ (1 / p.toReal)).toNNReal
    replace this := this.trans (hM _)
    rw [toNNReal_mul, toNNReal_mul, coe_mul, coe_mul, toNNReal_coe (max M 1),
      coe_toNNReal ofNat_ne_top, coe_toNNReal _] at this; swap
    · exact rpow_ne_top_of_nonneg (by positivity) (by finiteness)
    rw [mul_assoc, ← mul_rpow_of_nonneg δ⁻¹ δ (by positivity),
      ENNReal.inv_mul_cancel hδpos.ne' (ne_top_of_lt (hℐ 0)), one_rpow, mul_one,
      ← coe_two, ← coe_mul, coe_le_coe, two_mul] at this
    replace this := (add_le_add (le_max_left M 1) (le_max_right M 1)).trans this
    exact not_lt_of_ge this (lt_add_one M)
  refine ⟨C, fun i ↦ (hδ i { x | C ≤ ‖f i x‖₊ } (hC i)).trans_eq' ?_⟩
  apply (eLpNorm_indicator_eq_eLpNorm_restrict _).symm
  exact (measurableSet_le measurable_const (hf i).nnnorm.measurable)

theorem UniformIntegrable.spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  set g : ι → α → β := fun i => (hfu.1 i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfu.1 i).1
  have hgunif : UniformIntegrable g p μ := hfu.ae_eq fun i => (Exists.choose_spec <| hfu.1 i).2
  obtain ⟨C, hC⟩ := hgunif.spec' hp hp' hgmeas hε
  refine ⟨C, fun i => le_trans (le_of_eq <| eLpNorm_congr_ae ?_) (hC i)⟩
  filter_upwards [(Exists.choose_spec <| hfu.1 i).2] with x hx
  by_cases hfx : x ∈ { x | C ≤ ‖f i x‖₊ }
  · rw [Set.indicator_of_mem hfx, Set.indicator_of_mem, hx]
    rwa [Set.mem_ofPred, hx] at hfx
  · rw [Set.indicator_of_notMem hfx, Set.indicator_of_notMem]
    rwa [Set.mem_ofPred, hx] at hfx

/-- The definition of uniform integrable in mathlib is equivalent to the definition commonly
found in literature. -/
theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    UniformIntegrable f p μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε > 0, ∃ C : ℝ≥0,
          ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε :=
  ⟨fun h => ⟨h.1, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne' hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

/-- The averaging of a uniformly integrable sequence is also uniformly integrable. -/
theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, f i)) p μ := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  refine ⟨fun n ↦ ?_, unifIntegrable_iff'.2 fun ε hε ↦ ?_, ?_⟩
  · exact (Finset.aestronglyMeasurable_sum _ fun i _ => hf₁ i).const_smul _
  · obtain ⟨δ, hδ₁, hδ₂⟩ := (unifIntegrable_iff.1 hf₂) ε hε
    refine ⟨δ, hδ₁, fun n s hs hle ↦ ?_⟩
    simp_rw [Finset.smul_sum]
    refine (eLpNorm_sum_le (fun i _ ↦ ((hf₁ i).const_smul _).mono_measure
      μ.restrict_le_self) hp).trans ?_
    have this i : s.indicator ((n : ℝ)⁻¹ • f i) = (↑n : ℝ)⁻¹ • s.indicator (f i) :=
      indicator_const_smul _ _ _
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine div_le_of_le_mul' ?_
    have key := Finset.sum_le_card_nsmul (.range n) (fun i ↦ eLpNorm (f i) p (μ.restrict s)) ε
    simp only [Finset.mem_range, Finset.card_range, nsmul_eq_mul] at key
    exact key fun i _ ↦ hδ₂ i s hle
  · obtain ⟨C, hC⟩ := hf₃
    simp_rw [Finset.smul_sum]
    refine ⟨C, fun n => (eLpNorm_sum_le (fun i _ => (hf₁ i).const_smul _) hp).trans ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    simp_rw [eLpNorm_const_smul, ← Finset.mul_sum]
    rw [enorm_inv (by positivity), Real.enorm_natCast, ← ENNReal.div_eq_inv_mul]
    refine div_le_of_le_mul' ?_
    simpa using Finset.sum_le_card_nsmul (.range n) _ _ fun i _ => hC i

/-- The averaging of a uniformly integrable real-valued sequence is also uniformly integrable. -/
theorem uniformIntegrable_average_real (hp : 1 ≤ p) {f : ℕ → α → ℝ} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i ∈ Finset.range n, f i) / (n : α → ℝ)) p μ := by
  convert! uniformIntegrable_average hp hf using 2 with n
  ext x
  simp [div_eq_inv_mul]

/-- If `fn` is `UniformIntegrable`, then the family of limits in probability of sequences of `fn` is
`UniformIntegrable`. -/
lemma UniformIntegrable.uniformIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_tendstoInMeasure u (fun i => hUI.1 i), ?_⟩
  · exact hs.aestronglyMeasurable (fun n => hUI.1 (s n))
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => eLpNorm_le_of_tendstoInMeasure
      (Eventually.of_forall fun n => hC (s n)) hs (fun n => hUI.1 (s n))⟩

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
lemma UniformIntegrable.memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_tendstoInMeasure u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges in measure to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
lemma UniformIntegrable.integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_tendstoInMeasure htends)

/-- If `fn` is `UniformIntegrable`, then the family of a.e. limits of sequences of `fn` is
`UniformIntegrable`. -/
lemma UniformIntegrable.uniformIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β}
    (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine ⟨fun ⟨f, s, hs⟩ => ?_, hUI.2.1.unifIntegrable_of_ae_tendsto u (fun i => hUI.1 i), ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae u (fun n => hUI.1 (s n)) hs
  · obtain ⟨C, hC⟩ := hUI.2.2
    exact ⟨C, fun ⟨f, s, hs⟩ => Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hC (s n)) (fun n => hUI.1 (s n)) hs⟩

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is in `Lp`. -/
lemma UniformIntegrable.memLp_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f p μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    MemLp g p μ := by
  simpa using (hUI.uniformIntegrable_of_ae_tendsto u).memLp ⟨g, ⟨fun n => n, htends⟩⟩

/-- Suppose `f` is a sequence of functions that converges a.e. to `g`. If `f` is
`UniformIntegrable`, then `g` is integrable. -/
lemma UniformIntegrable.integrable_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f 1 μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) :
    Integrable g μ :=
  memLp_one_iff_integrable.mp (hUI.memLp_of_ae_tendsto htends)

end UniformIntegrable

end MeasureTheory
