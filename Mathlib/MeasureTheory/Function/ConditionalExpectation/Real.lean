/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!

# Conditional expectation of real-valued functions

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `MeasureTheory.rnDeriv_ae_eq_condExp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `MeasureTheory.Integrable.uniformIntegrable_condExp`: the conditional expectation of a function
  form a uniformly integrable class.
* `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`: the pull-out property of the conditional
  expectation.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

theorem rnDeriv_ae_eq_condExp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ}
    (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f|m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm)) hs,
      ← setIntegral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable

-- TODO: the following couple of lemmas should be generalized and proved using Jensen's inequality
-- for the conditional expectation (not in mathlib yet) .
theorem eLpNorm_one_condExp_le_eLpNorm (f : α → ℝ) : eLpNorm (μ[f|m]) 1 μ ≤ eLpNorm f 1 μ := by
  by_cases hf : Integrable f μ
  swap; · rw [condExp_of_not_integrable hf, eLpNorm_zero]; exact zero_le _
  by_cases hm : m ≤ m0
  swap; · rw [condExp_of_not_le hm, eLpNorm_zero]; exact zero_le _
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hsig, eLpNorm_zero]; exact zero_le _
  calc
    eLpNorm (μ[f|m]) 1 μ ≤ eLpNorm (μ[(|f|)|m]) 1 μ := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [condExp_mono hf hf.abs
        (ae_of_all μ (fun x => le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
        (condExp_neg ..).symm.le.trans (condExp_mono hf.neg hf.abs
          (ae_of_all μ (fun x => neg_le_abs (f x) : ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂
      exact abs_le_abs hx₁ hx₂
    _ = eLpNorm f 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
        ← ENNReal.toReal_eq_toReal (hasFiniteIntegral_iff_enorm.mp integrable_condExp.2).ne
          (hasFiniteIntegral_iff_enorm.mp hf.2).ne,
        ← integral_norm_eq_lintegral_enorm
          (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
        ← integral_norm_eq_lintegral_enorm hf.1]
      simp_rw [Real.norm_eq_abs]
      rw (config := {occs := .pos [2]}) [← integral_condExp hm]
      refine integral_congr_ae ?_
      have : 0 ≤ᵐ[μ] μ[(|f|)|m] := by
        rw [← condExp_zero]
        exact condExp_mono (integrable_zero _ _ _) hf.abs
          (ae_of_all μ (fun x => abs_nonneg (f x) : ∀ x, 0 ≤ |f x|))
      filter_upwards [this] with x hx
      exact abs_eq_self.2 hx

theorem integral_abs_condExp_le (f : α → ℝ) : ∫ x, |(μ[f|m]) x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  by_cases hm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hm, Pi.zero_apply, abs_zero, integral_zero]
    positivity
  by_cases hfint : Integrable f μ
  swap
  · simp only [condExp_of_not_integrable hfint, Pi.zero_apply, abs_zero, integral_const,
      Algebra.id.smul_eq_mul, mul_zero]
    positivity
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  · apply ENNReal.toReal_mono <;> simp_rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
    · exact hfint.2.ne
    · rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_one_eq_lintegral_enorm]
      exact eLpNorm_one_condExp_le_eLpNorm _
  · filter_upwards with x using abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact hfint.1.norm
  · filter_upwards with x using abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.norm

theorem setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → ℝ) :
    ∫ x in s, |(μ[f|m]) x| ∂μ ≤ ∫ x in s, |f x| ∂μ := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero, integral_zero]
    positivity
  by_cases hfint : Integrable f μ
  swap
  · simp only [condExp_of_not_integrable hfint, Pi.zero_apply, abs_zero, integral_const,
      Algebra.id.smul_eq_mul, mul_zero]
    positivity
  have : ∫ x in s, |(μ[f|m]) x| ∂μ = ∫ x, |(μ[s.indicator f|m]) x| ∂μ := by
    rw [← integral_indicator (hnm _ hs)]
    refine integral_congr_ae ?_
    have : (fun x => |(μ[s.indicator f|m]) x|) =ᵐ[μ] fun x => |s.indicator (μ[f|m]) x| :=
      (condExp_indicator hfint hs).fun_comp abs
    refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) this.symm
    rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    simp only [Real.norm_eq_abs]
  rw [this, ← integral_indicator (hnm _ hs)]
  refine (integral_abs_condExp_le _).trans
    (le_of_eq <| integral_congr_ae <| Eventually.of_forall fun x => ?_)
  simp_rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]

/-- If the real-valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
theorem ae_bdd_condExp_of_ae_bdd {R : ℝ≥0} {f : α → ℝ} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |(μ[f|m]) x| ≤ R := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ ≠ 0 at h
  simp only [← zero_lt_iff, Set.compl_def, Set.mem_setOf_eq, not_le] at h
  suffices μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R < μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R by
    exact this.ne rfl
  refine lt_of_lt_of_le (setIntegral_gt_gt R.coe_nonneg ?_ h.ne') ?_
  · exact integrable_condExp.abs.integrableOn
  refine (setIntegral_abs_condExp_le ?_ _).trans ?_
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condExp.norm.measurable
  simp only [← smul_eq_mul, ← setIntegral_const]
  refine setIntegral_mono_ae hfint.abs.integrableOn ?_ hbdd
  refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_
    (integrable_condExp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
  refine setLIntegral_mono
    (stronglyMeasurable_condExp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, Real.nnnorm_of_nonneg R.coe_nonneg]
  exact Subtype.mk_le_mk.2 (le_of_lt hx)

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) :
    UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  let A : MeasurableSpace α := m0
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans (zero_le _)⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp only [zero_le', Set.setOf_true, Set.indicator_univ, Pi.zero_apply, hx, condExp_zero]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : ∀ n, μ {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖μ[g|ℱ n] x‖₊} ≤
        eLpNorm μ[g|ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one, ENNReal.rpow_one]
      convert mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top
        (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable C
      · rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne),
      hC, Nonneg.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne, ← mul_assoc, ←
      ENNReal.ofReal_eq_coe_nnreal, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel₀ hδ.ne',
      ENNReal.ofReal_one, one_mul, ENNReal.rpow_one]
    exact eLpNorm_one_condExp_le_eLpNorm _
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condExp.measurable)
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_one_condExp_le_eLpNorm _

section PullOut

-- TODO: this section could be generalized beyond multiplication, to any bounded bilinear map.
/-- Auxiliary lemma for `condExp_mul_of_stronglyMeasurable_left`. -/
theorem condExp_stronglyMeasurable_simpleFunc_mul (hm : m ≤ m0) (f : @SimpleFunc α m ℝ) {g : α → ℝ}
    (hg : Integrable g μ) : μ[(f * g : α → ℝ)|m] =ᵐ[μ] f * μ[g|m] := by
  have : ∀ (s c) (f : α → ℝ), Set.indicator s (Function.const α c) * f = s.indicator (c • f) := by
    intro s c f
    ext1 x
    by_cases hx : x ∈ s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, Algebra.id.smul_eq_mul,
        Function.const_apply]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_notMem, not_false_iff, zero_mul]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise,
      SimpleFunc.coe_const, SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this, this]
    refine (condExp_indicator (hg.smul c) hs).trans ?_
    filter_upwards [condExp_smul c g m] with x hx
    classical simp_rw [Set.indicator_apply, hx]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[⇑(g₁ + g₂) * g|m] =ᵐ[μ] μ[⇑g₁ * g|m] + μ[⇑g₂ * g|m] := by
        rw [h_add, add_mul]; exact condExp_add (hg.simpleFunc_mul' hm _) (hg.simpleFunc_mul' hm _) _
      _ =ᵐ[μ] ⇑g₁ * μ[g|m] + ⇑g₂ * μ[g|m] := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] ⇑(g₁ + g₂) * μ[g|m] := by rw [h_add, add_mul]

theorem condExp_stronglyMeasurable_mul_of_bound (hm : m ≤ m0) [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ x ∂μ, Tendsto (fs · x) atTop (𝓝 (f x)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 ≤ c := by
    rcases hf_bound.exists with ⟨_x, hx⟩
    exact (norm_nonneg _).trans hx
  have hfs_bound : ∀ n x, ‖fs n x‖ ≤ c := hf.norm_approxBounded_le hc
  have : μ[f * μ[g|m]|m] = f * μ[g|m] := by
    refine condExp_of_stronglyMeasurable hm (hf.mul stronglyMeasurable_condExp) ?_
    exact integrable_condExp.bdd_mul' (hf.mono hm).aestronglyMeasurable hf_bound
  rw [← this]
  refine tendsto_condExp_unique (fun n x => fs n x * g x) (fun n x => fs n x * (μ[g|m]) x) (f * g)
    (f * μ[g|m]) ?_ ?_ ?_ ?_ (c * ‖g ·‖) ?_ (c * ‖(μ[g|m]) ·‖) ?_ ?_ ?_ ?_
  · exact fun n => hg.bdd_mul' ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (Eventually.of_forall (hfs_bound n))
  · exact fun n => integrable_condExp.bdd_mul'
      ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (Eventually.of_forall (hfs_bound n))
  · filter_upwards [hfs_tendsto] with x hx
    exact hx.mul tendsto_const_nhds
  · filter_upwards [hfs_tendsto] with x hx
    exact hx.mul tendsto_const_nhds
  · exact hg.norm.const_mul c
  · fun_prop
  · refine fun n => Eventually.of_forall fun x => ?_
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _))
  · refine fun n => Eventually.of_forall fun x => ?_
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _))
  · intro n
    simp_rw [← Pi.mul_apply]
    refine (condExp_stronglyMeasurable_simpleFunc_mul hm _ hg).trans ?_
    rw [condExp_of_stronglyMeasurable hm
      ((SimpleFunc.stronglyMeasurable _).mul stronglyMeasurable_condExp) _]
    exact integrable_condExp.bdd_mul'
      ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (Eventually.of_forall (hfs_bound n))

theorem condExp_stronglyMeasurable_mul_of_bound₀ (hm : m ≤ m0) [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : AEStronglyMeasurable[m] f μ) (hg : Integrable g μ) (c : ℝ)
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  grw [hf.ae_eq_mk]
  refine condExp_stronglyMeasurable_mul_of_bound hm hf.stronglyMeasurable_mk hg c ?_
  filter_upwards [hf_bound, hf.ae_eq_mk] with x hxc hx_eq
  rwa [← hx_eq]

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_stronglyMeasurable_left {f g : α → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  by_cases hm : m ≤ m0; swap; · simp_rw [condExp_of_not_le hm]; rw [mul_zero]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rw [mul_zero]
  haveI : SigmaFinite (μ.trim hm) := hμm
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices ∀ n, ∀ᵐ x ∂μ, x ∈ sets n → (μ[f * g|m]) x = f x * (μ[g|m]) x by
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx
    obtain ⟨i, hi⟩ : ∃ i, x ∈ sets i := by
      have h_mem : x ∈ ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hx i hi
  refine fun n => ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[f * g|m] =ᵐ[μ.restrict (sets n)] f * (μ.restrict (sets n))[g|m] by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    exact this.trans (EventuallyEq.rfl.mul (condExp_restrict_ae_eq_restrict hm (h_meas n) hg))
  suffices (μ.restrict (sets n))[(sets n).indicator f * g|m] =ᵐ[μ.restrict (sets n)]
      (sets n).indicator f * (μ.restrict (sets n))[g|m] by
    refine EventuallyEq.trans ?_ (this.trans ?_)
    · exact
        condExp_congr_ae ((indicator_ae_eq_restrict <| hm _ <| h_meas n).symm.mul EventuallyEq.rfl)
    · exact (indicator_ae_eq_restrict <| hm _ <| h_meas n).mul EventuallyEq.rfl
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_mul_of_bound hm (hf.indicator (h_meas n)) hg.integrableOn n ?_
  filter_upwards with x
  by_cases hxs : x ∈ sets n
  · simpa only [hxs, Set.indicator_of_mem] using h_norm n x hxs
  · simp only [hxs, Set.indicator_of_notMem, not_false_iff, _root_.norm_zero, Nat.cast_nonneg]

/-- Pull-out property of the conditional expectation. -/
lemma condExp_mul_of_stronglyMeasurable_right {f g : α → ℝ} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g := by
  simpa [mul_comm] using condExp_mul_of_stronglyMeasurable_left hg (mul_comm f g ▸ hfg) hf

/-- Pull-out property of the conditional expectation. -/
theorem condExp_mul_of_aestronglyMeasurable_left {f g : α → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  have : μ[f * g|m] =ᵐ[μ] μ[hf.mk f * g|m] :=
    condExp_congr_ae (hf.ae_eq_mk.mul EventuallyEq.rfl)
  refine this.trans ?_
  have : f * μ[g|m] =ᵐ[μ] hf.mk f * μ[g|m] := hf.ae_eq_mk.mul EventuallyEq.rfl
  refine (condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable_mk ?_ hg).trans this.symm
  refine (integrable_congr ?_).mp hfg
  exact hf.ae_eq_mk.mul EventuallyEq.rfl

/-- Pull-out property of the conditional expectation. -/
lemma condExp_mul_of_aestronglyMeasurable_right {f g : α → ℝ} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g := by
  simpa [mul_comm] using condExp_mul_of_aestronglyMeasurable_left hg (mul_comm f g ▸ hfg) hf

end PullOut

end MeasureTheory
