/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

#align_import measure_theory.function.conditional_expectation.real from "leanprover-community/mathlib"@"b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f"

/-!

# Conditional expectation of real-valued functions

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `MeasureTheory.rnDeriv_ae_eq_condexp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `MeasureTheory.Integrable.uniformIntegrable_condexp`: the conditional expectation of a function
  form a uniformly integrable class.
* `MeasureTheory.condexp_stronglyMeasurable_mul`: the pull-out property of the conditional
  expectation.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology BigOperators MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

theorem rnDeriv_ae_eq_condexp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ}
    (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f|m] := by
  refine' ae_eq_condexp_of_forall_set_integral_eq hm hf _ _ _
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm)) hs,
      ← set_integral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact StronglyMeasurable.aeStronglyMeasurable'
      (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
#align measure_theory.rn_deriv_ae_eq_condexp MeasureTheory.rnDeriv_ae_eq_condexp

-- TODO: the following couple of lemmas should be generalized and proved using Jensen's inequality
-- for the conditional expectation (not in mathlib yet) .
theorem snorm_one_condexp_le_snorm (f : α → ℝ) : snorm (μ[f|m]) 1 μ ≤ snorm f 1 μ := by
  by_cases hf : Integrable f μ
  swap; · rw [condexp_undef hf, snorm_zero]; exact zero_le _
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm, snorm_zero]; exact zero_le _
  by_cases hsig : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hsig, snorm_zero]; exact zero_le _
  calc
    snorm (μ[f|m]) 1 μ ≤ snorm (μ[(|f|)|m]) 1 μ := by
      refine' snorm_mono_ae _
      filter_upwards [@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf hf.abs
        (@ae_of_all _ m0 _ μ (fun x => le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
        EventuallyLE.trans (condexp_neg f).symm.le
          (@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf.neg hf.abs
          (@ae_of_all _ m0 _ μ (fun x => neg_le_abs_self (f x): ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂
      exact abs_le_abs hx₁ hx₂
    _ = snorm f 1 μ := by
      rw [snorm_one_eq_lintegral_nnnorm, snorm_one_eq_lintegral_nnnorm, ←
        ENNReal.toReal_eq_toReal (ne_of_lt integrable_condexp.2) (ne_of_lt hf.2), ←
        integral_norm_eq_lintegral_nnnorm
          (stronglyMeasurable_condexp.mono hm).aestronglyMeasurable,
        ← integral_norm_eq_lintegral_nnnorm hf.1]
      simp_rw [Real.norm_eq_abs]
      rw [← @integral_condexp _ _ _ _ _ m m0 μ _ hm hsig hf.abs]
      refine' integral_congr_ae _
      have : 0 ≤ᵐ[μ] μ[(|f|)|m] := by
        rw [← @condexp_zero α ℝ _ _ _ m m0 μ]
        exact condexp_mono (integrable_zero _ _ _) hf.abs
          (@ae_of_all _ m0 _ μ (fun x => abs_nonneg (f x) : ∀ x, 0 ≤ |f x|))
      filter_upwards [this] with x hx
      exact abs_eq_self.2 hx
#align measure_theory.snorm_one_condexp_le_snorm MeasureTheory.snorm_one_condexp_le_snorm

theorem integral_abs_condexp_le (f : α → ℝ) : ∫ x, |(μ[f|m]) x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  by_cases hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm, Pi.zero_apply, abs_zero, integral_zero]
    exact integral_nonneg fun x => abs_nonneg _
  by_cases hfint : Integrable f μ
  swap
  · simp only [condexp_undef hfint, Pi.zero_apply, abs_zero, integral_const, Algebra.id.smul_eq_mul,
      mul_zero]
    exact integral_nonneg fun x => abs_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  · rw [ENNReal.toReal_le_toReal] <;> simp_rw [← Real.norm_eq_abs, ofReal_norm_eq_coe_nnnorm]
    · rw [← snorm_one_eq_lintegral_nnnorm, ← snorm_one_eq_lintegral_nnnorm]
      exact snorm_one_condexp_le_snorm _
    · exact ne_of_lt integrable_condexp.2
    · exact ne_of_lt hfint.2
  · exact eventually_of_forall fun x => abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact hfint.1.norm
  · exact eventually_of_forall fun x => abs_nonneg _
  · simp_rw [← Real.norm_eq_abs]
    exact (stronglyMeasurable_condexp.mono hm).aestronglyMeasurable.norm
#align measure_theory.integral_abs_condexp_le MeasureTheory.integral_abs_condexp_le

theorem set_integral_abs_condexp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → ℝ) :
    ∫ x in s, |(μ[f|m]) x| ∂μ ≤ ∫ x in s, |f x| ∂μ := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hnm, Pi.zero_apply, abs_zero, integral_zero]
    exact integral_nonneg fun x => abs_nonneg _
  by_cases hfint : Integrable f μ
  swap
  · simp only [condexp_undef hfint, Pi.zero_apply, abs_zero, integral_const, Algebra.id.smul_eq_mul,
      mul_zero]
    exact integral_nonneg fun x => abs_nonneg _
  have : ∫ x in s, |(μ[f|m]) x| ∂μ = ∫ x, |(μ[s.indicator f|m]) x| ∂μ := by
    rw [← integral_indicator]
    swap; · exact hnm _ hs
    refine' integral_congr_ae _
    have : (fun x => |(μ[s.indicator f|m]) x|) =ᵐ[μ] fun x => |s.indicator (μ[f|m]) x| :=
      EventuallyEq.fun_comp (condexp_indicator hfint hs) _
    refine' EventuallyEq.trans (eventually_of_forall fun x => _) this.symm
    rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    rfl
  rw [this, ← integral_indicator]
  swap; · exact hnm _ hs
  refine' (integral_abs_condexp_le _).trans
    (le_of_eq <| integral_congr_ae <| eventually_of_forall fun x => _)
  simp_rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
#align measure_theory.set_integral_abs_condexp_le MeasureTheory.set_integral_abs_condexp_le

/-- If the real valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
theorem ae_bdd_condexp_of_ae_bdd {R : ℝ≥0} {f : α → ℝ} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |(μ[f|m]) x| ≤ R := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hnm, Pi.zero_apply, abs_zero]
    refine' eventually_of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condexp_undef hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ ≠ 0 at h
  simp only [← zero_lt_iff, Set.compl_def, Set.mem_setOf_eq, not_le] at h
  suffices (μ {x | ↑R < |(μ[f|m]) x|}).toReal * ↑R < (μ {x | ↑R < |(μ[f|m]) x|}).toReal * ↑R by
    exact this.ne rfl
  refine' lt_of_lt_of_le (set_integral_gt_gt R.coe_nonneg _ _ h.ne.symm) _
  · simp_rw [← Real.norm_eq_abs]
    exact (stronglyMeasurable_condexp.mono hnm).measurable.norm
  · exact integrable_condexp.abs.integrableOn
  refine' (set_integral_abs_condexp_le _ _).trans _
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condexp.norm.measurable
  simp only [← smul_eq_mul, ← set_integral_const, NNReal.val_eq_coe, IsROrC.ofReal_real_eq_id,
    id.def]
  refine' set_integral_mono_ae hfint.abs.integrableOn _ _
  · refine' ⟨aestronglyMeasurable_const, lt_of_le_of_lt _
      (integrable_condexp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
    refine' set_lintegral_mono (Measurable.nnnorm _).coe_nnreal_ennreal
      (stronglyMeasurable_condexp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => _
    · exact measurable_const
    · rw [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg R.coe_nonneg]
      exact Subtype.mk_le_mk.2 (le_of_lt hx)
  · exact hbdd
#align measure_theory.ae_bdd_condexp_of_ae_bdd MeasureTheory.ae_bdd_condexp_of_ae_bdd

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
theorem Integrable.uniformIntegrable_condexp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) :
    UniformIntegrable (fun i => μ[g|ℱ i]) 1 μ := by
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condexp.mono (hℱ n)).measurable.nnnorm
  have hg : Memℒp g 1 μ := memℒp_one_iff_integrable.2 hint
  refine' uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condexp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => _
  by_cases hne : snorm g 1 μ = 0
  · rw [snorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine' ⟨0, fun n => (le_of_eq <|
      (snorm_eq_zero_iff ((stronglyMeasurable_condexp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 _).trans (zero_le _)⟩
    filter_upwards [@condexp_congr_ae _ _ _ _ _ (ℱ n) m0 μ _ _ hne] with x hx
    simp only [zero_le', Set.setOf_true, Set.indicator_univ, Pi.zero_apply, hx, condexp_zero]
  obtain ⟨δ, hδ, h⟩ := hg.snorm_indicator_le μ le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (snorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.snorm_lt_top.ne)
  have : ∀ n, μ {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
    intro n
    have := mul_meas_ge_le_pow_snorm' μ one_ne_zero ENNReal.one_ne_top
      ((@stronglyMeasurable_condexp _ _ _ _ _ (ℱ n) _ μ g).mono (hℱ n)).aestronglyMeasurable C
    rw [ENNReal.one_toReal, ENNReal.rpow_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne.symm))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine' this.trans _
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne.symm))
        (Or.inl ENNReal.coe_lt_top.ne),
      hC, Nonneg.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.snorm_lt_top.ne, ← mul_assoc, ←
      ENNReal.ofReal_eq_coe_nnreal, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel hδ.ne.symm,
      ENNReal.ofReal_one, one_mul]
    exact snorm_one_condexp_le_snorm _
  refine' ⟨C, fun n => le_trans _ (h {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condexp.measurable)
  rw [← snorm_congr_ae (condexp_indicator hint hmeasℱ)]
  exact snorm_one_condexp_le_snorm _
#align measure_theory.integrable.uniform_integrable_condexp MeasureTheory.Integrable.uniformIntegrable_condexp

section PullOut

-- TODO: this section could be generalized beyond multiplication, to any bounded bilinear map.
/-- Auxiliary lemma for `condexp_stronglyMeasurable_mul`. -/
theorem condexp_stronglyMeasurable_simpleFunc_mul (hm : m ≤ m0) (f : @SimpleFunc α m ℝ) {g : α → ℝ}
    (hg : Integrable g μ) : μ[(f * g : α → ℝ)|m] =ᵐ[μ] f * μ[g|m] := by
  have : ∀ (s c) (f : α → ℝ), Set.indicator s (Function.const α c) * f = s.indicator (c • f) := by
    intro s c f
    ext1 x
    by_cases hx : x ∈ s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, Algebra.id.smul_eq_mul]; rfl
    · simp only [hx, Pi.mul_apply, Set.indicator_of_not_mem, not_false_iff, zero_mul]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · -- Porting note: if not classical, `DecidablePred fun x ↦ x ∈ s` cannot be synthesised
    -- for `Set.piecewise_eq_indicator`
    classical simp only [@SimpleFunc.const_zero _ _ m, @SimpleFunc.coe_piecewise _ _ m,
      @SimpleFunc.coe_const _ _ m, @SimpleFunc.coe_zero _ _ m, Set.piecewise_eq_indicator]
    rw [this, this]
    refine' (condexp_indicator (hg.smul c) hs).trans _
    filter_upwards [@condexp_smul α ℝ ℝ _ _ _ _ _ m m0 μ c g] with x hx
    classical simp_rw [Set.indicator_apply, hx]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[⇑(g₁ + g₂) * g|m] =ᵐ[μ] μ[(⇑g₁ + ⇑g₂) * g|m] := by
        refine' condexp_congr_ae (EventuallyEq.mul _ EventuallyEq.rfl); rw [h_add]
      _ =ᵐ[μ] μ[⇑g₁ * g|m] + μ[⇑g₂ * g|m] := by
        rw [add_mul]; exact condexp_add (hg.simpleFunc_mul' hm _) (hg.simpleFunc_mul' hm _)
      _ =ᵐ[μ] ⇑g₁ * μ[g|m] + ⇑g₂ * μ[g|m] := (EventuallyEq.add h_eq₁ h_eq₂)
      _ =ᵐ[μ] ⇑(g₁ + g₂) * μ[g|m] := by rw [h_add, add_mul]
#align measure_theory.condexp_strongly_measurable_simple_func_mul MeasureTheory.condexp_stronglyMeasurable_simpleFunc_mul

theorem condexp_stronglyMeasurable_mul_of_bound (hm : m ≤ m0) [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : ℝ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  let fs := hf.approxBounded c
  have hfs_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : μ.ae.NeBot := by simp only [hμ, ae_neBot, Ne.def, not_false_iff]
  have hc : 0 ≤ c :=
    haveI h_exists : ∃ x, ‖f x‖ ≤ c := Eventually.exists hf_bound
    (norm_nonneg _).trans h_exists.choose_spec
  have hfs_bound : ∀ n x, ‖fs n x‖ ≤ c := hf.norm_approxBounded_le hc
  have : μ[f * μ[g|m]|m] = f * μ[g|m] := by
    refine' condexp_of_stronglyMeasurable hm (hf.mul stronglyMeasurable_condexp) _
    exact integrable_condexp.bdd_mul' (hf.mono hm).aestronglyMeasurable hf_bound
  rw [← this]
  refine' tendsto_condexp_unique (fun n x => fs n x * g x) (fun n x => fs n x * (μ[g|m]) x) (f * g)
    (f * μ[g|m]) _ _ _ _ (fun x => c * ‖g x‖) _ (fun x => c * ‖(μ[g|m]) x‖) _ _ _ _
  · exact fun n => hg.bdd_mul' ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (eventually_of_forall (hfs_bound n))
  · exact fun n => integrable_condexp.bdd_mul'
      ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (eventually_of_forall (hfs_bound n))
  · filter_upwards [hfs_tendsto] with x hx
    rw [Pi.mul_apply]
    exact Tendsto.mul hx tendsto_const_nhds
  · filter_upwards [hfs_tendsto] with x hx
    rw [Pi.mul_apply]
    exact Tendsto.mul hx tendsto_const_nhds
  · exact hg.norm.const_mul c
  · exact integrable_condexp.norm.const_mul c
  · refine' fun n => eventually_of_forall fun x => _
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _))
  · refine' fun n => eventually_of_forall fun x => _
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hfs_bound n x) (norm_nonneg _))
  · intro n
    simp_rw [← Pi.mul_apply]
    refine' (condexp_stronglyMeasurable_simpleFunc_mul hm _ hg).trans _
    rw [condexp_of_stronglyMeasurable hm
      ((SimpleFunc.stronglyMeasurable _).mul stronglyMeasurable_condexp) _]
    exact integrable_condexp.bdd_mul'
      ((SimpleFunc.stronglyMeasurable (fs n)).mono hm).aestronglyMeasurable
      (eventually_of_forall (hfs_bound n))
#align measure_theory.condexp_strongly_measurable_mul_of_bound MeasureTheory.condexp_stronglyMeasurable_mul_of_bound

theorem condexp_stronglyMeasurable_mul_of_bound₀ (hm : m ≤ m0) [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : AEStronglyMeasurable' m f μ) (hg : Integrable g μ) (c : ℝ)
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  have : μ[f * g|m] =ᵐ[μ] μ[hf.mk f * g|m] :=
    condexp_congr_ae (EventuallyEq.mul hf.ae_eq_mk EventuallyEq.rfl)
  refine' this.trans _
  have : f * μ[g|m] =ᵐ[μ] hf.mk f * μ[g|m] := EventuallyEq.mul hf.ae_eq_mk EventuallyEq.rfl
  refine' EventuallyEq.trans _ this.symm
  refine' condexp_stronglyMeasurable_mul_of_bound hm hf.stronglyMeasurable_mk hg c _
  filter_upwards [hf_bound, hf.ae_eq_mk] with x hxc hx_eq
  rw [← hx_eq]
  exact hxc
#align measure_theory.condexp_strongly_measurable_mul_of_bound₀ MeasureTheory.condexp_stronglyMeasurable_mul_of_bound₀

/-- Pull-out property of the conditional expectation. -/
theorem condexp_stronglyMeasurable_mul {f g : α → ℝ} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  by_cases hm : m ≤ m0; swap; · simp_rw [condexp_of_not_le hm]; rw [mul_zero]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rw [mul_zero]
  haveI : SigmaFinite (μ.trim hm) := hμm
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices ∀ n, ∀ᵐ x ∂μ, x ∈ sets n → (μ[f * g|m]) x = f x * (μ[g|m]) x by
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx
    rw [Pi.mul_apply]
    obtain ⟨i, hi⟩ : ∃ i, x ∈ sets i := by
      have h_mem : x ∈ ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hx i hi
  refine' fun n => ae_imp_of_ae_restrict _
  suffices (μ.restrict (sets n))[f * g|m] =ᵐ[μ.restrict (sets n)] f * (μ.restrict (sets n))[g|m] by
    simp_rw [← Pi.mul_apply]
    refine' (condexp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans _
    exact this.trans (EventuallyEq.rfl.mul (condexp_restrict_ae_eq_restrict hm (h_meas n) hg))
  suffices (μ.restrict (sets n))[(sets n).indicator f * g|m] =ᵐ[μ.restrict (sets n)]
      (sets n).indicator f * (μ.restrict (sets n))[g|m] by
    refine' EventuallyEq.trans _ (this.trans _)
    · exact
        condexp_congr_ae ((indicator_ae_eq_restrict (hm _ (h_meas n))).symm.mul EventuallyEq.rfl)
    · exact (indicator_ae_eq_restrict (hm _ (h_meas n))).mul EventuallyEq.rfl
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine' condexp_stronglyMeasurable_mul_of_bound hm (hf.indicator (h_meas n)) hg.integrableOn n _
  refine' eventually_of_forall fun x => _
  by_cases hxs : x ∈ sets n
  · simp only [hxs, Set.indicator_of_mem]
    exact h_norm n x hxs
  · simp only [hxs, Set.indicator_of_not_mem, not_false_iff, _root_.norm_zero, Nat.cast_nonneg]
#align measure_theory.condexp_strongly_measurable_mul MeasureTheory.condexp_stronglyMeasurable_mul

/-- Pull-out property of the conditional expectation. -/
theorem condexp_stronglyMeasurable_mul₀ {f g : α → ℝ} (hf : AEStronglyMeasurable' m f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g|m] =ᵐ[μ] f * μ[g|m] := by
  have : μ[f * g|m] =ᵐ[μ] μ[hf.mk f * g|m] :=
    condexp_congr_ae (EventuallyEq.mul hf.ae_eq_mk EventuallyEq.rfl)
  refine' this.trans _
  have : f * μ[g|m] =ᵐ[μ] hf.mk f * μ[g|m] := EventuallyEq.mul hf.ae_eq_mk EventuallyEq.rfl
  refine' EventuallyEq.trans _ this.symm
  refine' condexp_stronglyMeasurable_mul hf.stronglyMeasurable_mk _ hg
  refine' (integrable_congr _).mp hfg
  exact EventuallyEq.mul hf.ae_eq_mk EventuallyEq.rfl
#align measure_theory.condexp_strongly_measurable_mul₀ MeasureTheory.condexp_stronglyMeasurable_mul₀

end PullOut

end MeasureTheory
