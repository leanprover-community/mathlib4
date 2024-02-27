/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.Disintegration.CdfToKernel
import Mathlib.Probability.Kernel.Disintegration.AuxLemmas

#align_import probability.kernel.cond_cdf from "leanprover-community/mathlib"@"3b88f4005dc2e28d42f974cc1ce838f0dafb39b8"

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ennreal.of_real (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.set_lintegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## References

The construction of the conditional cdf in this file follows the proof of Theorem 3.4 in
[O. Kallenberg, Foundations of modern probability][kallenberg2021].

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.Iic_snd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst
#align measure_theory.measure.Iic_snd MeasureTheory.Measure.IicSnd

theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs,
    restrict_apply' (MeasurableSet.univ.prod (measurableSet_Iic : MeasurableSet (Iic r))), ←
    prod_univ, prod_inter_prod, inter_univ, univ_inter]
#align measure_theory.measure.Iic_snd_apply MeasureTheory.Measure.IicSnd_apply

theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ
#align measure_theory.measure.Iic_snd_univ MeasureTheory.Measure.IicSnd_univ

theorem IicSnd_mono {r r' : ℝ} (h_le : r ≤ r') : ρ.IicSnd r ≤ ρ.IicSnd r' := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  simp_rw [IicSnd_apply ρ _ hs]
  refine measure_mono (prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩))
  exact mod_cast h_le
#align measure_theory.measure.Iic_snd_mono MeasureTheory.Measure.IicSnd_mono

theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  simp_rw [fst_apply hs, IicSnd_apply ρ r hs]
  exact measure_mono (prod_subset_preimage_fst _ _)
#align measure_theory.measure.Iic_snd_le_fst MeasureTheory.Measure.IicSnd_le_fst

theorem IicSnd_ac_fst (r : ℝ) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)
#align measure_theory.measure.Iic_snd_ac_fst MeasureTheory.Measure.IicSnd_ac_fst

theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ] (r : ℝ) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)
#align measure_theory.measure.is_finite_measure.Iic_snd MeasureTheory.Measure.IsFiniteMeasure.IicSnd

theorem iInf_IicSnd_gt (t : ℚ) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : ℚ // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]
#align measure_theory.measure.infi_Iic_snd_gt MeasureTheory.Measure.iInf_IicSnd_gt

theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  refine tendsto_measure_iUnion fun r q hr_le_q x ↦ ?_
  simp only [mem_prod, mem_Iic, and_imp]
  refine fun hxs hxr ↦ ⟨hxs, hxr.trans ?_⟩
  exact mod_cast hr_le_q
#align measure_theory.measure.tendsto_Iic_snd_at_top MeasureTheory.Measure.tendsto_IicSnd_atTop

theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  suffices h_neg :
      Tendsto (fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r)))) by
    have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      simp only [Rat.cast_eq_id, id.def, mem_iInter, mem_prod, mem_Iic]
      refine ⟨fun h i ↦ ⟨(h i).1, ?_⟩, fun h i ↦ ⟨(h i).1, ?_⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    have h_fun_eq : (fun r : ℚ ↦ ρ (s ×ˢ Iic (r : ℝ))) = fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(- -r)) := by
      simp_rw [neg_neg]
    rw [h_fun_eq]
    exact h_neg.comp tendsto_neg_atBot_atTop
  refine tendsto_measure_iInter (fun q ↦ hs.prod measurableSet_Iic) ?_ ⟨0, measure_ne_top ρ _⟩
  refine fun q r hqr ↦ prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, fun x hx ↦ ?_⟩)
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine hx.trans (neg_le_neg ?_)
  exact mod_cast hqr
#align measure_theory.measure.tendsto_Iic_snd_at_bot MeasureTheory.Measure.tendsto_IicSnd_atBot

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α}

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd

/-! ### Auxiliary definitions

We build towards the definition of `ProbabilityTheory.cond_cdf`. We first define
`ProbabilityTheory.preCDF`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere.  -/

/-- `preCDF` is the Radon-Nikodym derivative of `ρ.IicSnd` with respect to `ρ.fst` at each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the function `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, right-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allows us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (preCDF q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (preCDF q a)`. -/
noncomputable def preCDF (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst
#align probability_theory.pre_cdf ProbabilityTheory.preCDF

theorem measurable_preCDF {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _
#align probability_theory.measurable_pre_cdf ProbabilityTheory.measurable_preCDF

lemma measurable_preCDF' {ρ : Measure (α × ℝ)} :
    Measurable fun a r ↦ ENNReal.toReal (preCDF ρ r a) := by
    rw [measurable_pi_iff]
    exact fun _ ↦ measurable_preCDF.ennreal_toReal

theorem withDensity_preCDF (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)
#align probability_theory.with_density_pre_cdf ProbabilityTheory.withDensity_preCDF

theorem set_lintegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : ∀ r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, eq_self_iff_true, forall_const]
  rw [this, ← set_lintegral_withDensity_eq_set_lintegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [(_ : (1 : α → ℝ≥0∞) = fun _ ↦ 1)]
    exacts [measurable_const, rfl]
#align probability_theory.set_lintegral_pre_cdf_fst ProbabilityTheory.set_lintegral_preCDF_fst

theorem monotone_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r ↦ preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' ↦ ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF
    measurable_preCDF fun s hs _ ↦ ?_
  rw [set_lintegral_preCDF_fst ρ r hs, set_lintegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s
#align probability_theory.monotone_pre_cdf ProbabilityTheory.monotone_preCDF

theorem set_lintegral_iInf_gt_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (t : ℚ) {s : Set α}
    (hs : MeasurableSet s) : ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst = ρ.IicSnd t s := by
  refine le_antisymm ?_ ?_
  · have h : ∀ q : Ioi t, ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst ≤ ρ.IicSnd q s := by
      intro q
      rw [← set_lintegral_preCDF_fst ρ _ hs]
      refine set_lintegral_mono_ae ?_ measurable_preCDF ?_
      · exact measurable_iInf fun _ ↦ measurable_preCDF
      · filter_upwards [monotone_preCDF _] with a _
        exact fun _ ↦ iInf_le _ q
    calc
      ∫⁻ x in s, ⨅ r : Ioi t, preCDF ρ r x ∂ρ.fst ≤ ⨅ q : Ioi t, ρ.IicSnd q s := le_iInf h
      _ = ρ.IicSnd t s := Measure.iInf_IicSnd_gt ρ t hs
  · rw [(set_lintegral_preCDF_fst ρ t hs).symm]
    refine set_lintegral_mono_ae measurable_preCDF ?_ ?_
    · exact measurable_iInf fun _ ↦ measurable_preCDF
    · filter_upwards [monotone_preCDF _] with a ha_mono
      exact fun _ ↦ le_iInf fun r ↦ ha_mono (le_of_lt r.prop)
#align probability_theory.set_lintegral_infi_gt_pre_cdf ProbabilityTheory.set_lintegral_iInf_gt_preCDF

theorem preCDF_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine fun r ↦ ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF
    measurable_const fun s hs _ ↦ ?_
  rw [set_lintegral_preCDF_fst ρ r hs]
  simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s
#align probability_theory.pre_cdf_le_one ProbabilityTheory.preCDF_le_one

theorem set_integral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] :
    ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r s).toReal := by
  rw [integral_toReal]
  · rw [set_lintegral_preCDF_fst _ _ hs]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

theorem tendsto_lintegral_preCDF_atTop (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r ↦ ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (ρ univ)) := by
  convert ρ.tendsto_IicSnd_atTop MeasurableSet.univ
  · rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ]
  · exact Measure.fst_univ.symm
#align probability_theory.tendsto_lintegral_pre_cdf_at_top ProbabilityTheory.tendsto_lintegral_preCDF_atTop

theorem tendsto_lintegral_preCDF_atBot (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    Tendsto (fun r ↦ ∫⁻ a, preCDF ρ r a ∂ρ.fst) atBot (𝓝 0) := by
  convert ρ.tendsto_IicSnd_atBot MeasurableSet.univ
  rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ]
#align probability_theory.tendsto_lintegral_pre_cdf_at_bot ProbabilityTheory.tendsto_lintegral_preCDF_atBot

theorem tendsto_preCDF_atTop_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r ↦ preCDF ρ r a) atTop (𝓝 1) := by
  -- We show first that `preCDF` has a limit almost everywhere. That limit has to be at most 1.
  -- We then show that the integral of `preCDF` tends to the integral of 1, and that it also tends
  -- to the integral of the limit. Since the limit is at most 1 and has same integral as 1, it is
  -- equal to 1 a.e.
  have h_mono := monotone_preCDF ρ
  have h_le_one := preCDF_le_one ρ
  -- `preCDF` has a limit a.e.
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r ↦ preCDF ρ r a) atTop (𝓝 l) := by
    filter_upwards [h_mono] with a ha_mono
    exact ⟨_, tendsto_atTop_iSup ha_mono⟩
  classical
  -- let `F` be the pointwise limit of `preCDF` where it exists, and 0 elsewhere.
  let F : α → ℝ≥0∞ := fun a ↦
    if h : ∃ l, Tendsto (fun r ↦ preCDF ρ r a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, Tendsto (fun r ↦ preCDF ρ r a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, Tendsto (fun n : ℕ ↦ preCDF ρ n a) atTop (𝓝 (F a)) := by
    filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_nat_cast_atTop_atTop
  have hF_ae_meas : AEMeasurable F ρ.fst := by
    refine aemeasurable_of_tendsto_metrizable_ae _ (fun n ↦ ?_) h_tendsto_ℚ
    exact measurable_preCDF.aemeasurable
  have hF_le_one : ∀ᵐ a ∂ρ.fst, F a ≤ 1 := by
    filter_upwards [h_tendsto_ℚ, h_le_one] with a ha ha_le using le_of_tendsto' ha ha_le
  -- it suffices to show that the limit `F` is 1 a.e.
  suffices ∀ᵐ a ∂ρ.fst, F a = 1 by
    filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq
    rwa [ha_eq] at ha_tendsto
  -- since `F` is at most 1, proving that its integral is the same as the integral of 1 will tell
  -- us that `F` is 1 a.e.
  have h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = ∫⁻ _, 1 ∂ρ.fst := by
    have h_lintegral :
        Tendsto (fun r : ℕ ↦ ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone
        (fun _ ↦ measurable_preCDF.aemeasurable) ?_ h_tendsto_ℕ
      filter_upwards [h_mono] with a ha
      refine fun n m hnm ↦ ha ?_
      exact mod_cast hnm
    have h_lintegral' :
        Tendsto (fun r : ℕ ↦ ∫⁻ a, preCDF ρ r a ∂ρ.fst) atTop (𝓝 (∫⁻ _, 1 ∂ρ.fst)) := by
      rw [lintegral_one, Measure.fst_univ]
      exact (tendsto_lintegral_preCDF_atTop ρ).comp tendsto_nat_cast_atTop_atTop
    exact tendsto_nhds_unique h_lintegral h_lintegral'
  have : ∫⁻ a, 1 - F a ∂ρ.fst = 0 := by
    rw [lintegral_sub' hF_ae_meas _ hF_le_one, h_lintegral_eq, tsub_self]
    calc
      ∫⁻ a, F a ∂ρ.fst = ∫⁻ _, 1 ∂ρ.fst := h_lintegral_eq
      _ = ρ.fst univ := lintegral_one
      _ = ρ univ := Measure.fst_univ
      _ ≠ ∞ := measure_ne_top ρ _
  rw [lintegral_eq_zero_iff' (aemeasurable_const.sub hF_ae_meas)] at this
  filter_upwards [this, hF_le_one] with ha h_one_sub_eq_zero h_le_one
  rw [Pi.zero_apply, tsub_eq_zero_iff_le] at h_one_sub_eq_zero
  exact le_antisymm h_le_one h_one_sub_eq_zero
#align probability_theory.tendsto_pre_cdf_at_top_one ProbabilityTheory.tendsto_preCDF_atTop_one

theorem tendsto_preCDF_atBot_zero (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Tendsto (fun r ↦ preCDF ρ r a) atBot (𝓝 0) := by
  -- We show first that `preCDF` has a limit in ℝ≥0∞ almost everywhere.
  -- We then show that the integral of `preCDF` tends to 0, and that it also tends
  -- to the integral of the limit. Since the limit has integral 0, it is equal to 0 a.e.
  suffices ∀ᵐ a ∂ρ.fst, Tendsto (fun r ↦ preCDF ρ (-r) a) atTop (𝓝 0) by
    filter_upwards [this] with a ha
    have h_eq_neg : (fun r : ℚ ↦ preCDF ρ r a) = fun r : ℚ ↦ preCDF ρ (- -r) a := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ha.comp tendsto_neg_atBot_atTop
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, Tendsto (fun r ↦ preCDF ρ (-r) a) atTop (𝓝 l) := by
    filter_upwards [monotone_preCDF ρ] with a ha
    have h_anti : Antitone fun r ↦ preCDF ρ (-r) a := fun p q hpq ↦ ha (neg_le_neg hpq)
    exact ⟨_, tendsto_atTop_iInf h_anti⟩
  classical
  let F : α → ℝ≥0∞ := fun a ↦
    if h : ∃ l, Tendsto (fun r ↦ preCDF ρ (-r) a) atTop (𝓝 l) then h.choose else 0
  have h_tendsto : ∀ᵐ a ∂ρ.fst, Tendsto (fun r ↦ preCDF ρ (-r) a) atTop (𝓝 (F a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [dif_pos ha]
    exact ha.choose_spec
  suffices h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = 0 by
    have hF_ae_meas : AEMeasurable F ρ.fst := by
      refine aemeasurable_of_tendsto_metrizable_ae _ (fun n ↦ ?_) h_tendsto
      exact measurable_preCDF.aemeasurable
    rw [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq
    filter_upwards [h_tendsto, h_lintegral_eq] with a ha_tendsto ha_eq
    rwa [ha_eq] at ha_tendsto
  have h_lintegral :
      Tendsto (fun r ↦ ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst) atTop (𝓝 (∫⁻ a, F a ∂ρ.fst)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ 1)
      (eventually_of_forall fun _ ↦ measurable_preCDF) (eventually_of_forall fun _ ↦ ?_) ?_
      h_tendsto
    · filter_upwards [preCDF_le_one ρ] with a ha using ha _
    · rw [lintegral_one]
      exact measure_ne_top _ _
  have h_lintegral' : Tendsto (fun r ↦ ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst) atTop (𝓝 0) := by
    have h_lintegral_eq : (fun r ↦ ∫⁻ a, preCDF ρ (-r) a ∂ρ.fst)
        = fun r : ℚ ↦ ρ (univ ×ˢ Iic (-r : ℝ)) := by
      ext1 n
      rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ _ MeasurableSet.univ,
        Measure.IicSnd_univ]
      norm_cast
    rw [h_lintegral_eq]
    have h_zero_eq_measure_iInter : (0 : ℝ≥0∞) = ρ (⋂ r : ℚ, univ ×ˢ Iic (-r : ℝ)) := by
      suffices ⋂ r : ℚ, Iic (-(r : ℝ)) = ∅ by rw [← prod_iInter, this, prod_empty, measure_empty]
      ext1 x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false_iff, not_forall, not_le]
      simp_rw [neg_lt]
      exact exists_rat_gt _
    rw [h_zero_eq_measure_iInter]
    refine tendsto_measure_iInter (fun n ↦ MeasurableSet.univ.prod measurableSet_Iic)
        (fun i j hij x ↦ ?_) ⟨0, measure_ne_top ρ _⟩
    simp only [mem_prod, mem_univ, mem_Iic, true_and_iff]
    refine fun hxj ↦ hxj.trans (neg_le_neg ?_)
    exact mod_cast hij
  exact tendsto_nhds_unique h_lintegral h_lintegral'
#align probability_theory.tendsto_pre_cdf_at_bot_zero ProbabilityTheory.tendsto_preCDF_atBot_zero

theorem inf_gt_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ t : ℚ, ⨅ r : Ioi t, preCDF ρ r a = preCDF ρ t a := by
  rw [ae_all_iff]
  refine fun t ↦ ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite ?_ measurable_preCDF ?_
  · exact measurable_iInf fun i ↦ measurable_preCDF
  intro s hs _
  rw [set_lintegral_iInf_gt_preCDF ρ t hs, set_lintegral_preCDF_fst ρ t hs]
#align probability_theory.inf_gt_pre_cdf ProbabilityTheory.inf_gt_preCDF

#noalign probability_theory.has_cond_cdf
#noalign probability_theory.has_cond_cdf_ae
#noalign probability_theory.cond_cdf_set
#noalign probability_theory.measurable_set_cond_cdf_set
#noalign probability_theory.has_cond_cdf_of_mem_cond_cdf_set
#noalign probability_theory.mem_cond_cdf_set_ae
#noalign probability_theory.cond_cdf_rat
#noalign probability_theory.cond_cdf_rat_of_not_mem
#noalign probability_theory.cond_cdf_rat_of_mem
#noalign probability_theory.monotone_cond_cdf_rat
#noalign probability_theory.measurable_cond_cdf_rat
#noalign probability_theory.cond_cdf_rat_nonneg
#noalign probability_theory.cond_cdf_rat_le_one
#noalign probability_theory.tendsto_cond_cdf_rat_at_bot
#noalign probability_theory.tendsto_cond_cdf_rat_at_top
#noalign probability_theory.cond_cdf_rat_ae_eq
#noalign probability_theory.of_real_cond_cdf_rat_ae_eq
#noalign probability_theory.inf_gt_cond_cdf_rat
#noalign probability_theory.cond_cdf'
#noalign probability_theory.cond_cdf'_def
#noalign probability_theory.cond_cdf'_eq_cond_cdf_rat
#noalign probability_theory.cond_cdf'_nonneg
#noalign probability_theory.bdd_below_range_cond_cdf_rat_gt
#noalign probability_theory.monotone_cond_cdf'
#noalign probability_theory.continuous_within_at_cond_cdf'_Ici

/-! ### Conditional cdf -/

lemma isRatStieltjesPoint_ae (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, IsRatStieltjesPoint (fun a r ↦ (preCDF ρ r a).toReal) a := by
  filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ, tendsto_preCDF_atTop_one ρ,
    tendsto_preCDF_atBot_zero ρ, inf_gt_preCDF ρ] with a h1 h2 h3 h4 h5
  constructor
  · intro r r' hrr'
    have h_ne_top : ∀ r, preCDF ρ r a ≠ ∞ := fun r ↦ ((h2 r).trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.toReal_le_toReal (h_ne_top _) (h_ne_top _)]
    exact h1 hrr'
  · rw [← ENNReal.one_toReal, ENNReal.tendsto_toReal_iff]
    · exact h3
    · exact fun r ↦ ((h2 r).trans_lt ENNReal.one_lt_top).ne
    · exact ENNReal.one_ne_top
  · rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff]
    · exact h4
    · exact fun r ↦ ((h2 r).trans_lt ENNReal.one_lt_top).ne
    · exact ENNReal.zero_ne_top
  · intro q
    rw [← ENNReal.toReal_iInf]
    · suffices ⨅ i : ↥(Ioi q), preCDF ρ (↑i) a = preCDF ρ q a by rw [this]
      rw [← h5]
    · exact fun r ↦ ((h2 r).trans_lt ENNReal.one_lt_top).ne

theorem integrable_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℚ) :
    Integrable (fun a ↦ (preCDF ρ x a).toReal) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ ↦ ?_
  · exact  measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (set_lintegral_le_lintegral _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [preCDF_le_one ρ] with a ha using ENNReal.ofReal_toReal_le.trans (ha _)

lemma isRatCondKernelCDF_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDF (fun p r ↦ (preCDF ρ r p.2).toReal)
      (kernel.const Unit ρ) (kernel.const Unit ρ.fst) where
  measurable := measurable_preCDF'.comp measurable_snd
  isRatStieltjesPoint_ae a := by
    filter_upwards [isRatStieltjesPoint_ae ρ] with a ha
    exact ⟨ha.mono, ha.tendsto_atTop_one, ha.tendsto_atBot_zero, ha.iInf_rat_gt_eq⟩
  integrable _ q := integrable_preCDF ρ q
  set_integral a s hs q := by rw [kernel.const_apply, kernel.const_apply, set_integral_preCDF_fst _ _ hs,
    Measure.IicSnd_apply _ _ hs]

/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def condCDF (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction :=
  stieltjesOfMeasurableRat (fun a r ↦ (preCDF ρ r a).toReal) measurable_preCDF' a
#align probability_theory.cond_cdf ProbabilityTheory.condCDF

lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × ℝ)) (a : α) :
    condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal)
      (measurable_preCDF'.comp measurable_snd) ((), a) := by
  ext x
  rw [condCDF, ← stieltjesOfMeasurableRat_unit_prod]

#noalign probability_theory.cond_cdf_eq_cond_cdf_rat

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem condCDF_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCDF ρ a r :=
  stieltjesOfMeasurableRat_nonneg _ a r
#align probability_theory.cond_cdf_nonneg ProbabilityTheory.condCDF_nonneg

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem condCDF_le_one (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) : condCDF ρ a x ≤ 1 :=
  stieltjesOfMeasurableRat_le_one _ _ _
#align probability_theory.cond_cdf_le_one ProbabilityTheory.condCDF_le_one

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_condCDF_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) := tendsto_stieltjesOfMeasurableRat_atBot _ _
#align probability_theory.tendsto_cond_cdf_at_bot ProbabilityTheory.tendsto_condCDF_atBot

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_condCDF_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) := tendsto_stieltjesOfMeasurableRat_atTop _ _
#align probability_theory.tendsto_cond_cdf_at_top ProbabilityTheory.tendsto_condCDF_atTop

theorem condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ condCDF ρ a r) =ᵐ[ρ.fst] fun a ↦ (preCDF ρ r a).toReal := by
  filter_upwards [isRatStieltjesPoint_ae ρ] with a ha
  rw [condCDF, stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint ha]
#align probability_theory.cond_cdf_ae_eq ProbabilityTheory.condCDF_ae_eq

theorem ofReal_condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha, ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne
#align probability_theory.of_real_cond_cdf_ae_eq ProbabilityTheory.ofReal_condCDF_ae_eq

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) : Measurable fun a ↦ condCDF ρ a x :=
  measurable_stieltjesOfMeasurableRat _ _
#align probability_theory.measurable_cond_cdf ProbabilityTheory.measurable_condCDF

#noalign probability_theory.set_lintegral_cond_cdf_rat

theorem set_lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) := by
  have h := set_lintegral_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ) () x hs
  simp only [kernel.const_apply] at h
  rw [← h]
  congr with a
  congr
  exact condCDF_eq_stieltjesOfMeasurableRat_unit_prod _ _
#align probability_theory.set_lintegral_cond_cdf ProbabilityTheory.set_lintegral_condCDF

theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) := by
  rw [← set_lintegral_univ, set_lintegral_condCDF ρ _ MeasurableSet.univ]
#align probability_theory.lintegral_cond_cdf ProbabilityTheory.lintegral_condCDF

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a ↦ condCDF ρ a x := stronglyMeasurable_stieltjesOfMeasurableRat _ _
#align probability_theory.strongly_measurable_cond_cdf ProbabilityTheory.stronglyMeasurable_condCDF

theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ ↦ ?_
  · exact (stronglyMeasurable_condCDF ρ _).aestronglyMeasurable
  · have : ∀ y, (‖condCDF ρ y x‖₊ : ℝ≥0∞) ≤ 1 := by
      intro y
      rw [Real.nnnorm_of_nonneg (condCDF_nonneg _ _ _)]
      -- Porting note: was exact_mod_cast condCDF_le_one _ _ _
      simp only [ENNReal.coe_le_one_iff]
      exact condCDF_le_one _ _ _
    refine
      (set_lintegral_mono (measurable_condCDF _ _).ennnorm measurable_one fun y _ ↦ this y).trans
        ?_
    simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
    exact measure_mono (subset_univ _)
#align probability_theory.integrable_cond_cdf ProbabilityTheory.integrable_condCDF

theorem set_integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = (ρ (s ×ˢ Iic x)).toReal := by
  have h := set_lintegral_condCDF ρ x hs
  rw [← ofReal_integral_eq_lintegral_ofReal] at h
  · rw [← h, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ ↦ condCDF_nonneg _ _ _
  · exact (integrable_condCDF _ _).integrableOn
  · exact eventually_of_forall fun _ ↦ condCDF_nonneg _ _ _
#align probability_theory.set_integral_cond_cdf ProbabilityTheory.set_integral_condCDF

theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = (ρ (univ ×ˢ Iic x)).toReal := by
  rw [← set_integral_condCDF ρ _ MeasurableSet.univ, Measure.restrict_univ]
#align probability_theory.integral_cond_cdf ProbabilityTheory.integral_condCDF

lemma isCondKernelCDF_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (kernel.const Unit ρ)
      (kernel.const Unit ρ.fst) where
  measurable x := (measurable_condCDF ρ x).comp measurable_snd
  integrable _ x := integrable_condCDF ρ x
  tendsto_atTop_one p := tendsto_condCDF_atTop ρ p.2
  tendsto_atBot_zero p := tendsto_condCDF_atBot ρ p.2
  set_integral _ _ hs x := set_integral_condCDF ρ x hs

#noalign probability_theory.measure_cond_cdf_Iic
#noalign probability_theory.measure_cond_cdf_univ
#noalign probability_theory.measurable_measure_cond_cdf

end ProbabilityTheory
