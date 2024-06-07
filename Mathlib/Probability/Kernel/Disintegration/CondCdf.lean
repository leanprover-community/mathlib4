/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.Disintegration.CdfToKernel

#align_import probability.kernel.cond_cdf from "leanprover-community/mathlib"@"3b88f4005dc2e28d42f974cc1ce838f0dafb39b8"

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ennreal.of_real (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

`condCDF` is build from the more general tools about kernel CDFs developed in the file
`Probability.Kernel.Disintegration.CdfToKernel`. In that file, we build a function
`α × β → StieltjesFunction` (which is `α × β → ℝ → ℝ` with additional properties) from a function
`α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some properties like measurability more
easily. Here we apply that construction to the case `β = Unit` and then drop `β` to build
`condCDF : α → StieltjesFunction`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.set_lintegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.IicSnd r s = ρ (s ×ˢ Iic r)`. -/
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
      simp only [Rat.cast_eq_id, id, mem_iInter, mem_prod, mem_Iic]
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

We build towards the definition of `ProbabilityTheory.condCDF`. We first define
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
    Measurable fun a r ↦ (preCDF ρ r a).toReal := by
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

lemma lintegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫⁻ x, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r univ := by
  rw [← set_lintegral_univ, set_lintegral_preCDF_fst ρ r MeasurableSet.univ]

theorem monotone_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r ↦ preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' ↦ ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF
    measurable_preCDF fun s hs _ ↦ ?_
  rw [set_lintegral_preCDF_fst ρ r hs, set_lintegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s
#align probability_theory.monotone_pre_cdf ProbabilityTheory.monotone_preCDF

theorem preCDF_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine fun r ↦ ae_le_of_forall_set_lintegral_le_of_sigmaFinite measurable_preCDF
    measurable_const fun s hs _ ↦ ?_
  rw [set_lintegral_preCDF_fst ρ r hs]
  simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s
#align probability_theory.pre_cdf_le_one ProbabilityTheory.preCDF_le_one

lemma setIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] :
    ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r s).toReal := by
  rw [integral_toReal]
  · rw [set_lintegral_preCDF_fst _ _ hs]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

@[deprecated]
alias set_integral_preCDF_fst :=
  setIntegral_preCDF_fst -- deprecated on 2024-04-17

lemma integral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r univ).toReal := by
  rw [← integral_univ, setIntegral_preCDF_fst ρ _ MeasurableSet.univ]

lemma integrable_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℚ) :
    Integrable (fun a ↦ (preCDF ρ x a).toReal) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ ↦ ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (set_lintegral_le_lintegral _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [preCDF_le_one ρ] with a ha using ENNReal.ofReal_toReal_le.trans (ha _)

lemma isRatCondKernelCDFAux_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDFAux (fun p r ↦ (preCDF ρ r p.2).toReal)
      (kernel.const Unit ρ) (kernel.const Unit ρ.fst) where
  measurable := measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h1 h2
    have h_ne_top : ∀ r, preCDF ρ r a ≠ ∞ := fun r ↦ ((h2 r).trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.toReal_le_toReal (h_ne_top _) (h_ne_top _)]
    exact h1 hrr'
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [kernel.const_apply, forall_const]
    filter_upwards [preCDF_le_one ρ] with a ha
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp [ha]
  tendsto_integral_of_antitone a s _ hs_tendsto := by
    simp_rw [kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atBot MeasurableSet.univ
    rw [← ENNReal.zero_toReal]
    have h0 : Tendsto ENNReal.toReal (𝓝 0) (𝓝 0) :=
      ENNReal.continuousAt_toReal ENNReal.zero_ne_top
    exact h0.comp (h.comp hs_tendsto)
  tendsto_integral_of_monotone a s _ hs_tendsto := by
    simp_rw [kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atTop MeasurableSet.univ
    have h0 : Tendsto ENNReal.toReal (𝓝 (ρ.fst univ)) (𝓝 (ρ.fst univ).toReal) :=
      ENNReal.continuousAt_toReal (measure_ne_top _ _)
    exact h0.comp (h.comp hs_tendsto)
  integrable _ q := integrable_preCDF ρ q
  setIntegral a s hs q := by rw [kernel.const_apply, kernel.const_apply,
    setIntegral_preCDF_fst _ _ hs, Measure.IicSnd_apply _ _ hs]

lemma isRatCondKernelCDF_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDF (fun p r ↦ (preCDF ρ r p.2).toReal)
      (kernel.const Unit ρ) (kernel.const Unit ρ.fst) :=
  (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

#noalign probability_theory.set_lintegral_infi_gt_pre_cdf
#noalign probability_theory.tendsto_lintegral_pre_cdf_at_top
#noalign probability_theory.tendsto_lintegral_pre_cdf_at_bot
#noalign probability_theory.tendsto_pre_cdf_at_top_one
#noalign probability_theory.tendsto_pre_cdf_at_bot_zero
#noalign probability_theory.inf_gt_pre_cdf
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

/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def condCDF (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction :=
  stieltjesOfMeasurableRat (fun a r ↦ (preCDF ρ r a).toReal) measurable_preCDF' a
#align probability_theory.cond_cdf ProbabilityTheory.condCDF

lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × ℝ)) (a : α) :
    condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal)
      (measurable_preCDF'.comp measurable_snd) ((), a) := by
  ext x
  rw [condCDF, ← stieltjesOfMeasurableRat_unit_prod]

lemma isCondKernelCDF_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (kernel.const Unit ρ)
      (kernel.const Unit ρ.fst) := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

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
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r
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

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a ↦ condCDF ρ a x := stronglyMeasurable_stieltjesOfMeasurableRat _ _
#align probability_theory.strongly_measurable_cond_cdf ProbabilityTheory.stronglyMeasurable_condCDF

#noalign probability_theory.set_lintegral_cond_cdf_rat

theorem set_lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).set_lintegral () hs x
#align probability_theory.set_lintegral_cond_cdf ProbabilityTheory.set_lintegral_condCDF

theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).lintegral () x
#align probability_theory.lintegral_cond_cdf ProbabilityTheory.lintegral_condCDF

theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  (isCondKernelCDF_condCDF ρ).integrable () x
#align probability_theory.integrable_cond_cdf ProbabilityTheory.integrable_condCDF

theorem setIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = (ρ (s ×ˢ Iic x)).toReal :=
  (isCondKernelCDF_condCDF ρ).setIntegral () hs x
#align probability_theory.set_integral_cond_cdf ProbabilityTheory.setIntegral_condCDF

@[deprecated]
alias set_integral_condCDF :=
  setIntegral_condCDF -- deprecated on 2024-04-17

theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = (ρ (univ ×ˢ Iic x)).toReal :=
  (isCondKernelCDF_condCDF ρ).integral () x
#align probability_theory.integral_cond_cdf ProbabilityTheory.integral_condCDF

section Measure

theorem measure_condCDF_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _
#align probability_theory.measure_cond_cdf_Iic ProbabilityTheory.measure_condCDF_Iic

theorem measure_condCDF_univ (ρ : Measure (α × ℝ)) (a : α) : (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)
#align probability_theory.measure_cond_cdf_univ ProbabilityTheory.measure_condCDF_univ

instance instIsProbabilityMeasureCondCDF (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
theorem measurable_measure_condCDF (ρ : Measure (α × ℝ)) :
    Measurable fun a => (condCDF ρ a).measure := by
  rw [Measure.measurable_measure]
  refine fun s hs => ?_
  -- Porting note: supplied `C`
  refine MeasurableSpace.induction_on_inter
    (C := fun s => Measurable fun b ↦ StieltjesFunction.measure (condCDF ρ b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic ?_ ?_ ?_ ?_ hs
  · simp only [measure_empty, measurable_const]
  · rintro S ⟨u, rfl⟩
    simp_rw [measure_condCDF_Iic ρ _ u]
    exact (measurable_condCDF ρ u).ennreal_ofReal
  · intro t ht ht_cd_meas
    have :
      (fun a => (condCDF ρ a).measure tᶜ) =
        (fun a => (condCDF ρ a).measure univ) - fun a => (condCDF ρ a).measure t := by
      ext1 a
      rw [measure_compl ht (measure_ne_top (condCDF ρ a).measure _), Pi.sub_apply]
    simp_rw [this, measure_condCDF_univ ρ]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas
#align probability_theory.measurable_measure_cond_cdf ProbabilityTheory.measurable_measure_condCDF

end Measure

end ProbabilityTheory
