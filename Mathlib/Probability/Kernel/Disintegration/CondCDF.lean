/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Disintegration.CDFToKernel

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

`condCDF` is build from the more general tools about kernel CDFs developed in the file
`Probability.Kernel.Disintegration.CDFToKernel`. In that file, we build a function
`α × β → StieltjesFunction` (which is `α × β → ℝ → ℝ` with additional properties) from a function
`α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some properties like measurability more
easily. Here we apply that construction to the case `β = Unit` and then drop `β` to build
`condCDF : α → StieltjesFunction`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.setLIntegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.IicSnd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst

theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs, restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic),
    univ_prod, Set.prod_eq]

theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]
theorem IicSnd_mono {r r' : ℝ} (h_le : r ≤ r') : ρ.IicSnd r ≤ ρ.IicSnd r' := by
  unfold IicSnd; gcongr

theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst :=
  fst_mono restrict_le_self

theorem IicSnd_ac_fst (r : ℝ) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)

theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ] (r : ℝ) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)

theorem iInf_IicSnd_gt (t : ℚ) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : ℚ // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]

theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic

theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  suffices h_neg :
      Tendsto (fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r)))) by
    have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      simp only [mem_iInter, mem_prod, mem_Iic]
      refine ⟨fun h i ↦ ⟨(h i).1, ?_⟩, fun h i ↦ ⟨(h i).1, ?_⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    have h_fun_eq : (fun r : ℚ ↦ ρ (s ×ˢ Iic (r : ℝ))) = fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(- -r)) := by
      simp_rw [neg_neg]
    rw [h_fun_eq]
    exact h_neg.comp tendsto_neg_atBot_atTop
  refine tendsto_measure_iInter_atTop (fun q ↦ (hs.prod measurableSet_Iic).nullMeasurableSet)
    ?_ ⟨0, measure_ne_top ρ _⟩
  refine fun q r hqr ↦ Set.prod_mono subset_rfl fun x hx ↦ ?_
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine hx.trans (neg_le_neg ?_)
  exact mod_cast hqr

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd

/-! ### Auxiliary definitions

We build towards the definition of `ProbabilityTheory.condCDF`. We first define
`ProbabilityTheory.preCDF`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere. -/

/-- `preCDF` is the Radon-Nikodym derivative of `ρ.IicSnd` with respect to `ρ.fst` at each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the function `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, right-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allows us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (preCDF q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (preCDF q a)`. -/
noncomputable def preCDF (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst

theorem measurable_preCDF {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _

lemma measurable_preCDF' {ρ : Measure (α × ℝ)} :
    Measurable fun a r ↦ (preCDF ρ r a).toReal := by
  rw [measurable_pi_iff]
  exact fun _ ↦ measurable_preCDF.ennreal_toReal

theorem withDensity_preCDF (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)

theorem setLIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : ∀ r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, forall_const]
  rw [this, ← setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [Pi.one_def]
    exact measurable_const

lemma lintegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫⁻ x, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r univ := by
  rw [← setLIntegral_univ, setLIntegral_preCDF_fst ρ r MeasurableSet.univ]

theorem monotone_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r ↦ preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs, setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s

theorem preCDF_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine fun r ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s

lemma setIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] :
    ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real s := by
  rw [integral_toReal]
  · rw [setLIntegral_preCDF_fst _ _ hs, measureReal_def]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

lemma integral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real univ := by
  rw [← setIntegral_univ, setIntegral_preCDF_fst ρ _ MeasurableSet.univ]

lemma integrable_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℚ) :
    Integrable (fun a ↦ (preCDF ρ x a).toReal) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ ↦ ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [preCDF_le_one ρ] with a ha using ENNReal.ofReal_toReal_le.trans (ha _)

lemma isRatCondKernelCDFAux_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDFAux (fun p r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) where
  measurable := measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h₁ h₂
    exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hrr')
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [Kernel.const_apply]
    filter_upwards [preCDF_le_one ρ] with a ha
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp [ha]
  tendsto_integral_of_antitone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atBot MeasurableSet.univ
    rw [← ENNReal.toReal_zero]
    have h0 : Tendsto ENNReal.toReal (𝓝 0) (𝓝 0) :=
      ENNReal.continuousAt_toReal ENNReal.zero_ne_top
    exact h0.comp (h.comp hs_tendsto)
  tendsto_integral_of_monotone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atTop MeasurableSet.univ
    have h0 : Tendsto ENNReal.toReal (𝓝 (ρ.fst univ)) (𝓝 (ρ.fst.real univ)) :=
      ENNReal.continuousAt_toReal (measure_ne_top _ _)
    exact h0.comp (h.comp hs_tendsto)
  integrable _ q := integrable_preCDF ρ q
  setIntegral a s hs q := by rw [Kernel.const_apply, Kernel.const_apply,
    setIntegral_preCDF_fst _ _ hs, measureReal_def, measureReal_def, Measure.IicSnd_apply _ _ hs]

lemma isRatCondKernelCDF_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDF (fun p r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

/-! ### Conditional cdf -/

/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def condCDF (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction :=
  stieltjesOfMeasurableRat (fun a r ↦ (preCDF ρ r a).toReal) measurable_preCDF' a

lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × ℝ)) (a : α) :
    condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal)
      (measurable_preCDF'.comp measurable_snd) ((), a) := by
  ext x
  rw [condCDF, ← stieltjesOfMeasurableRat_unit_prod]

lemma isCondKernelCDF_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (Kernel.const Unit ρ)
      (Kernel.const Unit ρ.fst) := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem condCDF_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCDF ρ a r :=
  stieltjesOfMeasurableRat_nonneg _ a r

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem condCDF_le_one (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) : condCDF ρ a x ≤ 1 :=
  stieltjesOfMeasurableRat_le_one _ _ _

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_condCDF_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) := tendsto_stieltjesOfMeasurableRat_atBot _ _

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_condCDF_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) := tendsto_stieltjesOfMeasurableRat_atTop _ _

theorem condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ condCDF ρ a r) =ᵐ[ρ.fst] fun a ↦ (preCDF ρ r a).toReal := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r

theorem ofReal_condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha, ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) : Measurable fun a ↦ condCDF ρ a x :=
  measurable_stieltjesOfMeasurableRat _ _

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a ↦ condCDF ρ a x := stronglyMeasurable_stieltjesOfMeasurableRat _ _

theorem setLIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setLIntegral () hs x

theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).lintegral () x

theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  (isCondKernelCDF_condCDF ρ).integrable () x

theorem setIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setIntegral () hs x

theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).integral () x

section Measure

theorem measure_condCDF_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _

theorem measure_condCDF_univ (ρ : Measure (α × ℝ)) (a : α) : (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)

instance instIsProbabilityMeasureCondCDF (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
theorem measurable_measure_condCDF (ρ : Measure (α × ℝ)) :
    Measurable fun a => (condCDF ρ a).measure :=
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u ↦ (measurable_condCDF ρ u).ennreal_ofReal

end Measure

end ProbabilityTheory
