/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes

/-!
# Building a Markov kernel from a conditional cumulative distribution function

Let `κ : kernel α (β × ℝ)` and `ν : kernel α β` be two finite kernels.
A function `f : α × β → StieltjesFunction` is called a conditional kernel CDF of `κ` with respect
to `ν` if it is measurable, tends to to 0 at -∞ and to 1 at +∞ for all `p : α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for all measurable
sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a (s ×ˢ Iic x)).toReal`.

From such a function with property `hf : IsCondKernelCDF f κ ν`, we can build a `kernel (α × β) ℝ`
denoted by `hf.toKernel f` such that `κ = ν ⊗ₖ hf.toKernel f`.

## Main definitions

Let `κ : kernel α (β × ℝ)` and `ν : kernel α β`.

* `ProbabilityTheory.IsCondKernelCDF`: a function `f : α × β → StieltjesFunction` is called
  a conditional kernel CDF of `κ` with respect to `ν` if it is measurable, tends to to 0 at -∞ and
  to 1 at +∞ for all `p : α × β`, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and
  `x : ℝ` and for all measurable sets `s : Set β`,
  `∫ b in s, f (a, b) x ∂(ν a) = (κ a (s ×ˢ Iic x)).toReal`.
* `ProbabilityTheory.IsCondKernelCDF.toKernel`: from a function `f : α × β → StieltjesFunction`
  with the property `hf : IsCondKernelCDF f κ ν`, build a `kernel (α × β) ℝ` such that
  `κ = ν ⊗ₖ hf.toKernel f`.
* `ProbabilityTheory.IsRatCondKernelCDF`: a function `f : α × β → ℚ → ℝ` is called a rational
  conditional kernel CDF of `κ` with respect to `ν` if is measurable and satisfies the same
  integral conditions as in the definition of `IsCondKernelCDF`, and the `ℚ → ℝ` function `f (a, b)`
  satisfies the properties of a Stieltjes function for `(ν a)`-almost all `b : β`.

## Main statements

* `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`: if `f : α × β → ℚ → ℝ` has the
  property `IsRatCondKernelCDF`, then `stieltjesOfMeasurableRat f` is a function
  `α × β → StieltjesFunction` with the property `IsCondKernelCDF`.
* `ProbabilityTheory.compProd_toKernel`: for `hf : IsCondKernelCDF f κ ν`, `ν ⊗ₖ hf.toKernel f = κ`.

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {κ : kernel α (β × ℝ)} {ν : kernel α β}

section stieltjesOfMeasurableRat

variable {f : α × β → ℚ → ℝ}

/-- a function `f : α × β → ℚ → ℝ` is called a rational conditional kernel CDF of `κ` with respect
to `ν` if is measurable, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ`
and for all measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a (s ×ˢ Iic x)).toReal`.
Also the `ℚ → ℝ` function `f (a, b)` should satisfy the properties of a Sieltjes function for
`(ν a)`-almost all `b : β`. -/
structure IsRatCondKernelCDF (f : α × β → ℚ → ℝ) (κ : kernel α (β × ℝ)) (ν : kernel α β) : Prop :=
  measurable : Measurable f
  isRatStieltjesPoint_ae (a : α) : ∀ᵐ b ∂(ν a), IsRatStieltjesPoint f (a, b)
  integrable (a : α) (q : ℚ) : Integrable (fun b ↦ f (a, b) q) (ν a)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (q : ℚ) :
    ∫ b in s, f (a, b) q ∂(ν a) = (κ a (s ×ˢ Iic (q : ℝ))).toReal

lemma IsRatCondKernelCDF.mono (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Monotone (f (a, b)) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.mono

lemma IsRatCondKernelCDF.tendsto_atTop_one (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Tendsto (f (a, b)) atTop (𝓝 1) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atTop_one

lemma IsRatCondKernelCDF.tendsto_atBot_zero (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Tendsto (f (a, b)) atBot (𝓝 0) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atBot_zero

lemma IsRatCondKernelCDF.iInf_rat_gt_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), ∀ q, ⨅ r : Ioi q, f (a, b) r = f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.iInf_rat_gt_eq

lemma stieltjesOfMeasurableRat_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : ℚ) :
    (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) q) =ᵐ[ν a] fun b ↦ f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint ha]

lemma setIntegral_stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : ℚ)
    {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) q ∂(ν a)
      = (κ a (s ×ˢ Iic (q : ℝ))).toReal := by
  rw [setIntegral_congr_ae hs (g := fun b ↦ f (a, b) q) ?_, hf.setIntegral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ ↦ hb

@[deprecated]
alias set_integral_stieltjesOfMeasurableRat_rat :=
  setIntegral_stieltjesOfMeasurableRat_rat -- deprecated on 2024-04-17

lemma set_lintegral_stieltjesOfMeasurableRat_rat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (q : ℚ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) q) ∂(ν a)
      = κ a (s ×ˢ Iic (q : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [setIntegral_stieltjesOfMeasurableRat_rat hf a q hs, ENNReal.ofReal_toReal]
    exact measure_ne_top _ _
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x ↦ stieltjesOfMeasurableRat_nonneg _ _ _)

lemma set_lintegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_stieltjesOfMeasurableRat_rat`.
  -- We use a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices κ a (s ×ˢ Iic (q : ℝ)) = 0 by
      symm
      refine measure_mono_null (fun p ↦ ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 ↦ ⟨h1, h2.trans hq.le⟩
    suffices (κ a (s ×ˢ Iic (q : ℝ))).toReal = 0 by
      rw [ENNReal.toReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.setIntegral a hs q]
    simp [hρ_zero]
  have h : ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = ∫⁻ b in s, ⨅ r : { r' : ℚ // x < r' },
        ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) r) ∂(ν a) := by
    congr with b : 1
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    rw [← measure_iInter_eq_iInf]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      refine ⟨fun h a ha ↦ h.trans ?_, fun h ↦ ?_⟩
      · exact mod_cast ha.le
      · refine le_of_forall_lt_rat_imp_le fun q hq ↦ h q ?_
        exact mod_cast hq
    · exact fun _ ↦ measurableSet_Iic
    · refine Monotone.directed_ge fun r r' hrr' ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hrr'
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h, lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } ↦ ?_]
  rotate_left
  · intro b
    rw [set_lintegral_stieltjesOfMeasurableRat_rat hf a _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij b ↦ ?_
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    refine measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · refine Measurable.ennreal_ofReal ?_
    exact (measurable_stieltjesOfMeasurableRat hf.measurable _).comp measurable_prod_mk_left
  simp_rw [set_lintegral_stieltjesOfMeasurableRat_rat hf _ _ hs]
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq ↦ hyx.trans hq.le⟩
  · exact fun i ↦ hs.prod measurableSet_Iic
  · refine Monotone.directed_ge fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩

lemma lintegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    ∫⁻ b, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (univ ×ˢ Iic x) := by
  rw [← set_lintegral_univ, set_lintegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

lemma integrable_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    Integrable (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) x) (ν a) := by
  have : (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) x)
      = fun b ↦ (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact (measurable_stieltjesOfMeasurableRat hf.measurable x).comp measurable_prod_mk_left
  · rw [lintegral_stieltjesOfMeasurableRat hf]
    exact measure_ne_top _ _

lemma setIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a (s ×ˢ Iic x)).toReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff, ENNReal.ofReal_toReal]
  rotate_left
  · exact measure_ne_top _ _
  · exact setIntegral_nonneg hs (fun _ _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal, set_lintegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exact (integrable_stieltjesOfMeasurableRat hf _ _).restrict
  · exact ae_of_all _ (fun _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)

@[deprecated]
alias set_integral_stieltjesOfMeasurableRat :=
  setIntegral_stieltjesOfMeasurableRat -- deprecated on 2024-04-17

lemma integral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    ∫ b, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a (univ ×ˢ Iic x)).toReal := by
  rw [← integral_univ, setIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

end stieltjesOfMeasurableRat

section isRatCondKernelCDFAux

variable {f : α × β → ℚ → ℝ}

/-- This property implies `IsRatCondKernelCDF`. The measurability, integrability and integral
conditions are the same, but the limit properties of `IsRatCondKernelCDF` are replaced by
limits of integrals. -/
structure IsRatCondKernelCDFAux (f : α × β → ℚ → ℝ) (κ : kernel α (β × ℝ)) (ν : kernel α β) :
    Prop :=
  measurable : Measurable f
  mono' (a : α) {q r : ℚ} (_hqr : q ≤ r) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ f (a, c) r
  nonneg' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), 0 ≤ f (a, c) q
  le_one' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ 1
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atBot (𝓝 0)` but slightly easier
  to prove in the current applications of this definition (some integral convergence lemmas
  currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_antitone (a : α) (seq : ℕ → ℚ) (_hs : Antitone seq)
    (_hs_tendsto : Tendsto seq atTop atBot) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 0)
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atTop (𝓝 (ν a univ).toReal)` but
  slightly easier to prove in the current applications of this definition (some integral convergence
  lemmas currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_monotone (a : α) (seq : ℕ → ℚ) (_hs : Monotone seq)
    (_hs_tendsto : Tendsto seq atTop atTop) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 (ν a univ).toReal)
  integrable (a : α) (q : ℚ) : Integrable (fun c ↦ f (a, c) q) (ν a)
  setIntegral (a : α) {A : Set β} (_hA : MeasurableSet A) (q : ℚ) :
    ∫ c in A, f (a, c) q ∂(ν a) = (κ a (A ×ˢ Iic ↑q)).toReal

lemma IsRatCondKernelCDFAux.measurable_right (hf : IsRatCondKernelCDFAux f κ ν) (a : α) (q : ℚ) :
    Measurable (fun t ↦ f (a, t) q) := by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prod_mk_left

lemma IsRatCondKernelCDFAux.mono (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), Monotone (f (a, c)) := by
  unfold Monotone
  simp_rw [ae_all_iff]
  exact fun _ _ hqr ↦ hf.mono' a hqr

lemma IsRatCondKernelCDFAux.nonneg (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ q, 0 ≤ f (a, c) q := ae_all_iff.mpr <| hf.nonneg' a

lemma IsRatCondKernelCDFAux.le_one (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ q, f (a, c) q ≤ 1 := ae_all_iff.mpr <| hf.le_one' a

lemma IsRatCondKernelCDFAux.tendsto_zero_of_antitone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ) (hseq : Antitone seq)
    (hseq_tendsto : Tendsto seq atTop atBot) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (seq m)) atTop (𝓝 0) := by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (seq n)
  · rw [integral_zero]
    exact hf.tendsto_integral_of_antitone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm ↦ ht (hseq hnm)
  · filter_upwards [hf.nonneg a] with c hc using fun i ↦ hc (seq i)

lemma IsRatCondKernelCDFAux.tendsto_one_of_monotone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ) (hseq : Monotone seq)
    (hseq_tendsto : Tendsto seq atTop atTop) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (seq m)) atTop (𝓝 1) := by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (seq n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_of_monotone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm ↦ ht (hseq hnm)
  · filter_upwards [hf.le_one a] with c hc using fun i ↦ hc (seq i)

lemma IsRatCondKernelCDFAux.tendsto_atTop_one (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (f (a, t)) atTop (𝓝 1) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    rw [tendsto_iff_tendsto_subseq_of_monotone h_mono tendsto_natCast_atTop_atTop]
    exact ht
  filter_upwards [hf.tendsto_one_of_monotone a Nat.cast Nat.mono_cast tendsto_natCast_atTop_atTop]
    with x hx using hx

lemma IsRatCondKernelCDFAux.tendsto_atBot_zero (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (f (a, t)) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun q : ℚ ↦ f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    have h_eq_neg : f (a, t) = fun q : ℚ ↦ f (a, t) (- -q) := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    convert ht.comp tendsto_neg_atBot_atTop
    simp
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    have h_anti : Antitone (fun q ↦ f (a, t) (-q)) := h_mono.comp_antitone monotone_id.neg
    exact (tendsto_iff_tendsto_subseq_of_antitone h_anti tendsto_natCast_atTop_atTop).mpr ht
  exact hf.tendsto_zero_of_antitone _ _ Nat.mono_cast.neg
    (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)

lemma IsRatCondKernelCDFAux.bddBelow_range (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, BddBelow (range fun (r : Ioi q) ↦ f (a, t) r) := by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q ↦ ⟨0, ?_⟩
  simp [mem_lowerBounds, hc]

lemma IsRatCondKernelCDFAux.integrable_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, f (a, t) r) (ν a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨(measurable_iInf fun i ↦ hf.measurable_right a _).aestronglyMeasurable, ?_⟩
  refine (?_ : _ ≤ (ν a univ : ℝ≥0∞)).trans_lt (measure_lt_top _ _)
  refine (snorm_le_of_ae_bound (C := 1) ?_).trans (by simp)
  filter_upwards [hf.bddBelow_range a, hf.nonneg a, hf.le_one a]
    with t hbdd_below h_nonneg h_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · refine ciInf_le_of_le ?_ ?_ ?_
    · exact hbdd_below _
    · exact ⟨q + 1, by simp⟩
    · exact h_le_one _
  · exact le_ciInf fun r ↦ h_nonneg _

lemma _root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {s : Set α} (hs : MeasurableSet s) (t : ℚ) :
    ⨅ r : { r' : ℚ // t < r' }, ρ (s ×ˢ Iic (r : ℝ)) = ρ (s ×ˢ Iic (t : ℝ)) := by
  rw [← measure_iInter_eq_iInf]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall, Subtype.coe_mk]
    refine ⟨fun h ↦ ?_, fun h a hta ↦ h.trans ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q htq ↦ h q ?_
      exact mod_cast htq
    · exact mod_cast hta.le
  · exact fun _ => hs.prod measurableSet_Iic
  · refine Monotone.directed_ge fun r r' hrr' ↦ prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, ?_⟩)
    refine Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  · exact ⟨⟨t + 1, lt_add_one _⟩, measure_ne_top ρ _⟩

lemma IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) (q : ℚ) {A : Set β} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a) = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        ≤ (κ a (A ×ˢ Iic (r : ℝ))).toReal := by
      intro r
      rw [← hf.setIntegral a hA]
      refine setIntegral_mono_ae ?_ ?_ ?_
      · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
      · exact (hf.integrable _ _).integrableOn
      · filter_upwards [hf.bddBelow_range a] with t ht using ciInf_le (ht _) r
    calc ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a)
      ≤ ⨅ r : Ioi q, (κ a (A ×ˢ Iic (r : ℝ))).toReal := le_ciInf h
    _ = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
        rw [← Measure.iInf_rat_gt_prod_Iic hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← hf.setIntegral a hA]
    refine setIntegral_mono_ae ?_ ?_ ?_
    · exact (hf.integrable _ _).integrableOn
    · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
    · filter_upwards [hf.mono a] with c h_mono using le_ciInf (fun r ↦ h_mono (le_of_lt r.prop))

@[deprecated]
alias IsRatCondKernelCDFAux.set_integral_iInf_rat_gt :=
  IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt -- deprecated on 2024-04-17

lemma IsRatCondKernelCDFAux.iInf_rat_gt_eq (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, ⨅ r : Ioi q, f (a, t) r = f (a, t) q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · exact fun _ _ _ ↦ (hf.integrable_iInf_rat_gt _ _).integrableOn
  · exact fun _ _ _ ↦ (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.setIntegral _ hs, hf.setIntegral_iInf_rat_gt _ _ hs]

lemma IsRatCondKernelCDFAux.isRatStieltjesPoint_ae (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t) := by
  filter_upwards [hf.tendsto_atTop_one a, hf.tendsto_atBot_zero a,
    hf.iInf_rat_gt_eq a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨h_mono, ht_top, ht_bot, ht_iInf⟩

lemma IsRatCondKernelCDFAux.isRatCondKernelCDF (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] :
    IsRatCondKernelCDF f κ ν where
  measurable := hf.measurable
  isRatStieltjesPoint_ae := hf.isRatStieltjesPoint_ae
  integrable := hf.integrable
  setIntegral := hf.setIntegral

end isRatCondKernelCDFAux

section IsCondKernelCDF

variable {f : α × β → StieltjesFunction}

/-- A function `f : α × β → StieltjesFunction` is called a conditional kernel CDF of `κ` with
respect to `ν` if it is measurable, tends to to 0 at -∞ and to 1 at +∞ for all `p : α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for all
measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a (s ×ˢ Iic x)).toReal`. -/
structure IsCondKernelCDF (f : α × β → StieltjesFunction) (κ : kernel α (β × ℝ)) (ν : kernel α β) :
    Prop :=
  measurable (x : ℝ) : Measurable fun p ↦ f p x
  integrable (a : α) (x : ℝ) : Integrable (fun b ↦ f (a, b) x) (ν a)
  tendsto_atTop_one (p : α × β) : Tendsto (f p) atTop (𝓝 1)
  tendsto_atBot_zero (p : α × β) : Tendsto (f p) atBot (𝓝 0)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (x : ℝ) :
    ∫ b in s, f (a, b) x ∂(ν a) = (κ a (s ×ˢ Iic x)).toReal

lemma IsCondKernelCDF.nonneg (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : ℝ) : 0 ≤ f p x :=
  Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x

lemma IsCondKernelCDF.le_one (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : ℝ) : f p x ≤ 1 :=
  Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x

lemma IsCondKernelCDF.integral
    {f : α × β → StieltjesFunction} (hf : IsCondKernelCDF f κ ν) (a : α) (x : ℝ) :
    ∫ b, f (a, b) x ∂(ν a) = (κ a (univ ×ˢ Iic x)).toReal := by
  rw [← hf.setIntegral _ MeasurableSet.univ, Measure.restrict_univ]

lemma IsCondKernelCDF.set_lintegral [IsFiniteKernel κ]
    {f : α × β → StieltjesFunction} (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ b in s, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ ↦ hf.nonneg _ _)), hf.setIntegral a hs x, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

lemma IsCondKernelCDF.lintegral [IsFiniteKernel κ]
    {f : α × β → StieltjesFunction} (hf : IsCondKernelCDF f κ ν) (a : α) (x : ℝ) :
    ∫⁻ b, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (univ ×ˢ Iic x) := by
  rw [← hf.set_lintegral _ MeasurableSet.univ, Measure.restrict_univ]

lemma isCondKernelCDF_stieltjesOfMeasurableRat {f : α × β → ℚ → ℝ} (hf : IsRatCondKernelCDF f κ ν)
    [IsFiniteKernel κ] :
    IsCondKernelCDF (stieltjesOfMeasurableRat f hf.measurable) κ ν where
  measurable := measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  setIntegral a _ hs x := setIntegral_stieltjesOfMeasurableRat hf a x hs

end IsCondKernelCDF

section ToKernel

variable {_ : MeasurableSpace β} {f : α × β → StieltjesFunction}
  {κ : kernel α (β × ℝ)} {ν : kernel α β}

/-- A measurable function `α → StieltjesFunction` with limits 0 at -∞ and 1 at +∞ gives a measurable
function `α → Measure ℝ` by taking `StieltjesFunction.measure` at each point. -/
lemma StieltjesFunction.measurable_measure {f : α → StieltjesFunction}
    (hf : ∀ q, Measurable fun a ↦ f a q)
    (hf_bot : ∀ a, Tendsto (f a) atBot (𝓝 0))
    (hf_top : ∀ a, Tendsto (f a) atTop (𝓝 1)) :
    Measurable fun a ↦ (f a).measure := by
  refine Measure.measurable_measure.mpr fun s hs ↦ ?_
  have : ∀ a, IsProbabilityMeasure (f a).measure :=
    fun a ↦ (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
  refine MeasurableSpace.induction_on_inter
    (C := fun s ↦ Measurable fun b ↦ StieltjesFunction.measure (f b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic ?_ ?_ ?_ ?_ hs
  · simp only [measure_empty, measurable_const]
  · rintro S ⟨u, rfl⟩
    simp_rw [StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_zero]
    exact (hf _).ennreal_ofReal
  · intro t ht ht_cd_meas
    have : (fun a ↦ (f a).measure tᶜ) = (fun a ↦ (f a).measure univ) - fun a ↦ (f a).measure t := by
      ext1 a
      rw [measure_compl ht, Pi.sub_apply]
      exact measure_ne_top _ _
    simp_rw [this, measure_univ]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas

/-- A function `f : α × β → StieltjesFunction` with the property `IsCondKernelCDF f κ ν` gives a
Markov kernel from `α × β` to `ℝ`, by taking for each `p : α × β` the measure defined by `f p`. -/
noncomputable
def IsCondKernelCDF.toKernel (f : α × β → StieltjesFunction) (hf : IsCondKernelCDF f κ ν) :
    kernel (α × β) ℝ where
  val p := (f p).measure
  property := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one

lemma IsCondKernelCDF.toKernel_apply {hf : IsCondKernelCDF f κ ν} (p : α × β) :
    hf.toKernel f p = (f p).measure := rfl

instance instIsMarkovKernel_toKernel {hf : IsCondKernelCDF f κ ν} :
    IsMarkovKernel (hf.toKernel f) :=
  ⟨fun _ ↦ (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩

lemma IsCondKernelCDF.toKernel_Iic {hf : IsCondKernelCDF f κ ν} (p : α × β) (x : ℝ) :
    hf.toKernel f p (Iic x) = ENNReal.ofReal (f p x) := by
  rw [IsCondKernelCDF.toKernel_apply p, (f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

end ToKernel

section

variable {f : α × β → StieltjesFunction}

lemma set_lintegral_toKernel_Iic [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) (Iic x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.set_lintegral _ hs _

lemma set_lintegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a) = κ a (s ×ˢ univ) := by
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  have h_dir : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ Iic (q : ℝ) := by
    refine Monotone.directed_le fun r r' hrr' ↦ Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ s ×ˢ Iic (q : ℝ) := by
    refine Monotone.directed_le fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  simp_rw [measure_iUnion_eq_iSup h_dir, measure_iUnion_eq_iSup h_dir_prod]
  rw [lintegral_iSup_directed]
  · simp_rw [set_lintegral_toKernel_Iic hf _ _ hs]
  · refine fun q ↦ Measurable.aemeasurable ?_
    exact (kernel.measurable_coe _ measurableSet_Iic).comp measurable_prod_mk_left
  · refine Monotone.directed_le fun i j hij t ↦ measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij

lemma lintegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) :
    ∫⁻ b, hf.toKernel f (a, b) univ ∂(ν a) = κ a univ := by
  rw [← set_lintegral_univ, set_lintegral_toKernel_univ hf a MeasurableSet.univ, univ_prod_univ]

lemma set_lintegral_toKernel_prod [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set ℝ} (ht : MeasurableSet t) :
    ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) = κ a (s ×ˢ t) := by
  -- `set_lintegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  apply MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ ht
  · simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  · rintro t ⟨q, rfl⟩
    exact set_lintegral_toKernel_Iic hf a _ hs
  · intro t ht ht_lintegral
    calc ∫⁻ b in s, hf.toKernel f (a, b) tᶜ ∂(ν a)
      = ∫⁻ b in s, hf.toKernel f (a, b) univ - hf.toKernel f (a, b) t ∂(ν a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (hf.toKernel f (a, x)) _)]
    _ = ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a)
          - ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) := by
        rw [lintegral_sub]
        · exact (kernel.measurable_coe (hf.toKernel f) ht).comp measurable_prod_mk_left
        · rw [ht_lintegral]
          exact measure_ne_top _ _
        · exact eventually_of_forall fun a ↦ measure_mono (subset_univ _)
    _ = κ a (s ×ˢ univ) - κ a (s ×ˢ t) := by
        rw [set_lintegral_toKernel_univ hf a hs, ht_lintegral]
    _ = κ a (s ×ˢ tᶜ) := by
        rw [← measure_diff _ (hs.prod ht) (measure_ne_top _ _)]
        · rw [prod_diff_prod, compl_eq_univ_diff]
          simp only [diff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  · intro f hf_disj hf_meas hf_eq
    simp_rw [measure_iUnion hf_disj hf_meas]
    rw [lintegral_tsum, prod_iUnion, measure_iUnion]
    · simp_rw [hf_eq]
    · intro i j hij
      rw [Function.onFun, Set.disjoint_prod]
      exact Or.inr (hf_disj hij)
    · exact fun i ↦ MeasurableSet.prod hs (hf_meas i)
    · exact fun i ↦
        ((kernel.measurable_coe _ (hf_meas i)).comp measurable_prod_mk_left).aemeasurable.restrict

lemma lintegral_toKernel_mem [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set (β × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ b, hf.toKernel f (a, b) {y | (b, y) ∈ s} ∂(ν a) = κ a s := by
  -- `set_lintegral_toKernel_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp only [mem_empty_iff_false, setOf_false, measure_empty, lintegral_const,
      zero_mul]
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂ := by
      intro a ha
      simp only [ha, prod_mk_mem_set_prod_eq, true_and_iff, setOf_mem_eq]
    rw [← lintegral_add_compl _ ht₁]
    have h_eq1 : ∫⁻ x in t₁, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(ν a)
        = ∫⁻ x in t₁, hf.toKernel f (a, x) t₂ ∂(ν a) := by
      refine set_lintegral_congr_fun ht₁ (eventually_of_forall fun a ha ↦ ?_)
      rw [h_prod_eq_snd a ha]
    have h_eq2 :
        ∫⁻ x in t₁ᶜ, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} ∂(ν a) = 0 := by
      suffices h_eq_zero :
          ∀ x ∈ t₁ᶜ, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t₁ ×ˢ t₂} = 0 by
        rw [set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero)]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, prod_mk_mem_set_prod_eq, false_and_iff, setOf_false, measure_empty]
    rw [h_eq1, h_eq2, add_zero]
    exact set_lintegral_toKernel_prod hf a ht₁ ht₂
  · intro t ht ht_eq
    calc ∫⁻ b, hf.toKernel f (a, b) {y : ℝ | (b, y) ∈ tᶜ} ∂(ν a)
      = ∫⁻ b, hf.toKernel f (a, b) {y : ℝ | (b, y) ∈ t}ᶜ ∂(ν a) := rfl
    _ = ∫⁻ b, hf.toKernel f (a, b) univ
          - hf.toKernel f (a, b) {y : ℝ | (b, y) ∈ t} ∂(ν a) := by
        congr with x : 1
        exact measure_compl (measurable_prod_mk_left ht)
          (measure_ne_top (hf.toKernel f (a, x)) _)
    _ = ∫⁻ x, hf.toKernel f (a, x) univ ∂(ν a) -
          ∫⁻ x, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t} ∂(ν a) := by
        have h_le : (fun x ↦ hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t})
              ≤ᵐ[ν a] fun x ↦ hf.toKernel f (a, x) univ :=
          eventually_of_forall fun _ ↦ measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact kernel.measurable_kernel_prod_mk_left' ht a
        refine ((lintegral_mono_ae h_le).trans_lt ?_).ne
        rw [lintegral_toKernel_univ hf]
        exact measure_lt_top _ univ
    _ = κ a univ - κ a t := by rw [ht_eq, lintegral_toKernel_univ hf]
    _ = κ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  · intro f' hf_disj hf_meas hf_eq
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f' i} = ⋃ i, {x | (a, x) ∈ f' i} := by
      intro a; ext x; simp only [mem_iUnion, mem_setOf_eq]
    simp_rw [h_eq]
    have h_disj : ∀ a, Pairwise (Disjoint on fun i ↦ {x | (a, x) ∈ f' i}) := by
      intro a i j hij
      have h_disj := hf_disj hij
      rw [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj ⊢
      ext1 x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false_iff]
      intro h_mem_both
      suffices (a, x) ∈ ∅ by rwa [mem_empty_iff_false] at this
      rwa [← h_disj, mem_inter_iff]
    calc ∫⁻ b, hf.toKernel f (a, b) (⋃ i, {y | (b, y) ∈ f' i}) ∂(ν a)
      = ∫⁻ b, ∑' i, hf.toKernel f (a, b) {y | (b, y) ∈ f' i} ∂(ν a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i ↦ measurable_prod_mk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ b, hf.toKernel f (a, b) {y | (b, y) ∈ f' i} ∂(ν a) :=
          lintegral_tsum fun i ↦ (kernel.measurable_kernel_prod_mk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, κ a (f' i) := by simp_rw [hf_eq]
    _ = κ a (iUnion f') := (measure_iUnion hf_disj hf_meas).symm

lemma compProd_toKernel [IsFiniteKernel κ] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν) :
    ν ⊗ₖ hf.toKernel f = κ := by
  ext a s hs
  rw [kernel.compProd_apply _ _ _ hs, lintegral_toKernel_mem hf a hs]

end

end ProbabilityTheory
