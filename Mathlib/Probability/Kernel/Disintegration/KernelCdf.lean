/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes

/-!
# Conditional cumulative distribution function of a Markov kernel

## Main definitions

Let `μ : kernel α (β × ℝ)` and `ν : kernel α β`.

* `ProbabilityTheory.IsCondKernelCDF`: a function `f : α × β → StieltjesFunction` is called
  a conditional kernel CDF of `μ` with respect to `ν` if it is measurable, tends to to 0 at -∞ and
  to 1 at +∞ for all `p : α × β`, if `fun t ↦ f (a, t) x` is `(ν a)`-integrable for all `a : α` and
  `x : ℝ` and for all measurable sets `s : Set β`,
  `∫ t in s, f (a, t) x ∂(ν a) = (μ a (s ×ˢ Iic x)).toReal`.
* `ProbabilityTheory.IsCondKernelCDF.toKernel`: from a function `f : α × β → StieltjesFunction`
  with the property `hf : IsCondKernelCDF f μ ν`, build a `kernel (α × β) ℝ` such that
  `μ = ν ⊗ₖ hf.toKernel f`.
* `ProbabilityTheory.IsRatCondKernelCDF`: a function `f : α × β → ℚ → ℝ` is called a rational
  conditional kernel CDF of `μ` with respect to `ν` if is measurable and satisfies the same
  integral conditions as in the definition of `IsCondKernelCDF`, and the `ℚ → ℝ` function `f (a, x)`
  satisfies the properties of a Sieltjes function for `(ν a)`-almost all `x : β`.

## Main statements

* `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`: if `f : α × β → ℚ → ℝ` has the
  property `IsRatCondKernelCDF`, then `stieltjesOfMeasurableRat f` is a function
  `α × β → StieltjesFunction` with the property `IsCondKernelCDF`.
* `ProbabilityTheory.kernel.eq_compProd_toKernel`: for `hf : IsCondKernelCDF f μ ν`,
  `μ = ν ⊗ₖ hf.toKernel f`

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α]

section stieltjesOfMeasurableRat

variable {α β : Type*} [MeasurableSpace α] {mβ : MeasurableSpace β}
  {f : α × β → ℚ → ℝ} {μ : kernel α (β × ℝ)} {ν : kernel α β}

structure IsRatCondKernelCDF (f : α × β → ℚ → ℝ) (μ : kernel α (β × ℝ)) (ν : kernel α β) : Prop :=
  (measurable : Measurable f)
  (isRatStieltjesPoint_ae (a : α) : ∀ᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t))
  (integrable (a : α) (q : ℚ) : Integrable (fun t ↦ f (a, t) q) (ν a))
  (set_integral (a : α) {s : Set β} (_hs : MeasurableSet s) (q : ℚ) :
    ∫ t in s, f (a, t) q ∂(ν a) = (μ a (s ×ˢ Iic (q : ℝ))).toReal)

lemma stieltjesOfMeasurableRat_ae_eq (hf : IsRatCondKernelCDF f μ ν) (a : α) (q : ℚ) :
    (fun t ↦ stieltjesOfMeasurableRat f hf.measurable (a, t) q) =ᵐ[ν a] fun t ↦ f (a, t) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint ha]

lemma set_integral_stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f μ ν) (a : α) (q : ℚ)
    {s : Set β} (hs : MeasurableSet s) :
    ∫ t in s, stieltjesOfMeasurableRat f hf.measurable (a, t) q ∂(ν a)
      = (μ a (s ×ˢ Iic (q : ℝ))).toReal := by
  rw [set_integral_congr_ae hs (g := fun t ↦ f (a, t) q) ?_, hf.set_integral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ ↦ hb

lemma set_lintegral_stieltjesOfMeasurableRat_rat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (q : ℚ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) q) ∂(ν a)
      = μ a (s ×ˢ Iic (q : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [set_integral_stieltjesOfMeasurableRat_rat hf a q hs, ENNReal.ofReal_toReal]
    exact measure_ne_top _ _
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x ↦ stieltjesOfMeasurableRat_nonneg _ _ _)

lemma set_lintegral_stieltjesOfMeasurableRat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) x) ∂(ν a)
      = μ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `set_lintegral_stieltjesOfMeasurableRat_rat`.
  -- We use  a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices μ a (s ×ˢ Iic (q : ℝ)) = 0 by
      symm
      refine measure_mono_null (fun p ↦ ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 ↦ ⟨h1, h2.trans hq.le⟩
    suffices (μ a (s ×ˢ Iic (q : ℝ))).toReal = 0 by
      rw [ENNReal.toReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.set_integral a hs q]
    simp [hρ_zero]
  have h : ∫⁻ t in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) x) ∂(ν a)
      = ∫⁻ t in s, ⨅ r : { r' : ℚ // x < r' },
        ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) r) ∂(ν a) := by
    congr with t : 1
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
  · refine Monotone.directed_ge fun i j hij t ↦ ?_
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

lemma lintegral_stieltjesOfMeasurableRat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (x : ℝ) :
    ∫⁻ t, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) x) ∂(ν a)
      = μ a (univ ×ˢ Iic x) := by
  rw [← set_lintegral_univ, set_lintegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

lemma integrable_stieltjesOfMeasurableRat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (x : ℝ) :
    Integrable (fun t ↦ stieltjesOfMeasurableRat f hf.measurable (a, t) x) (ν a) := by
  have : (fun t ↦ stieltjesOfMeasurableRat f hf.measurable (a, t) x)
      = fun t ↦ (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, t) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact (measurable_stieltjesOfMeasurableRat hf.measurable x).comp measurable_prod_mk_left
  · rw [lintegral_stieltjesOfMeasurableRat hf]
    exact measure_ne_top _ _

lemma set_integral_stieltjesOfMeasurableRat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫ t in s, stieltjesOfMeasurableRat f hf.measurable (a, t) x ∂(ν a)
      = (μ a (s ×ˢ Iic x)).toReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff, ENNReal.ofReal_toReal]
  rotate_left
  · exact measure_ne_top _ _
  · exact set_integral_nonneg hs (fun _ _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal, set_lintegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exact (integrable_stieltjesOfMeasurableRat hf _ _).restrict
  · exact ae_of_all _ (fun _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)

lemma integral_stieltjesOfMeasurableRat [IsFiniteKernel μ] (hf : IsRatCondKernelCDF f μ ν)
    (a : α) (x : ℝ) :
    ∫ t, stieltjesOfMeasurableRat f hf.measurable (a, t) x ∂(ν a)
      = (μ a (univ ×ˢ Iic x)).toReal := by
  rw [← integral_univ, set_integral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

end stieltjesOfMeasurableRat

section IsCondKernelCDF

variable {α β : Type*} [MeasurableSpace α] {mβ : MeasurableSpace β}
  {f : α × β → StieltjesFunction} {μ : kernel α (β × ℝ)} {ν : kernel α β}

structure IsCondKernelCDF (f : α × β → StieltjesFunction) (μ : kernel α (β × ℝ)) (ν : kernel α β) :
    Prop :=
  (measurable (x : ℝ) : Measurable fun p ↦ f p x)
  (integrable (a : α) (x : ℝ) : Integrable (fun t ↦ f (a, t) x) (ν a))
  (tendsto_atTop_one (p : α × β) : Tendsto (f p) atTop (𝓝 1))
  (tendsto_atBot_zero (p : α × β) : Tendsto (f p) atBot (𝓝 0))
  (set_integral (a : α) {s : Set β} (_hs : MeasurableSet s) (x : ℝ) :
    ∫ t in s, f (a, t) x ∂(ν a) = (μ a (s ×ˢ Iic x)).toReal)

lemma IsCondKernelCDF.nonneg (hf : IsCondKernelCDF f μ ν) (p : α × β) (x : ℝ) : 0 ≤ f p x :=
  Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x

lemma IsCondKernelCDF.le_one (hf : IsCondKernelCDF f μ ν) (p : α × β) (x : ℝ) : f p x ≤ 1 :=
  Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x

lemma IsCondKernelCDF.set_lintegral [IsFiniteKernel μ]
    {f : α × β → StieltjesFunction} (hf : IsCondKernelCDF f μ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ t in s, ENNReal.ofReal (f (a, t) x) ∂(ν a) = μ a (s ×ˢ Iic x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ ↦ hf.nonneg _ _)), hf.set_integral a hs x, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

lemma isCondKernelCDF_stieltjesOfMeasurableRat {f : α × β → ℚ → ℝ} (hf : IsRatCondKernelCDF f μ ν)
    [IsFiniteKernel μ] :
    IsCondKernelCDF (stieltjesOfMeasurableRat f hf.measurable) μ ν where
  measurable := measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  set_integral a _ hs x := set_integral_stieltjesOfMeasurableRat hf a x hs

end IsCondKernelCDF

section ToKernel

variable {_ : MeasurableSpace β} {f : α × β → StieltjesFunction}
  {μ : kernel α (β × ℝ)} {ν : kernel α β} {hf : IsCondKernelCDF f μ ν}

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
    simp_rw [StieltjesFunction.measure_Iic (f _) (hf_bot _)]
    simp only [sub_zero]
    exact (hf _).ennreal_ofReal
  · intro t ht ht_cd_meas
    have : (fun a ↦ (f a).measure tᶜ) =
        (fun a ↦ (f a).measure univ)
          - fun a ↦ (f a).measure t := by
      ext1 a
      rw [measure_compl ht, Pi.sub_apply]
      exact measure_ne_top _ _
    simp_rw [this, measure_univ]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas

noncomputable
def IsCondKernelCDF.toKernel (f : α × β → StieltjesFunction) (hf : IsCondKernelCDF f μ ν) :
    kernel (α × β) ℝ where
  val p := (f p).measure
  property := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one

lemma IsCondKernelCDF.toKernel_apply (p : α × β) : hf.toKernel f p = (f p).measure := rfl

instance instIsMarkovKernel_toKernel : IsMarkovKernel (hf.toKernel f) :=
  ⟨fun _ ↦ (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩

lemma IsCondKernelCDF.toKernel_Iic (p : α × β) (x : ℝ) :
    hf.toKernel f p (Iic x) = ENNReal.ofReal (f p x) := by
  rw [IsCondKernelCDF.toKernel_apply p, (f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

end ToKernel

section

variable {α β : Type*} [MeasurableSpace α] {mβ : MeasurableSpace β}
  {f : α × β → StieltjesFunction} {μ : kernel α (β × ℝ)} {ν : kernel α β}
  {hf : IsCondKernelCDF f μ ν}

lemma set_lintegral_toKernel_Iic [IsFiniteKernel μ] (hf : IsCondKernelCDF f μ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, hf.toKernel f (a, t) (Iic x) ∂(ν a) = μ a (s ×ˢ Iic x) := by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.set_lintegral _ hs _

lemma set_lintegral_toKernel_univ [IsFiniteKernel μ] (hf : IsCondKernelCDF f μ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ t in s, hf.toKernel f (a, t) univ ∂(ν a) = μ a (s ×ˢ univ) := by
  have : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
    ext1 x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true_iff]
    obtain ⟨r, hr⟩ := exists_rat_gt x
    exact ⟨r, hr.le⟩
  rw [← this, prod_iUnion]
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

lemma lintegral_toKernel_univ [IsFiniteKernel μ] (hf : IsCondKernelCDF f μ ν) (a : α) :
    ∫⁻ t, hf.toKernel f (a, t) univ ∂(ν a) = μ a univ := by
  rw [← set_lintegral_univ, set_lintegral_toKernel_univ hf a MeasurableSet.univ, univ_prod_univ]

lemma set_lintegral_toKernel_prod [IsFiniteKernel μ] (hf : IsCondKernelCDF f μ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set ℝ} (ht : MeasurableSet t) :
    ∫⁻ x in s, hf.toKernel f (a, x) t ∂(ν a) = μ a (s ×ˢ t) := by
  -- `set_lintegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  apply MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ ht
  · simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  · rintro t ⟨q, rfl⟩
    exact set_lintegral_toKernel_Iic hf a _ hs
  · intro t ht ht_lintegral
    calc ∫⁻ x in s, hf.toKernel f (a, x) tᶜ ∂(ν a)
      = ∫⁻ x in s, hf.toKernel f (a, x) univ - hf.toKernel f (a, x) t ∂(ν a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (hf.toKernel f (a, x)) _)]
    _ = ∫⁻ x in s, hf.toKernel f (a, x) univ ∂(ν a)
          - ∫⁻ x in s, hf.toKernel f (a, x) t ∂(ν a) := by
        rw [lintegral_sub]
        · exact (kernel.measurable_coe (hf.toKernel f) ht).comp measurable_prod_mk_left
        · rw [ht_lintegral]
          exact measure_ne_top _ _
        · exact eventually_of_forall fun a ↦ measure_mono (subset_univ _)
    _ = μ a (s ×ˢ univ) - μ a (s ×ˢ t) := by
        rw [set_lintegral_toKernel_univ hf a hs, ht_lintegral]
    _ = μ a (s ×ˢ tᶜ) := by
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

lemma lintegral_toKernel_mem [IsFiniteKernel μ] (hf : IsCondKernelCDF f μ ν)
    (a : α) {s : Set (β × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ x, hf.toKernel f (a, x) {y | (x, y) ∈ s} ∂(ν a) = μ a s := by
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
    calc ∫⁻ x, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ tᶜ} ∂(ν a)
      = ∫⁻ x, hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t}ᶜ ∂(ν a) := rfl
    _ = ∫⁻ x, hf.toKernel f (a, x) univ
          - hf.toKernel f (a, x) {y : ℝ | (x, y) ∈ t} ∂(ν a) := by
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
    _ = μ a univ - μ a t := by rw [ht_eq, lintegral_toKernel_univ hf]
    _ = μ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
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
    calc ∫⁻ x, hf.toKernel f (a, x) (⋃ i, {y | (x, y) ∈ f' i}) ∂(ν a)
      = ∫⁻ x, ∑' i, hf.toKernel f (a, x) {y | (x, y) ∈ f' i} ∂(ν a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i ↦ measurable_prod_mk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ x, hf.toKernel f (a, x) {y | (x, y) ∈ f' i} ∂(ν a) :=
          lintegral_tsum fun i ↦ (kernel.measurable_kernel_prod_mk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, μ a (f' i) := by simp_rw [hf_eq]
    _ = μ a (iUnion f') := (measure_iUnion hf_disj hf_meas).symm

lemma kernel.eq_compProd_toKernel [IsFiniteKernel μ] [IsSFiniteKernel ν]
    (hf : IsCondKernelCDF f μ ν) :
    μ = ν ⊗ₖ hf.toKernel f := by
  ext a s hs
  rw [kernel.compProd_apply _ _ _ hs, lintegral_toKernel_mem hf a hs]

lemma ae_toKernel_eq_one [IsFiniteKernel μ] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f μ ν) (a : α)
    {s : Set ℝ} (hs : MeasurableSet s) (hμs : μ a {x | x.snd ∈ sᶜ} = 0) :
    ∀ᵐ t ∂(ν a), hf.toKernel f (a, t) s = 1 := by
  have h_eq : μ = ν ⊗ₖ hf.toKernel f := kernel.eq_compProd_toKernel hf
  have h : μ a {x | x.snd ∈ sᶜ} = (ν ⊗ₖ hf.toKernel f) a {x | x.snd ∈ sᶜ} := by
    rw [← h_eq]
  rw [hμs, kernel.compProd_apply] at h
  swap; · exact measurable_snd hs.compl
  rw [eq_comm, lintegral_eq_zero_iff] at h
  swap
  · simp only [mem_compl_iff, mem_setOf_eq]
    change Measurable ((fun p ↦ hf.toKernel f p {c | c ∉ s}) ∘ (fun b : β ↦ (a, b)))
    exact (kernel.measurable_coe _ hs.compl).comp measurable_prod_mk_left
  simp only [mem_compl_iff, mem_setOf_eq, kernel.prodMkLeft_apply'] at h
  filter_upwards [h] with t ht
  change hf.toKernel f (a, t) sᶜ = 0 at ht
  rwa [prob_compl_eq_zero_iff hs] at ht

lemma measurableSet_toKernel_eq_one (hf : IsCondKernelCDF f μ ν) {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet {p | hf.toKernel f p s = 1} :=
  (kernel.measurable_coe _ hs) (measurableSet_singleton 1)

end

end ProbabilityTheory
