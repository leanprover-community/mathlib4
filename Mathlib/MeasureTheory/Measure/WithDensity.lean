/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Measure with a given density with respect to another measure

For a measure `μ` on `α` and a function `f : α → ℝ≥0∞`, we define a new measure `μ.withDensity f`.
On a measurable set `s`, that measure has value `∫⁻ a in s, f a ∂μ`.

An important result about `withDensity` is the Radon-Nikodym theorem. It states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν` then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that
`μ = ν.withDensity f`.
See `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`.

-/

open Set hiding restrict restrict_apply

open Filter ENNReal NNReal MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}

/-- Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the
measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`. -/
noncomputable
def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun s hs hd =>
    lintegral_iUnion hs hd _
#align measure_theory.measure.with_density MeasureTheory.Measure.withDensity

@[simp]
theorem withDensity_apply (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs
#align measure_theory.with_density_apply MeasureTheory.withDensity_apply

@[simp]
lemma withDensity_zero_left (f : α → ℝ≥0∞) : (0 : Measure α).withDensity f = 0 := by
  ext s hs
  rw [withDensity_apply _ hs]
  simp

theorem withDensity_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
    μ.withDensity f = μ.withDensity g := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)
#align measure_theory.with_density_congr_ae MeasureTheory.withDensity_congr_ae

lemma withDensity_mono {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) :
    μ.withDensity f ≤ μ.withDensity g := by
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  refine set_lintegral_mono_ae' hs ?_
  filter_upwards [hfg] with x h_le using fun _ ↦ h_le

theorem withDensity_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  refine' Measure.ext fun s hs => _
  rw [withDensity_apply _ hs, Measure.add_apply, withDensity_apply _ hs, withDensity_apply _ hs,
    ← lintegral_add_left hf]
  simp only [Pi.add_apply]
#align measure_theory.with_density_add_left MeasureTheory.withDensity_add_left

theorem withDensity_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  simpa only [add_comm] using withDensity_add_left hg f
#align measure_theory.with_density_add_right MeasureTheory.withDensity_add_right

theorem withDensity_add_measure {m : MeasurableSpace α} (μ ν : Measure α) (f : α → ℝ≥0∞) :
    (μ + ν).withDensity f = μ.withDensity f + ν.withDensity f := by
  ext1 s hs
  simp only [withDensity_apply f hs, restrict_add, lintegral_add_measure, Measure.add_apply]
#align measure_theory.with_density_add_measure MeasureTheory.withDensity_add_measure

theorem withDensity_sum {ι : Type*} {m : MeasurableSpace α} (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    (sum μ).withDensity f = sum fun n => (μ n).withDensity f := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply f hs, restrict_sum μ hs, lintegral_sum_measure]
#align measure_theory.with_density_sum MeasureTheory.withDensity_sum

theorem withDensity_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine' Measure.ext fun s hs => _
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul r hf]
  simp only [Pi.smul_apply, smul_eq_mul]
#align measure_theory.with_density_smul MeasureTheory.withDensity_smul

theorem withDensity_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    μ.withDensity (r • f) = r • μ.withDensity f := by
  refine' Measure.ext fun s hs => _
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul' r f hr]
  simp only [Pi.smul_apply, smul_eq_mul]
#align measure_theory.with_density_smul' MeasureTheory.withDensity_smul'

theorem withDensity_smul_measure (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
    (r • μ).withDensity f = r • μ.withDensity f := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.coe_smul, Pi.smul_apply, withDensity_apply _ hs,
    smul_eq_mul, set_lintegral_smul_measure]

theorem isFiniteMeasure_withDensity {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ ≠ ∞) :
    IsFiniteMeasure (μ.withDensity f) :=
  { measure_univ_lt_top := by
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lt_top_iff_ne_top] }
#align measure_theory.is_finite_measure_with_density MeasureTheory.isFiniteMeasure_withDensity

theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ := by
  refine' AbsolutelyContinuous.mk fun s hs₁ hs₂ => _
  rw [withDensity_apply _ hs₁]
  exact set_lintegral_measure_zero _ _ hs₂
#align measure_theory.with_density_absolutely_continuous MeasureTheory.withDensity_absolutelyContinuous

@[simp]
theorem withDensity_zero : μ.withDensity 0 = 0 := by
  ext1 s hs
  simp [withDensity_apply _ hs]
#align measure_theory.with_density_zero MeasureTheory.withDensity_zero

@[simp]
theorem withDensity_one : μ.withDensity 1 = μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]
#align measure_theory.with_density_one MeasureTheory.withDensity_one

@[simp]
theorem withDensity_const (c : ℝ≥0∞) : μ.withDensity (fun _ ↦ c) = c • μ := by
  ext1 s hs
  simp [withDensity_apply _ hs]

theorem withDensity_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    μ.withDensity (∑' n, f n) = sum fun n => μ.withDensity (f n) := by
  ext1 s hs
  simp_rw [sum_apply _ hs, withDensity_apply _ hs]
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' i : ℕ, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).aemeasurable]
  refine' lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)
#align measure_theory.with_density_tsum MeasureTheory.withDensity_tsum

theorem withDensity_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    μ.withDensity (s.indicator f) = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [withDensity_apply _ ht, lintegral_indicator _ hs, restrict_comm hs, ←
    withDensity_apply _ ht]
#align measure_theory.with_density_indicator MeasureTheory.withDensity_indicator

theorem withDensity_indicator_one {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (s.indicator 1) = μ.restrict s := by
  rw [withDensity_indicator hs, withDensity_one]
#align measure_theory.with_density_indicator_one MeasureTheory.withDensity_indicator_one

theorem withDensity_ofReal_mutuallySingular {f : α → ℝ} (hf : Measurable f) :
    (μ.withDensity fun x => ENNReal.ofReal <| f x) ⟂ₘ
      μ.withDensity fun x => ENNReal.ofReal <| -f x := by
  set S : Set α := { x | f x < 0 }
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine' ⟨S, hS, _, _⟩
  · rw [withDensity_apply _ hS, lintegral_eq_zero_iff hf.ennreal_ofReal, EventuallyEq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [withDensity_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_ofReal, EventuallyEq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)
#align measure_theory.with_density_of_real_mutually_singular MeasureTheory.withDensity_ofReal_mutuallySingular

theorem restrict_withDensity {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f := by
  ext1 t ht
  rw [restrict_apply ht, withDensity_apply _ ht, withDensity_apply _ (ht.inter hs),
    restrict_restrict ht]
#align measure_theory.restrict_with_density MeasureTheory.restrict_withDensity

theorem withDensity_eq_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h : μ.withDensity f = 0) :
    f =ᵐ[μ] 0 := by
  rw [← lintegral_eq_zero_iff' hf, ← set_lintegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    h, Measure.coe_zero, Pi.zero_apply]
#align measure_theory.with_density_eq_zero MeasureTheory.withDensity_eq_zero

theorem withDensity_apply_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hf : Measurable f) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x ≠ 0 } ∩ s) = 0 := by
  constructor
  · intro hs
    let t := toMeasurable (μ.withDensity f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_toMeasurable (μ.withDensity f) s))
    have A : μ.withDensity f t = 0 := by rw [measure_toMeasurable, hs]
    rw [withDensity_apply f (measurableSet_toMeasurable _ s), lintegral_eq_zero_iff hf,
      EventuallyEq, ae_restrict_iff, ae_iff] at A
    swap
    · exact hf (measurableSet_singleton 0)
    simp only [Pi.zero_apply, mem_setOf_eq, Filter.mem_mk] at A
    convert A using 2
    ext x
    simp only [and_comm, exists_prop, mem_inter_iff, iff_self_iff, mem_setOf_eq, mem_compl_iff,
      not_forall]
  · intro hs
    let t := toMeasurable μ ({ x | f x ≠ 0 } ∩ s)
    have A : s ⊆ t ∪ { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_setOf_eq, eq_self_iff_true, or_true_iff]
      · left
        apply subset_toMeasurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply withDensity_absolutelyContinuous
      rwa [measure_toMeasurable]
    · have M : MeasurableSet { x : α | f x = 0 } := hf (measurableSet_singleton _)
      rw [withDensity_apply _ M, lintegral_eq_zero_iff hf]
      filter_upwards [ae_restrict_mem M]
      simp only [imp_self, Pi.zero_apply, imp_true_iff]
#align measure_theory.with_density_apply_eq_zero MeasureTheory.withDensity_apply_eq_zero

theorem ae_withDensity_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x := by
  rw [ae_iff, ae_iff, withDensity_apply_eq_zero hf, iff_iff_eq]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, iff_self_iff, mem_setOf_eq, not_forall]
#align measure_theory.ae_with_density_iff MeasureTheory.ae_withDensity_iff

theorem ae_withDensity_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ.restrict { x | f x ≠ 0 }, p x := by
  rw [ae_withDensity_iff hf, ae_restrict_iff']
  · simp only [mem_setOf]
  · exact hf (measurableSet_singleton 0).compl
#align measure_theory.ae_with_density_iff_ae_restrict MeasureTheory.ae_withDensity_iff_ae_restrict

theorem aemeasurable_withDensity_ennreal_iff {f : α → ℝ≥0} (hf : Measurable f) {g : α → ℝ≥0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ≥0∞) * g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine' ⟨fun x => f x * g' x, hf.coe_nnreal_ennreal.smul g'meas, _⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine' ⟨fun x => ((f x)⁻¹ : ℝ≥0∞) * g' x, hf.coe_nnreal_ennreal.inv.smul g'meas, _⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx, ← mul_assoc, ENNReal.inv_mul_cancel h'x ENNReal.coe_ne_top, one_mul]
#align measure_theory.ae_measurable_with_density_ennreal_iff MeasureTheory.aemeasurable_withDensity_ennreal_iff

open MeasureTheory.SimpleFunc

variable {m0 : MeasurableSpace α}

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.withDensity f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.withDensity f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (h_mf : Measurable f) :
    ∀ {g : α → ℝ≥0∞}, Measurable g → ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h _ h_mea_g _ h_ind_g h_ind_h
    simp [mul_add, *, Measurable.mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => mul_le_mul_left' (h_mono_g hmn x) _
    simp [lintegral_iSup, ENNReal.mul_iSup, h_mf.mul (h_mea_g _), *]
#align measure_theory.lintegral_with_density_eq_lintegral_mul MeasureTheory.lintegral_withDensity_eq_lintegral_mul

theorem set_lintegral_withDensity_eq_set_lintegral_mul (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂μ.withDensity f = ∫⁻ x in s, (f * g) x ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul _ hf hg]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul

/-- The Lebesgue integral of `g` with respect to the measure `μ.withDensity f` coincides with
the integral of `f * g`. This version assumes that `g` is almost everywhere measurable. For a
version without conditions on `g` but requiring that `f` is almost everywhere finite, see
`lintegral_withDensity_eq_lintegral_mul_non_measurable` -/
theorem lintegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.withDensity f)) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  have : μ.withDensity f = μ.withDensity f' := withDensity_congr_ae hf.ae_eq_mk
  rw [this] at hg ⊢
  let g' := hg.mk g
  calc
    ∫⁻ a, g a ∂μ.withDensity f' = ∫⁻ a, g' a ∂μ.withDensity f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x ≠ 0 }
      · have Z := hg.ae_eq_mk
        rw [EventuallyEq, ae_withDensity_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [hx, Pi.mul_apply]
      · have M : MeasurableSet { x : α | f' x ≠ 0 }ᶜ :=
          (hf.measurable_mk (measurableSet_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
        simp only [hx, zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀' MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'

theorem lintegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ :=
  lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀

theorem lintegral_withDensity_le_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) : (∫⁻ a, g a ∂μ.withDensity f) ≤ ∫⁻ a, (f * g) a ∂μ := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  have A : f * i ≤ f * g := fun x => mul_le_mul_left' (hi x) _
  refine' le_iSup₂_of_le (f * i) (f_meas.mul i_meas) _
  exact le_iSup_of_le A (le_of_eq (lintegral_withDensity_eq_lintegral_mul _ f_meas i_meas))
#align measure_theory.lintegral_with_density_le_lintegral_mul MeasureTheory.lintegral_withDensity_le_lintegral_mul

theorem lintegral_withDensity_eq_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  refine' le_antisymm (lintegral_withDensity_le_lintegral_mul μ f_meas g) _
  rw [← iSup_lintegral_measurable_le_eq_lintegral, ← iSup_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  have A : (fun x => (f x)⁻¹ * i x) ≤ g := by
    intro x
    dsimp
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine' le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.inv.mul i_meas) _)
  refine' le_iSup_of_le A _
  rw [lintegral_withDensity_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx h'x.ne, one_mul]
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable

theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas hf]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable

theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, (f * g) a ∂μ := by
  let f' := hf.mk f
  calc
    ∫⁻ a, g a ∂μ.withDensity f = ∫⁻ a, g a ∂μ.withDensity f' := by
      rw [withDensity_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_withDensity_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀

theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ (μ : Measure α)
    {f : α → ℝ≥0∞} {s : Set α} (hf : AEMeasurable f (μ.restrict s)) (g : α → ℝ≥0∞)
    (hs : MeasurableSet s) (h'f : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    ∫⁻ a in s, g a ∂μ.withDensity f = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_withDensity hs, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hf h'f]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀ MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀

theorem withDensity_mul₀ {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g := by
  ext1 s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs, restrict_withDensity hs,
    lintegral_withDensity_eq_lintegral_mul₀ hf.restrict hg.restrict]

theorem withDensity_mul (μ : Measure α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g :=
  withDensity_mul₀ hf.aemeasurable hg.aemeasurable
#align measure_theory.with_density_mul MeasureTheory.withDensity_mul

lemma withDensity_inv_same_le {μ : Measure α} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (μ.withDensity f).withDensity f⁻¹ ≤ μ := by
  change (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) ≤ μ
  rw [← withDensity_mul₀ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) ≤ᵐ[μ] 1 by
    refine (withDensity_mono this).trans ?_
    rw [withDensity_one]
  refine ae_of_all _ (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.one_apply]
  by_cases hx_top : f x = ∞
  · simp only [hx_top, ENNReal.inv_top, mul_zero, zero_le]
  by_cases hx_zero : f x = 0
  · simp only [hx_zero, ENNReal.inv_zero, zero_mul, zero_le]
  rw [ENNReal.mul_inv_cancel hx_zero hx_top]

lemma withDensity_inv_same₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ := by
  rw [← withDensity_mul₀ hf hf.inv]
  suffices (f * fun x ↦ (f x)⁻¹) =ᵐ[μ] 1 by
    rw [withDensity_congr_ae this, withDensity_one]
  filter_upwards [hf_ne_zero, hf_ne_top] with x hf_ne_zero hf_ne_top
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_inv_cancel hf_ne_zero hf_ne_top, Pi.one_apply]

lemma withDensity_inv_same {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) = μ :=
  withDensity_inv_same₀ hf.aemeasurable hf_ne_zero hf_ne_top

/-- If `f` is almost everywhere positive and finite, then `μ ≪ μ.withDensity f`. See also
`withDensity_absolutelyContinuous` for the reverse direction, which always holds. -/
lemma withDensity_absolutelyContinuous' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    μ ≪ μ.withDensity f := by
  suffices (μ.withDensity f).withDensity (fun x ↦ (f x)⁻¹) ≪ μ.withDensity f by
    rwa [withDensity_inv_same₀ hf hf_ne_zero hf_ne_top] at this
  exact withDensity_absolutelyContinuous _ _

/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
theorem exists_absolutelyContinuous_isFiniteMeasure {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : ∃ ν : Measure α, IsFiniteMeasure ν ∧ μ ≪ ν := by
  obtain ⟨g, gpos, gmeas, hg⟩ :
    ∃ g : α → ℝ≥0, (∀ x : α, 0 < g x) ∧ Measurable g ∧ ∫⁻ x : α, ↑(g x) ∂μ < 1 :=
    exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  refine' ⟨μ.withDensity fun x => g x, isFiniteMeasure_withDensity hg.ne_top, _⟩
  have : μ = (μ.withDensity fun x => g x).withDensity fun x => (g x)⁻¹ := by
    have A : ((fun x : α => (g x : ℝ≥0∞)) * fun x : α => (g x : ℝ≥0∞)⁻¹) = 1 := by
      ext1 x
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (gpos x).ne') ENNReal.coe_ne_top
    rw [← withDensity_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A,
      withDensity_one]
  nth_rw 1 [this]
  exact withDensity_absolutelyContinuous _ _
#align measure_theory.exists_absolutely_continuous_is_finite_measure MeasureTheory.exists_absolutelyContinuous_isFiniteMeasure

end MeasureTheory
