/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Yaël Dillies
-/
import Mathlib.MeasureTheory.Integral.SetIntegral

#align_import measure_theory.integral.average from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

Both have a version for the Lebesgue integral rather than Bochner.

We prove several version of the first moment method: An integrable function is below/above its
average on a set of positive measure.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## TODO

Provide the first moment method for the Lebesgue integral as well. A draft is available on branch
`first_moment_lintegral` in mathlib3 repository.

## Tags

integral, center mass, average value
-/


open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology BigOperators ENNReal Convex

variable {α E F : Type _} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ ν : Measure α}
  {s t : Set α}

/-!
### Average value of a function w.r.t. a measure

The (Bochner, Lebesgue) average value of a function `f` w.r.t. a measure `μ` (notation:
`⨍ x, f x ∂μ`, `⨍⁻ x, f x ∂μ`) is defined as the (Bochner, Lebesgue) integral divided by the total
measure, so it is equal to zero if `μ` is an infinite measure, and (typically) equal to infinity if
`f` is not integrable. If `μ` is a probability measure, then the average of any function is equal to
its integral.
-/

namespace MeasureTheory
section ENNReal
variable (μ)
variable {f g : α → ℝ≥0∞}

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`, notation: `⨍⁻ x, f x ∂μ`.
It is defined as `μ univ⁻¹ * ∫⁻ x, f x ∂μ`, so it is equal to zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ` (defined as `⨍⁻ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ
#align measure_theory.laverage MeasureTheory.laverage

notation3"⨍⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => laverage μ r
notation3"⨍⁻ "(...)", "r:60:(scoped f => laverage volume f) => r
notation3"⨍⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => laverage (Measure.restrict μ s) r
notation3 (prettyPrint := false)
  "⨍⁻ "(...)" in "s", "r:60:(scoped f => laverage Measure.restrict volume s f) => r

@[simp]
theorem laverage_zero : ⨍⁻ _x, (0 : ℝ≥0∞) ∂μ = 0 := by rw [laverage, lintegral_zero]
#align measure_theory.laverage_zero MeasureTheory.laverage_zero

@[simp]
theorem laverage_zero_measure (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0 := by simp [laverage]
#align measure_theory.laverage_zero_measure MeasureTheory.laverage_zero_measure

theorem laverage_eq' (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ := rfl
#align measure_theory.laverage_eq' MeasureTheory.laverage_eq'

theorem laverage_eq (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ := by
  rw [laverage_eq', lintegral_smul_measure, ENNReal.div_eq_inv_mul]
#align measure_theory.laverage_eq MeasureTheory.laverage_eq

theorem laverage_eq_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) :
    ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by rw [laverage, measure_univ, inv_one, one_smul]
#align measure_theory.laverage_eq_lintegral MeasureTheory.laverage_eq_lintegral

@[simp]
theorem measure_mul_laverage [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  cases' eq_or_ne μ 0 with hμ hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, MulZeroClass.mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel' (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]
#align measure_theory.measure_mul_laverage MeasureTheory.measure_mul_laverage

theorem setLaverage_eq (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s := by rw [laverage_eq, restrict_apply_univ]
#align measure_theory.set_laverage_eq MeasureTheory.setLaverage_eq

theorem setLaverage_eq' (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [laverage_eq', restrict_apply_univ]
#align measure_theory.set_laverage_eq' MeasureTheory.setLaverage_eq'

variable {μ}

theorem laverage_congr {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ := by
  simp only [laverage_eq, lintegral_congr_ae h]
#align measure_theory.laverage_congr MeasureTheory.laverage_congr

theorem setLaverage_congr (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ := by
  simp only [setLaverage_eq, set_lintegral_congr h, measure_congr h]
#align measure_theory.set_laverage_congr MeasureTheory.setLaverage_congr

theorem setLaverage_congr_fun (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, set_lintegral_congr_fun hs h]
#align measure_theory.set_laverage_congr_fun MeasureTheory.setLaverage_congr_fun

theorem laverage_lt_top (hf : ∫⁻ x, f x ∂μ ≠ ∞) : ⨍⁻ x, f x ∂μ < ∞ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    exact div_lt_top hf (measure_univ_ne_zero.2 hμ)
#align measure_theory.laverage_lt_top MeasureTheory.laverage_lt_top

theorem setLaverage_lt_top : ∫⁻ x in s, f x ∂μ ≠ ∞ → ⨍⁻ x in s, f x ∂μ < ∞ :=
  laverage_lt_top
#align measure_theory.set_laverage_lt_top MeasureTheory.setLaverage_lt_top

theorem laverage_add_measure :
    ⨍⁻ x, f x ∂(μ + ν) =
      μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν := by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  haveI := hμ; haveI := hν
  simp only [←ENNReal.mul_div_right_comm, measure_mul_laverage, ←ENNReal.add_div,
    ←lintegral_add_measure, ←Measure.add_apply, ←laverage_eq]
#align measure_theory.laverage_add_measure MeasureTheory.laverage_add_measure

theorem measure_mul_setLaverage (f : α → ℝ≥0∞) (h : μ s ≠ ∞) :
    μ s * ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [←measure_mul_laverage, restrict_apply_univ]
#align measure_theory.measure_mul_set_laverage MeasureTheory.measure_mul_setLaverage

theorem laverage_union (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    ⨍⁻ x in s ∪ t, f x ∂μ =
      μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t) * ⨍⁻ x in t, f x ∂μ :=
  by rw [restrict_union₀ hd ht, laverage_add_measure, restrict_apply_univ, restrict_apply_univ]
#align measure_theory.laverage_union MeasureTheory.laverage_union

theorem laverage_union_mem_openSegment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t, f x ∂μ) := by
  refine'
    ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ <| add_ne_top.2 ⟨hsμ, htμ⟩,
      ENNReal.div_pos ht₀ <| add_ne_top.2 ⟨hsμ, htμ⟩, _, (laverage_union hd ht).symm⟩
  rw [←ENNReal.add_div,
    ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]
#align measure_theory.laverage_union_mem_open_segment MeasureTheory.laverage_union_mem_openSegment

theorem laverage_union_mem_segment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ [⨍⁻ x in s, f x ∂μ -[ℝ≥0∞] ⨍⁻ x in t, f x ∂μ] := by
  by_cases hs₀ : μ s = 0
  · rw [←ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine'
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le _, zero_le _, _, (laverage_union hd ht).symm⟩
    rw [←ENNReal.add_div,
      ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]
#align measure_theory.laverage_union_mem_segment MeasureTheory.laverage_union_mem_segment

theorem laverage_mem_openSegment_compl_self [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) :
    ⨍⁻ x, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)
#align measure_theory.laverage_mem_open_segment_compl_self MeasureTheory.laverage_mem_openSegment_compl_self

@[simp]
theorem laverage_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : ℝ≥0∞) :
    ⨍⁻ _x, c ∂μ = c := by
  simp only [laverage, lintegral_const, measure_univ, mul_one]
#align measure_theory.laverage_const MeasureTheory.laverage_const

theorem setLaverage_const (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : ℝ≥0∞) : ⨍⁻ _x in s, c ∂μ = c := by
  simp only [setLaverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]
#align measure_theory.set_laverage_const MeasureTheory.setLaverage_const

theorem laverage_one [IsFiniteMeasure μ] [NeZero μ] : ⨍⁻ _x, (1 : ℝ≥0∞) ∂μ = 1 :=
  laverage_const _ _
#align measure_theory.laverage_one MeasureTheory.laverage_one

theorem setLaverage_one (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : ⨍⁻ _x in s, (1 : ℝ≥0∞) ∂μ = 1 :=
  setLaverage_const hs₀ hs _
#align measure_theory.set_laverage_one MeasureTheory.setLaverage_one

--porting note: Dropped `simp` because of `simp` seeing through `1 : α → ℝ≥0∞` and applying
-- `lintegral_const`. This is suboptimal.
theorem lintegral_laverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [lintegral_const, laverage_eq,
      ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]
#align measure_theory.lintegral_laverage MeasureTheory.lintegral_laverage

theorem setLintegral_setLaverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ _x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ :=
  lintegral_laverage _ _
#align measure_theory.set_lintegral_set_laverage MeasureTheory.setLintegral_setLaverage

end ENNReal

section NormedAddCommGroup

variable (μ)
variable {f g : α → E}

/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍ x, f x ∂μ`. It is defined as
`(μ univ).toReal⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

For the average on a set, use `⨍ x in s, f x ∂μ` (defined as `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ
#align measure_theory.average MeasureTheory.average

@[inherit_doc average]
notation3 "⨍ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => average μ r

@[inherit_doc average]
notation3 "⨍ "(...)", "r:60:(scoped f => average volume f) => r

@[inherit_doc average]
notation3 "⨍ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => average (Measure.restrict μ s) r

@[inherit_doc average]
notation3 "⨍ "(...)" in "s", "r:60:(scoped f => average (Measure.restrict volume s) f) => r

@[simp]
theorem average_zero : ⨍ _, (0 : E) ∂μ = 0 := by rw [average, integral_zero]
#align measure_theory.average_zero MeasureTheory.average_zero

@[simp]
theorem average_zero_measure (f : α → E) : ⨍ x, f x ∂(0 : Measure α) = 0 := by
  rw [average, smul_zero, integral_zero_measure]
#align measure_theory.average_zero_measure MeasureTheory.average_zero_measure

@[simp]
theorem average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f
#align measure_theory.average_neg MeasureTheory.average_neg

theorem average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl
#align measure_theory.average_eq' MeasureTheory.average_eq'

theorem average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq', integral_smul_measure, ENNReal.toReal_inv]
#align measure_theory.average_eq MeasureTheory.average_eq

theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average, measure_univ, inv_one, one_smul]
#align measure_theory.average_eq_integral MeasureTheory.average_eq_integral

@[simp]
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) :
    (μ univ).toReal • ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  cases' eq_or_ne μ 0 with hμ hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine' (ENNReal.toReal_pos _ <| measure_ne_top _ _).ne'
    rwa [Ne.def, measure_univ_eq_zero]
#align measure_theory.measure_smul_average MeasureTheory.measure_smul_average

theorem setAverage_eq (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by rw [average_eq, restrict_apply_univ]
#align measure_theory.set_average_eq MeasureTheory.setAverage_eq

theorem setAverage_eq' (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]
#align measure_theory.set_average_eq' MeasureTheory.setAverage_eq'

variable {μ}

theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]
#align measure_theory.average_congr MeasureTheory.average_congr

theorem setAverage_congr (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ := by
  simp only [setAverage_eq, set_integral_congr_set_ae h, measure_congr h]
#align measure_theory.set_average_congr MeasureTheory.setAverage_congr

theorem setAverage_congr_fun (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍ x in s, f x ∂μ = ⨍ x in s, g x ∂μ := by simp only [average_eq, set_integral_congr_ae hs h]
#align measure_theory.set_average_congr_fun MeasureTheory.setAverage_congr_fun

theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      ((μ univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂μ +
        ((ν univ).toReal / ((μ univ).toReal + (ν univ).toReal)) • ⨍ x, f x ∂ν := by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ←smul_add,
    ←integral_add_measure hμ hν, ←ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _)]
  rw [average_eq, Measure.add_apply]
#align measure_theory.average_add_measure MeasureTheory.average_add_measure

theorem average_pair {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average
#align measure_theory.average_pair MeasureTheory.average_pair

theorem measure_smul_setAverage (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    (μ s).toReal • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ := by
  haveI := Fact.mk h.lt_top
  rw [←measure_smul_average, restrict_apply_univ]
#align measure_theory.measure_smul_set_average MeasureTheory.measure_smul_setAverage

theorem average_union {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ =
      ((μ s).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in s, f x ∂μ +
        ((μ t).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in t, f x ∂μ := by
  haveI := Fact.mk hsμ.lt_top; haveI := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, restrict_apply_univ, restrict_apply_univ]
#align measure_theory.average_union MeasureTheory.average_union

theorem average_union_mem_openSegment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < (μ s).toReal; exact ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < (μ t).toReal; exact ENNReal.toReal_pos ht₀ htμ
  refine' mem_openSegment_iff_div.mpr
    ⟨(μ s).toReal, (μ t).toReal, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩
#align measure_theory.average_union_mem_open_segment MeasureTheory.average_union_mem_openSegment

theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] := by
  by_cases hse : μ s = 0
  · rw [←ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine'
      mem_segment_iff_div.mpr
        ⟨(μ s).toReal, (μ t).toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, _,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < (μ s).toReal := ENNReal.toReal_pos hse hsμ
      _ ≤ _ := le_add_of_nonneg_right ENNReal.toReal_nonneg
#align measure_theory.average_union_mem_segment MeasureTheory.average_union_mem_segment

theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn
#align measure_theory.average_mem_open_segment_compl_self MeasureTheory.average_mem_openSegment_compl_self

@[simp]
theorem average_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E) :
    ⨍ _x, c ∂μ = c := by
  rw [average, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
#align measure_theory.average_const MeasureTheory.average_const

theorem setAverage_const {s : Set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) :
    ⨍ _ in s, c ∂μ = c :=
  have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _
#align measure_theory.set_average_const MeasureTheory.setAverage_const

-- porting note: was `@[simp]` but `simp` can prove it
theorem integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ := by simp
#align measure_theory.integral_average MeasureTheory.integral_average

theorem setIntegral_setAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (s : Set α) :
    ∫ _ in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
  integral_average _ _
#align measure_theory.set_integral_set_average MeasureTheory.setIntegral_setAverage

theorem integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 := by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm
#align measure_theory.integral_sub_average MeasureTheory.integral_sub_average

theorem setAverage_sub_setAverage (hs : μ s ≠ ∞) (f : α → E) :
    ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _
#align measure_theory.set_integral_sub_set_average MeasureTheory.setAverage_sub_setAverage

theorem integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) :
    ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 := by
  rw [integral_sub (integrable_const _) hf, integral_average, sub_self]
#align measure_theory.integral_average_sub MeasureTheory.integral_average_sub

theorem setIntegral_setAverage_sub (hs : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf
#align measure_theory.set_integral_set_average_sub MeasureTheory.setIntegral_setAverage_sub

end NormedAddCommGroup

theorem ofReal_average {f : α → ℝ} (hf : Integrable f μ) (hf₀ : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]
#align measure_theory.of_real_average MeasureTheory.ofReal_average

theorem ofReal_setAverage {f : α → ℝ} (hf : IntegrableOn f s μ) (hf₀ : 0 ≤ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) / μ s := by
  simpa using ofReal_average hf hf₀
#align measure_theory.of_real_set_average MeasureTheory.ofReal_setAverage

theorem toReal_laverage {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf' : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (⨍⁻ x, f x ∂μ).toReal = ⨍ x, (f x).toReal ∂μ := by
    rw [average_eq, laverage_eq, smul_eq_mul, toReal_div, div_eq_inv_mul, ←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2)]
#align measure_theory.to_real_laverage MeasureTheory.toReal_laverage

theorem toReal_setLaverage {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s))
    (hf' : ∀ᵐ x ∂μ.restrict s, f x ≠ ∞) :
    (⨍⁻ x in s, f x ∂μ).toReal = ⨍ x in s, (f x).toReal ∂μ := by
  simpa [laverage_eq] using toReal_laverage hf hf'
#align measure_theory.to_real_set_laverage MeasureTheory.toReal_setLaverage

/-! ### First moment method -/

section FirstMomentReal
variable {N : Set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_setAverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | f x ≤ ⨍ a in s, f a ∂μ}) := by
  refine' pos_iff_ne_zero.2 fun H => _
  replace H : (μ.restrict s) {x | f x ≤ ⨍ a in s, f a ∂μ} = 0
  · rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  haveI := Fact.mk hμ₁.lt_top
  refine' (integral_sub_average (μ.restrict s) f).not_gt _
  refine' (set_integral_pos_iff_support_of_nonneg_ae _ _).2 _
  · refine' eq_bot_mono (measure_mono fun x hx => _) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_setOf_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const.2 <| Or.inr <| lt_top_iff_ne_top.2 hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← diff_compl, ← diff_inter_self_eq_diff, measure_diff_null]
    refine' eq_bot_mono (measure_mono _) (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le
#align measure_theory.measure_le_set_average_pos MeasureTheory.measure_le_setAverage_pos

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_setAverage_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | ⨍ a in s, f a ∂μ ≤ f x}) := by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg
#align measure_theory.measure_set_average_le_pos MeasureTheory.measure_setAverage_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_setAverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_le_set_average MeasureTheory.exists_le_setAverage

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_setAverage_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_set_average_le MeasureTheory.exists_setAverage_le

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_average_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | f x ≤ ⨍ a, f a ∂μ} := by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn
#align measure_theory.measure_le_average_pos MeasureTheory.measure_le_average_pos

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_average_le_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | ⨍ a, f a ∂μ ≤ f x} := by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn
#align measure_theory.measure_average_le_pos MeasureTheory.measure_average_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩
#align measure_theory.exists_le_average MeasureTheory.exists_le_average

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩
#align measure_theory.exists_average_le MeasureTheory.exists_average_le

/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
theorem exists_not_mem_null_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍ a, f a ∂μ := by
  have := measure_le_average_pos hμ hf
  rw [← measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩
#align measure_theory.exists_not_mem_null_le_average MeasureTheory.exists_not_mem_null_le_average

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
theorem exists_not_mem_null_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍ a, f a ∂μ ≤ f x := by
  simpa [integral_neg, neg_div] using exists_not_mem_null_le_average hμ hf.neg hN
#align measure_theory.exists_not_mem_null_average_le MeasureTheory.exists_not_mem_null_average_le

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. An integrable function is smaller than its integral on a set of
positive measure. -/
theorem measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x ≤ ∫ a, f a ∂μ} := by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.measure_le_integral_pos MeasureTheory.measure_le_integral_pos

/-- **First moment method**. An integrable function is greater than its integral on a set of
positive measure. -/
theorem measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ ≤ f x} := by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.measure_integral_le_pos MeasureTheory.measure_integral_le_pos

/-- **First moment method**. The minimum of an integrable function is smaller than its integral. -/
theorem exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.exists_le_integral MeasureTheory.exists_le_integral

/-- **First moment method**. The maximum of an integrable function is greater than its integral. -/
theorem exists_integral_le (hf : Integrable f μ) : ∃ x, ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.exists_integral_le MeasureTheory.exists_integral_le

/-- **First moment method**. The minimum of an integrable function is smaller than its integral,
while avoiding a null set. -/
theorem exists_not_mem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using
    exists_not_mem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN
#align measure_theory.exists_not_mem_null_le_integral MeasureTheory.exists_not_mem_null_le_integral

/-- **First moment method**. The maximum of an integrable function is greater than its integral,
while avoiding a null set. -/
theorem exists_not_mem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using
    exists_not_mem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN
#align measure_theory.exists_not_mem_null_integral_le MeasureTheory.exists_not_mem_null_integral_le

end ProbabilityMeasure
end FirstMomentReal

section FirstMomentEnnreal
variable {N : Set α} {f : α → ℝ≥0∞}

/-- **First moment method**. A measurable function is smaller than its mean on a set of ositive
measure. -/
theorem measure_le_setLaverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞)
    (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x ∈ s | f x ≤ ⨍⁻ a in s, f a ∂μ} := by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [←setOf_inter_eq_sep, ←Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [←setOf_inter_eq_sep, ←Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const),
    ←measure_diff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine' this.trans_le (measure_mono _)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [←toReal_laverage hf, toReal_le_toReal hx (setLaverage_lt_top h).ne] at hfx
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hf h
#align measure_theory.measure_le_set_laverage_pos MeasureTheory.measure_le_setLaverage_pos

/-- **First moment method**. A measurable function is greater than its mean on a set of ositive
measure. -/
theorem measure_setLaverage_le_pos (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : 0 < μ {x ∈ s | ⨍⁻ a in s, f a ∂μ ≤ f x} := by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLaverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [←setOf_inter_eq_sep, ←Measure.restrict_apply₀' hs, hfg']
  rw [←setOf_inter_eq_sep, ←Measure.restrict_apply₀' hs, ←
    measure_diff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine' this.trans_le (measure_mono _)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [←toReal_laverage hg.aemeasurable, toReal_le_toReal (setLaverage_lt_top hint).ne hx] at hfx
  exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint
#align measure_theory.measure_set_laverage_le_pos MeasureTheory.measure_setLaverage_le_pos

/-- **First moment method**. The minimum of a measurable function is smaller than its ean. -/
theorem exists_le_setLaverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : AEMeasurable f (μ.restrict s)) :
    ∃ x ∈ s, f x ≤ ⨍⁻ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLaverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_le_set_laverage MeasureTheory.exists_le_setLaverage

/-- **First moment method**. The maximum of a measurable function is greater than its ean. -/
theorem exists_setLaverage_le (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : ∃ x ∈ s, ⨍⁻ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLaverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩
#align measure_theory.exists_set_laverage_le MeasureTheory.exists_setLaverage_le

/-- **First moment method**. A measurable function is greater than its mean on a set of ositive
measure. -/
theorem measure_laverage_le_pos (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
    0 < μ {x | ⨍⁻ a, f a ∂μ ≤ f x} := by
  simpa [hint] using
    @measure_setLaverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ
#align measure_theory.measure_laverage_le_pos MeasureTheory.measure_laverage_le_pos

/-- **First moment method**. The maximum of a measurable function is greater than its ean. -/
theorem exists_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ⨍⁻ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩
#align measure_theory.exists_laverage_le MeasureTheory.exists_laverage_le

/-- **First moment method**. The maximum of a measurable function is greater than its ean, while
avoiding a null set. -/
theorem exists_not_mem_null_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a : α, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍⁻ a, f a ∂μ ≤ f x := by
  have := measure_laverage_le_pos hμ hint
  rw [←measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩
#align measure_theory.exists_not_mem_null_laverage_le MeasureTheory.exists_not_mem_null_laverage_le

section FiniteMeasure
variable [IsFiniteMeasure μ]

/-- **First moment method**. A measurable function is smaller than its mean on a set of ositive
measure. -/
theorem measure_le_laverage_pos (hμ : μ ≠ 0) (hf : AEMeasurable f μ) :
    0 < μ {x | f x ≤ ⨍⁻ a, f a ∂μ} := by
  simpa using
    measure_le_setLaverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict
#align measure_theory.measure_le_laverage_pos MeasureTheory.measure_le_laverage_pos

/-- **First moment method**. The minimum of a measurable function is smaller than its ean. -/
theorem exists_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) : ∃ x, f x ≤ ⨍⁻ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩
#align measure_theory.exists_le_laverage MeasureTheory.exists_le_laverage

/-- **First moment method**. The minimum of a measurable function is smaller than its ean, while
avoiding a null set. -/
theorem exists_not_mem_null_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍⁻ a, f a ∂μ := by
  have := measure_le_laverage_pos hμ hf
  rw [←measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩
#align measure_theory.exists_not_mem_null_le_laverage MeasureTheory.exists_not_mem_null_le_laverage

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. A measurable function is smaller than its integral on a set f
positive measure. -/
theorem measure_le_lintegral_pos (hf : AEMeasurable f μ) : 0 < μ {x | f x ≤ ∫⁻ a, f a ∂μ} := by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.measure_le_lintegral_pos MeasureTheory.measure_le_lintegral_pos

/-- **First moment method**. A measurable function is greater than its integral on a set f
positive measure. -/
theorem measure_lintegral_le_pos (hint : ∫⁻ a, f a ∂μ ≠ ∞) : 0 < μ {x | ∫⁻ a, f a ∂μ ≤ f x} := by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint
#align measure_theory.measure_lintegral_le_pos MeasureTheory.measure_lintegral_le_pos

/-- **First moment method**. The minimum of a measurable function is smaller than its ntegral. -/
theorem exists_le_lintegral (hf : AEMeasurable f μ) : ∃ x, f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf
#align measure_theory.exists_le_lintegral MeasureTheory.exists_le_lintegral

/-- **First moment method**. The maximum of a measurable function is greater than its ntegral. -/
theorem exists_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint
#align measure_theory.exists_lintegral_le MeasureTheory.exists_lintegral_le

/-- **First moment method**. The minimum of a measurable function is smaller than its ntegral,
while avoiding a null set. -/
theorem exists_not_mem_null_le_lintegral (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using
    exists_not_mem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN
#align measure_theory.exists_not_mem_null_le_lintegral MeasureTheory.exists_not_mem_null_le_lintegral

/-- **First moment method**. The maximum of a measurable function is greater than its ntegral,
while avoiding a null set. -/
theorem exists_not_mem_null_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_not_mem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN
#align measure_theory.exists_not_mem_null_lintegral_le MeasureTheory.exists_not_mem_null_lintegral_le

end ProbabilityMeasure
end FirstMomentEnnreal
end MeasureTheory
