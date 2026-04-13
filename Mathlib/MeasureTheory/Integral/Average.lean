/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

Both have a version for the Lebesgue integral rather than Bochner.

We prove several versions of the first moment method: An integrable function is below/above its
average on a set of positive measure:
* `measure_le_setLAverage_pos` for the Lebesgue integral
* `measure_le_setAverage_pos` for the Bochner integral

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## Tags

integral, center mass, average value, set average
-/

@[expose] public section


open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E F : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ ν : Measure α}
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
variable (μ) {f g : α → ℝ≥0∞}

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`, denoted `⨍⁻ x, f x ∂μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => laverage μ r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure.

It is equal to `(volume univ)⁻¹ * ∫⁻ x, f x`, so it takes value zero if the space has infinite
measure. In a probability space, the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x`, defined as `⨍⁻ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => laverage volume f) => r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ s)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `s` has infinite measure. If `s`
has measure `1`, then the average of any function is equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  laverage (Measure.restrict μ s) r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume s)⁻¹ * ∫⁻ x, f x`, so it takes value zero if `s` has infinite measure. If
`s` has measure `1`, then the average of any function is equal to its integral. -/
notation3 (prettyPrint := false)
  "⨍⁻ " (...) " in " s ", " r:60:(scoped f => laverage Measure.restrict volume s f) => r

@[simp]
theorem laverage_zero : ⨍⁻ _x, (0 : ℝ≥0∞) ∂μ = 0 := by rw [laverage, lintegral_zero]

@[simp]
theorem laverage_zero_measure (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0 := by simp [laverage]

theorem laverage_eq' (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ := rfl

theorem laverage_eq (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ := by
  rw [laverage_eq', lintegral_smul_measure, ENNReal.div_eq_inv_mul, smul_eq_mul]

theorem laverage_eq_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) :
    ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by rw [laverage, measure_univ, inv_one, one_smul]

@[simp]
theorem measure_mul_laverage [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

theorem setLAverage_eq (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s := by rw [laverage_eq, restrict_apply_univ]

theorem setLAverage_eq' (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [laverage_eq', restrict_apply_univ]

variable {μ}

theorem laverage_congr {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ := by
  simp only [laverage_eq, lintegral_congr_ae h]

theorem setLAverage_congr (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ := by
  simp only [setLAverage_eq, setLIntegral_congr h, measure_congr h]

theorem setLAverage_congr_fun_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun_ae hs h]

theorem setLAverage_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun hs h]

theorem laverage_lt_top (hf : ∫⁻ x, f x ∂μ ≠ ∞) : ⨍⁻ x, f x ∂μ < ∞ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    finiteness [measure_univ_ne_zero.2 hμ]

theorem setLAverage_lt_top : ∫⁻ x in s, f x ∂μ ≠ ∞ → ⨍⁻ x in s, f x ∂μ < ∞ :=
  laverage_lt_top

theorem laverage_add_measure :
    ⨍⁻ x, f x ∂(μ + ν) =
      μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν := by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  simp only [← ENNReal.mul_div_right_comm, measure_mul_laverage, ← ENNReal.add_div,
    ← lintegral_add_measure, ← Measure.add_apply, ← laverage_eq]

theorem measure_mul_setLAverage (f : α → ℝ≥0∞) (h : μ s ≠ ∞) :
    μ s * ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_mul_laverage, restrict_apply_univ]

theorem laverage_union (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    ⨍⁻ x in s ∪ t, f x ∂μ =
      μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t) * ⨍⁻ x in t, f x ∂μ := by
  rw [restrict_union₀ hd ht, laverage_add_measure, restrict_apply_univ, restrict_apply_univ]

theorem laverage_union_mem_openSegment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t, f x ∂μ) := by
  refine
    ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ <| add_ne_top.2 ⟨hsμ, htμ⟩,
      ENNReal.div_pos ht₀ <| add_ne_top.2 ⟨hsμ, htμ⟩, ?_, (laverage_union hd ht).symm⟩
  rw [← ENNReal.add_div,
    ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]

theorem laverage_union_mem_segment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ [⨍⁻ x in s, f x ∂μ -[ℝ≥0∞] ⨍⁻ x in t, f x ∂μ] := by
  by_cases hs₀ : μ s = 0
  · rw [← ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le _, zero_le _, ?_, (laverage_union hd ht).symm⟩
    rw [← ENNReal.add_div,
      ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]

theorem laverage_mem_openSegment_compl_self [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) :
    ⨍⁻ x, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)

@[simp]
theorem laverage_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : ℝ≥0∞) :
    ⨍⁻ _x, c ∂μ = c := by
  simp only [laverage, lintegral_const, measure_univ, mul_one]

theorem setLAverage_const (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : ℝ≥0∞) : ⨍⁻ _x in s, c ∂μ = c := by
  simp only [setLAverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]

theorem laverage_one [IsFiniteMeasure μ] [NeZero μ] : ⨍⁻ _x, (1 : ℝ≥0∞) ∂μ = 1 :=
  laverage_const _ _

theorem setLAverage_one (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : ⨍⁻ _x in s, (1 : ℝ≥0∞) ∂μ = 1 :=
  setLAverage_const hs₀ hs _

@[simp]
theorem laverage_mul_measure_univ (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    (⨍⁻ (a : α), f a ∂μ) * μ univ = ∫⁻ x, f x ∂μ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq, ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

theorem lintegral_laverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ := by
  simp

theorem setLIntegral_setLAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ _x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ :=
  lintegral_laverage _ _

@[gcongr]
theorem laverage_mono_ae (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ :=
  lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
theorem setLAverage_mono_ae (s : Set α) (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ :=
  laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self

theorem setLAverage_le_essSup (s : Set α) (f : α → ℝ≥0∞) : ⨍⁻ x in s, f x ∂μ ≤ essSup f μ := by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) (zero_le (essSup f μ))
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _

theorem laverage_le_essSup (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ ≤ essSup f μ := by
  simpa using setLAverage_le_essSup univ f

end ENNReal

section NormedAddCommGroup

variable (μ)
variable {f g : α → E}

/-- Average value of a function `f` w.r.t. a measure `μ`, denoted `⨍ x, f x ∂μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of a function `f` w.r.t. a measure `μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => average μ r

/-- Average value of a function `f` w.r.t. the standard measure.

It is equal to `(volume.real univ)⁻¹ * ∫ x, f x`, so it takes value zero if `f` is not integrable
or if the space has infinite measure. In a probability space, the average of any function is equal
to its integral.

For the average on a set, use `⨍ x in s, f x`, defined as `⨍ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => average volume f) => r

/-- Average value of a function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ.real s)⁻¹ * ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable on
`s` or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is
equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  average (Measure.restrict μ s) r

/-- Average value of a function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume.real s)⁻¹ * ∫ x, f x`, so it takes value zero `f` is not integrable on `s`
or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is equal to
its integral. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => average (Measure.restrict volume s) f) => r

@[simp]
theorem average_zero : ⨍ _, (0 : E) ∂μ = 0 := by rw [average, integral_zero]

@[simp]
theorem average_zero_measure (f : α → E) : ⨍ x, f x ∂(0 : Measure α) = 0 := by
  rw [average, smul_zero, integral_zero_measure]

@[simp]
theorem average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f

theorem average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl

theorem average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq', integral_smul_measure, ENNReal.toReal_inv, measureReal_def]

theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average, measure_univ, inv_one, one_smul]

@[simp]
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) :
    μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine (ENNReal.toReal_pos ?_ <| measure_ne_top _ _).ne'
    rwa [Ne, measure_univ_eq_zero]

theorem setAverage_eq (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ := by
  rw [average_eq, measureReal_restrict_apply_univ]

theorem setAverage_eq' (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]

variable {μ}

theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]

theorem setAverage_congr (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ := by
  simp only [setAverage_eq, setIntegral_congr_set h, measureReal_congr h]

theorem setAverage_congr_fun (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍ x in s, f x ∂μ = ⨍ x in s, g x ∂μ := by simp only [average_eq, setIntegral_congr_ae hs h]

theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      (μ.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂μ +
        (ν.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂ν := by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν]
  rw [average_eq, measureReal_add_apply]

theorem average_pair [CompleteSpace E]
    {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average

theorem measure_smul_setAverage (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    μ.real s • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ := by
  haveI := Fact.mk h.lt_top
  rw [← measure_smul_average, measureReal_restrict_apply_univ]

theorem average_union {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ =
      (μ.real s / (μ.real s + μ.real t)) • ⨍ x in s, f x ∂μ +
        (μ.real t / (μ.real s + μ.real t)) • ⨍ x in t, f x ∂μ := by
  haveI := Fact.mk hsμ.lt_top; haveI := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, measureReal_restrict_apply_univ,
    measureReal_restrict_apply_univ]

theorem average_union_mem_openSegment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < μ.real t := ENNReal.toReal_pos ht₀ htμ
  exact mem_openSegment_iff_div.mpr
    ⟨μ.real s, μ.real t, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] := by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine
      mem_segment_iff_div.mpr
        ⟨μ.real s, μ.real t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < μ.real s := ENNReal.toReal_pos hse hsμ
      _ ≤ _ := le_add_of_nonneg_right ENNReal.toReal_nonneg

theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn

variable [CompleteSpace E]

@[simp]
theorem average_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E) :
    ⨍ _x, c ∂μ = c := by
  rw [average, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

theorem setAverage_const {s : Set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) :
    ⨍ _ in s, c ∂μ = c :=
  have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _

theorem integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ := by simp

theorem setIntegral_setAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (s : Set α) :
    ∫ _ in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
  integral_average _ _

theorem integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 := by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm

theorem setAverage_sub_setAverage (hs : μ s ≠ ∞) (f : α → E) :
    ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _

theorem integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) :
    ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 := by
  rw [integral_sub (integrable_const _) hf, integral_average, sub_self]

theorem setIntegral_setAverage_sub (hs : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf

end NormedAddCommGroup

theorem ofReal_average {f : α → ℝ} (hf : Integrable f μ) (hf₀ : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, measureReal_def, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]

theorem ofReal_setAverage {f : α → ℝ} (hf : IntegrableOn f s μ) (hf₀ : 0 ≤ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) / μ s := by
  simpa using ofReal_average hf hf₀

theorem toReal_laverage {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf' : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (⨍⁻ x, f x ∂μ).toReal = ⨍ x, (f x).toReal ∂μ := by
    rw [average_eq, laverage_eq, smul_eq_mul, toReal_div, div_eq_inv_mul, ←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2), measureReal_def]

theorem toReal_setLAverage {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s))
    (hf' : ∀ᵐ x ∂μ.restrict s, f x ≠ ∞) :
    (⨍⁻ x in s, f x ∂μ).toReal = ⨍ x in s, (f x).toReal ∂μ := by
  simpa [laverage_eq] using toReal_laverage hf hf'

/-! ### First moment method -/

section FirstMomentReal
variable {N : Set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_setAverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | f x ≤ ⨍ a in s, f a ∂μ}) := by
  refine pos_iff_ne_zero.2 fun H => ?_
  replace H : (μ.restrict s) {x | f x ≤ ⨍ a in s, f a ∂μ} = 0 := by
    rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  haveI := Fact.mk hμ₁.lt_top
  refine (integral_sub_average (μ.restrict s) f).not_gt ?_
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · refine measure_mono_null (fun x hx ↦ ?_) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_setOf_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← diff_compl, ← diff_inter_self_eq_diff, measure_diff_null]
    refine measure_mono_null ?_ (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_setAverage_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | ⨍ a in s, f a ∂μ ≤ f x}) := by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_setAverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_setAverage_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_average_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | f x ≤ ⨍ a, f a ∂μ} := by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
theorem measure_average_le_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | ⨍ a, f a ∂μ ≤ f x} := by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
theorem exists_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
theorem exists_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
theorem exists_notMem_null_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍ a, f a ∂μ := by
  have := measure_le_average_pos hμ hf
  rw [← measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
theorem exists_notMem_null_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍ a, f a ∂μ ≤ f x := by
  simpa [integral_neg, neg_div] using exists_notMem_null_le_average hμ hf.neg hN

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. An integrable function is smaller than its integral on a set of
positive measure. -/
theorem measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x ≤ ∫ a, f a ∂μ} := by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. An integrable function is greater than its integral on a set of
positive measure. -/
theorem measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ ≤ f x} := by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral. -/
theorem exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The maximum of an integrable function is greater than its integral. -/
theorem exists_integral_le (hf : Integrable f μ) : ∃ x, ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral,
while avoiding a null set. -/
theorem exists_notMem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using
    exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of an integrable function is greater than its integral,
while avoiding a null set. -/
theorem exists_notMem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using
    exists_notMem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN

end ProbabilityMeasure
end FirstMomentReal

section FirstMomentENNReal
variable {N : Set α} {f : α → ℝ≥0∞}

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_setLAverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞)
    (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x ∈ s | f x ≤ ⨍⁻ a in s, f a ∂μ} := by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [← setOf_inter_eq_sep, ← Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [← setOf_inter_eq_sep, ← Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const),
    ← measure_diff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [← toReal_laverage hf, toReal_le_toReal hx (setLAverage_lt_top h).ne] at hfx
  simp_rw [ae_iff, not_ne_iff]
  exact measure_eq_top_of_lintegral_ne_top hf h

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
theorem measure_setLAverage_le_pos (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : 0 < μ {x ∈ s | ⨍⁻ a in s, f a ∂μ ≤ f x} := by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLAverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [← setOf_inter_eq_sep, ← Measure.restrict_apply₀' hs, hfg']
  rw [← setOf_inter_eq_sep, ← Measure.restrict_apply₀' hs, ←
    measure_diff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [← toReal_laverage hg.aemeasurable, toReal_le_toReal (setLAverage_lt_top hint).ne hx] at hfx
  · exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
theorem exists_le_setLAverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : AEMeasurable f (μ.restrict s)) :
    ∃ x ∈ s, f x ≤ ⨍⁻ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
theorem exists_setLAverage_le (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : ∃ x ∈ s, ⨍⁻ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLAverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
theorem measure_laverage_le_pos (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
    0 < μ {x | ⨍⁻ a, f a ∂μ ≤ f x} := by
  simpa [hint] using
    @measure_setLAverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
theorem exists_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ⨍⁻ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean, while
avoiding a null set. -/
theorem exists_notMem_null_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a : α, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍⁻ a, f a ∂μ ≤ f x := by
  have := measure_laverage_le_pos hμ hint
  rw [← measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

section FiniteMeasure
variable [IsFiniteMeasure μ]

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
theorem measure_le_laverage_pos (hμ : μ ≠ 0) (hf : AEMeasurable f μ) :
    0 < μ {x | f x ≤ ⨍⁻ a, f a ∂μ} := by
  simpa using
    measure_le_setLAverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
theorem exists_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) : ∃ x, f x ≤ ⨍⁻ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The minimum of a measurable function is smaller than its mean, while
avoiding a null set. -/
theorem exists_notMem_null_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍⁻ a, f a ∂μ := by
  have := measure_le_laverage_pos hμ hf
  rw [← measure_diff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. A measurable function is smaller than its integral on a set f
positive measure. -/
theorem measure_le_lintegral_pos (hf : AEMeasurable f μ) : 0 < μ {x | f x ≤ ∫⁻ a, f a ∂μ} := by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. A measurable function is greater than its integral on a set f
positive measure. -/
theorem measure_lintegral_le_pos (hint : ∫⁻ a, f a ∂μ ≠ ∞) : 0 < μ {x | ∫⁻ a, f a ∂μ ≤ f x} := by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral. -/
theorem exists_le_lintegral (hf : AEMeasurable f μ) : ∃ x, f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The maximum of a measurable function is greater than its integral. -/
theorem exists_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral,
while avoiding a null set. -/
theorem exists_notMem_null_le_lintegral (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of a measurable function is greater than its integral,
while avoiding a null set. -/
theorem exists_notMem_null_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN

end ProbabilityMeasure
end FirstMomentENNReal

/-- If the average of a function `f` along a sequence of sets `aₙ` converges to `c` (more precisely,
we require that `⨍ y in a i, ‖f y - c‖ ∂μ` tends to `0`), then the integral of `gₙ • f` also tends
to `c` if `gₙ` is supported in `aₙ`, has integral converging to one and supremum at most `K / μ aₙ`.
-/
theorem tendsto_integral_smul_of_tendsto_average_norm_sub
    [CompleteSpace E]
    {ι : Type*} {a : ι → Set α} {l : Filter ι} {f : α → E} {c : E} {g : ι → α → ℝ} (K : ℝ)
    (hf : Tendsto (fun i ↦ ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0))
    (f_int : ∀ᶠ i in l, IntegrableOn f (a i) μ)
    (hg : Tendsto (fun i ↦ ∫ y, g i y ∂μ) l (𝓝 1))
    (g_supp : ∀ᶠ i in l, Function.support (g i) ⊆ a i)
    (g_bound : ∀ᶠ i in l, ∀ x, |g i x| ≤ K / μ.real (a i)) :
    Tendsto (fun i ↦ ∫ y, g i y • f y ∂μ) l (𝓝 c) := by
  have g_int : ∀ᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : ∀ᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    rw [← integral_smul_const, ← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y ↦ g i y • f y) ⊆ a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memLp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / μ.real (a i)) (Eventually.of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i ↦ ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.toReal_top, _root_.div_zero, abs_nonpos_iff, measureReal_def] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_const_mul, norm_smul, ← mul_assoc,
      ← div_eq_mul_inv]
    have : ∀ x, x ∉ a i → ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.notMem_support]; exact fun h ↦ hx (hi h)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x ↦ by positivity)) ?_
      (Eventually.of_forall (fun x ↦ ?_))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ ↦ c) (a i) μ
      simp [mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

/-- If `s` is a connected set of finite, nonzero `μ`-measure and `f : α → ℝ` is continuous on `s`
and integrable on `s` w.r.t. `μ`, then `f` attains its `μ`-average on `s`. -/
theorem exists_eq_setAverage
    [TopologicalSpace α] {f : α → ℝ} (hs : IsConnected s) (hf : ContinuousOn f s)
    (hint : IntegrableOn f s μ) (hμfin : μ s ≠ ⊤) (hμ0 : μ s ≠ 0) :
    ∃ c ∈ s, f c = ⨍ x in s, f x ∂μ := by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x ∈ s ∧ f x ≤ ave}
  let S₂ : Set α := {x | x ∈ s ∧ ave ≤ f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind

end MeasureTheory
