/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Density
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform distributions and probability mass functions
This file defines two related notions of uniform distributions, which will be unified in the future.

# Uniform distributions

Defines the uniform distribution for any set with finite measure.

## Main definitions
* `IsUniform X s ℙ μ` : A random variable `X` has uniform distribution on `s` under `ℙ` if the
  push-forward measure agrees with the rescaled restricted measure `μ`.

# Uniform probability mass functions

This file defines a number of uniform `PMF` distributions from various inputs,
  uniformly drawing from the corresponding object.

## Main definitions
`PMF.uniformOfFinset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`PMF.uniformOfFintype` gives all elements equal probability,
  equal to the inverse of the size of the `Fintype`.

`PMF.ofMultiset` draws randomly from the given `Multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `Multiset`

## TODO
* Refactor the `PMF` definitions to come from a `uniformMeasure` on a `Finset`/`Fintype`/`Multiset`.
-/

open scoped Finset MeasureTheory NNReal ENNReal

-- TODO: We can't `open ProbabilityTheory` without opening the `ProbabilityTheory` locale :(
open TopologicalSpace MeasureTheory.Measure PMF

noncomputable section

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace pdf

variable {Ω : Type*}
variable {_ : MeasurableSpace Ω} {ℙ : Measure Ω}

/-- A random variable `X` has uniform distribution on `s` if its push-forward measure is
`(μ s)⁻¹ • μ.restrict s`. -/
def IsUniform (X : Ω → E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :=
  map X ℙ = ProbabilityTheory.cond μ s

namespace IsUniform

theorem aemeasurable {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : AEMeasurable X ℙ := by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' ℝ≥0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hns hnt]

theorem absolutelyContinuous {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) : map X ℙ ≪ μ := by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous

theorem measure_preimage {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) :
    ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s := by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]

theorem isProbabilityMeasure {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this, hu.measure_preimage hns hnt MeasurableSet.univ, Set.inter_univ,
      ENNReal.div_self hns hnt]⟩

theorem toMeasurable_iff {X : Ω → E} {s : Set E} :
    IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ := by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]

protected theorem toMeasurable {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) :
    IsUniform X (toMeasurable μ s) ℙ μ := by
  unfold IsUniform at *
  rwa [ProbabilityTheory.cond_toMeasurable_eq]

theorem hasPDF {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ := by
  let t := toMeasurable μ s
  apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1)) <|
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu, withDensity_indicator (measurableSet_toMeasurable μ s), withDensity_smul _ measurable_one,
    withDensity_one, restrict_toMeasurable hnt, measure_toMeasurable, ProbabilityTheory.cond]

theorem pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω → E} {s : Set E}
    (hu : IsUniform X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rcases hμs with H|H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

theorem pdf_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) := by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ μ := hasPDF hns hnt hu
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hns hnt hu
  apply (eq_of_map_eq_withDensity _ _).mp
  · rw [hu, withDensity_indicator hms, withDensity_smul _ measurable_one, withDensity_one,
      ProbabilityTheory.cond]
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms

theorem pdf_toReal_ae_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

variable {X : Ω → ℝ} {s : Set ℝ}

theorem mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal := by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x ↦ x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hnt.1 hnt.2 huX
  constructor
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine hasFiniteIntegral_mul (pdf_eq hcs.measurableSet huX) ?_
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)
  have : ∀ x, ‖x‖ₑ * s.indicator ind x = s.indicator (fun x => ‖x‖ₑ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [ind, this, lintegral_indicator hcs.measurableSet, mul_one, Algebra.id.smul_eq_mul,
    Pi.one_apply, Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_enorm]
  exact ENNReal.mul_ne_top (setLIntegral_lt_top_of_isCompact hnt.2 hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hnt.1)).ne

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  rw [← smul_eq_mul, ← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasurable]
    rwa [aestronglyMeasurable_iff_aemeasurable]

end IsUniform

variable {X : Ω → E}

lemma IsUniform.cond {s : Set E} :
    IsUniform (id : E → E) s (ProbabilityTheory.cond μ s) μ := by
  unfold IsUniform
  rw [Measure.map_id]

/-- The density of the uniform measure on a set with respect to itself. This allows us to abstract
away the choice of random variable and probability space. -/
def uniformPDF (s : Set E) (x : E) (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x

/-- Check that indeed any uniform random variable has the uniformPDF. -/
lemma uniformPDF_eq_pdf {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X s ℙ μ) :
    (fun x ↦ uniformPDF s x μ) =ᵐ[μ] pdf X ℙ μ := by
  unfold uniformPDF
  exact Filter.EventuallyEq.trans (pdf.IsUniform.pdf_eq hs hu).symm (ae_eq_refl _)

open scoped Classical in
/-- Alternative way of writing the uniformPDF. -/
lemma uniformPDF_ite {s : Set E} {x : E} :
    uniformPDF s x μ = if x ∈ s then (μ s)⁻¹ else 0 := by
  unfold uniformPDF
  unfold Set.indicator
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end pdf

end MeasureTheory

namespace PMF

variable {α : Type*}

open scoped NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

theorem uniformOfFinset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

theorem uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]

@[deprecated (since := "2025-05-23")]
alias uniformOfFinset_apply_of_not_mem := uniformOfFinset_apply_of_notMem

@[simp]
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff, Finset.ne_empty_of_mem ha])

theorem mem_support_uniformOfFinset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s with x ∈ t, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, if_true, uniformOfFinset_apply]

@[simp]
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]

theorem mem_support_uniformOfFintype (a : α) : a ∈ (uniformOfFintype α).support := by simp

section Measure

variable (s : Set α)

theorem toOuterMeasure_uniformOfFintype_apply [Fintype s] :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformOfFintype, toOuterMeasure_uniformOfFinset_apply, Fintype.card_subtype,
    Finset.card_univ]

theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

end Measure

end UniformOfFintype

section OfMultiset

open scoped Classical in
/-- Given a non-empty multiset `s` we construct the `PMF` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : ℝ≥0∞) / (Multiset.card s))
          = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑' b, (s.count b : ℝ≥0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
        _ = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑ b ∈ s.toFinset, (s.count b : ℝ≥0∞) :=
          (congr_arg (fun x => (Multiset.card s : ℝ≥0∞)⁻¹ * x)
            (tsum_eq_sum fun a ha =>
              Nat.cast_eq_zero.2 <| by rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]))
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq s,
            ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.natCast_ne_top _)]
        )⟩

variable {s : Multiset α} (hs : s ≠ 0)

open scoped Classical in
@[simp]
theorem ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card s) :=
  rfl

open scoped Classical in
@[simp]
theorem support_ofMultiset : (ofMultiset s hs).support = s.toFinset :=
  Set.ext (by simp [mem_support_iff, hs])

open scoped Classical in
theorem mem_support_ofMultiset_iff (a : α) : a ∈ (ofMultiset s hs).support ↔ a ∈ s.toFinset := by
  simp

theorem ofMultiset_apply_of_notMem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 := by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.natCast_ne_top, or_false] using ha

@[deprecated (since := "2025-05-23")]
alias ofMultiset_apply_of_not_mem := ofMultiset_apply_of_notMem

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_ofMultiset_apply :
    (ofMultiset s hs).toOuterMeasure t =
      (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) := by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ t <;> simp [Set.indicator, hx, div_eq_mul_inv]

open scoped Classical in
@[simp]
theorem toMeasure_ofMultiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofMultiset_apply hs t)

end Measure

end OfMultiset

end PMF
