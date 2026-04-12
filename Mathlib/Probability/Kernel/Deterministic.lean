/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# IsDeterministic

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `MeasureTheory.IsZeroOneMeasure`: a measure is a zero-one measure if it only takes the values `0`
  and `1`.
* `ProbabilityTheory.Kernel.IsDeterministic`: a kernel is deterministic if it commutes with
  the copy kernel, i.e. sampling and then copying the output is the same as running the kernel twice
  independently.

## Main statements

* `ProbabilityTheory.Kernel.is_deterministic_iff_zero_one`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.

* `ProbabilityTheory.Kernel.parallelComp_id_comp_copy_comp`: if the composition of two Markov
  kernels `η ∘ₖ κ` is deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by
  computing `η ∘ₖ κ` and `κ` independently.

## References

Section 10 & 11 in [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020].

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {α : Type*} [MeasurableSpace α]

namespace MeasureTheory

/-- A measure is a zero-one measure if it only takes the values `0` and `1`. -/
class IsZeroOneMeasure (μ : Measure α) : Prop where
  zero_one' : ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1

lemma Measure.zero_one (μ : Measure α) [IsZeroOneMeasure μ] :
    ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1 :=
  IsZeroOneMeasure.zero_one'

variable {μ : Measure α} [IsZeroOneMeasure μ]

instance : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    cases μ.zero_one MeasurableSet.univ with
    | inr h => simp [h]
    | inl h => simp [h]

lemma exists_one_iff_univ_one : (∃ s, MeasurableSet s ∧ μ s = 1) ↔ μ univ = 1 := by
  constructor
  · rintro ⟨s, hs, h⟩
    cases μ.zero_one MeasurableSet.univ with
    | inr h₁ => exact h₁
    | inl h₀ =>
      have := measure_mono (μ := μ) <| subset_univ s
      rw [h] at this
      simp_all
  · intro h
    exact ⟨univ, MeasurableSet.univ, h⟩

lemma univ_one {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 1) : μ univ = 1 :=
  (exists_one_iff_univ_one).mp ⟨s, hs, hμs⟩

lemma compl_eq_zero {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 1) : μ sᶜ = 0 := by
  rw [measure_compl hs (by simp), univ_one hs hμs, hμs, tsub_self]

lemma inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s = 1) (hμt : μ t = 1) : μ (s ∩ t) = 1 := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  cases μ.zero_one hs <;> cases μ.zero_one ht <;> cases μ.zero_one (hs.inter ht)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s ∩ t)ᶜ ≤ 0 by
    rw [measure_compl (hs.inter ht) (by simp), univ_one hs ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ ∪ tᶜ) := by simp [compl_inter]
  _ ≤ μ sᶜ + μ tᶜ := measure_union_le _ _
  _ ≤ 0 := by
    rw [compl_eq_zero hs ‹_›, compl_eq_zero ht ‹_›]
    simp

lemma inter_eq_prod {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∩ t) = μ s * μ t := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  cases μ.zero_one hs <;> cases μ.zero_one ht <;> cases μ.zero_one (hs.inter ht)
  all_goals try simp_all [inter_eq_one]

end MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace ProbabilityTheory.Kernel

lemma copy_comp_apply_prod (κ : Kernel α β) (a : α) {s t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : (copy β ∘ₖ κ) a (s ×ˢ t) = κ a (s ∩ t) := by
  rw [comp_apply' _ _ _ <| hs.prod ht]
  simp_rw [copy_apply, Measure.dirac_apply' _ <| hs.prod ht, indicator_prod_one]
  calc
  _ = ∫⁻ b, (s ∩ t).indicator 1 b ∂κ a := by
    congr with b
    simp [inter_indicator_one]
  _ = κ a (s ∩ t) := lintegral_indicator_one <| hs.inter ht

/-- A kernel is deterministic if it satisfies the naturality condition with respect to the copy
kernel. -/
class IsDeterministic (κ : Kernel α β) : Prop where
  comp_natural' : (κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ

lemma comp_natural (κ : Kernel α β) [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ := IsDeterministic.comp_natural'

lemma deterministic_is_deterministic {f : α → β} (hf : Measurable f) :
    IsDeterministic <| deterministic f hf := ⟨deterministic_comp_copy hf⟩

lemma is_deterministic_iff_zero_one (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ ∀ a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs ↦ ?_⟩
    have := DFunLike.congr_fun κ.comp_natural a |> DFunLike.congr_fun <| (s ×ˢ s)
    rw [parallelComp_comp_copy, prod_apply_prod, copy_comp_apply_prod, inter_self] at this
    · by_cases hκ : κ a s = 0
      · simp [hκ]
      · exact Or.inr <| (ENNReal.mul_eq_left hκ (by simp)).mp this
    all_goals exact hs
  · intro _
    refine ⟨?_⟩
    ext : 1
    rw [parallelComp_comp_copy, prod_apply]
    refine Measure.prod_eq fun s t hs ht ↦ ?_
    rw [copy_comp_apply_prod _ _ hs ht]
    exact inter_eq_prod hs ht

lemma zero_one (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] :
    ∀ a, IsZeroOneMeasure (κ a) := (is_deterministic_iff_zero_one κ).mp ‹_›

lemma parallelComp_id_comp_copy_comp {γ : Type*} [MeasurableSpace γ] {κ : Kernel α β}
    {η : Kernel β γ} [IsMarkovKernel κ] [IsMarkovKernel η] [IsDeterministic (η ∘ₖ κ)] :
    η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ := by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s t hs ht ↦ ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b ↦ η b s) b := by
    simp only [indicator]
    split_ifs
    all_goals simp_all
  simp_rw [this]
  rw [lintegral_indicator ht]
  have := ((η ∘ₖ κ).zero_one a)
  cases ((η ∘ₖ κ) a).zero_one hs with
  | inl h₀ =>
    rw [h₀, zero_mul, setLIntegral_eq_zero_iff ht <| η.measurable_coe hs]
    rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff <| η.measurable_coe hs] at h₀
    filter_upwards [h₀] with x hx _ using hx
  | inr h₁ =>
    rw [h₁, one_mul]
    have integral_le_kernel : ∫⁻ b in t, (η b) s ∂κ a ≤ κ a t := by
      calc
      _ ≤ ∫⁻ a in t, 1 ∂κ a := by
        refine lintegral_mono ?_
        intro b
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
      _ = κ a t := by rw [setLIntegral_one]
    refine le_antisymm integral_le_kernel <| tsub_eq_zero_iff_le.mp ?_
    rw [← nonpos_iff_eq_zero]
    calc
    _ = ∫⁻ b in t, 1 ∂κ a - ∫⁻ b in t, (η b) s ∂κ a := by
      rw [setLIntegral_one]
    _ = ∫⁻ b in t, 1 - (η b) s ∂κ a := by
      rw [lintegral_sub]
      · exact η.measurable_coe hs
      · exact ne_top_of_le_ne_top (by simp) integral_le_kernel
      · refine ae_of_all _ fun b ↦ ?_
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
    _ ≤ ∫⁻ b, 1 - (η b) s ∂κ a := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, (η x) sᶜ ∂κ a := by
        congr with x
        rw [measure_compl hs (by simp)]
        simp
    _ = (η ∘ₖ κ) a sᶜ := by
        rw [η.comp_apply' _ _ hs.compl]
    _ = 0 := compl_eq_zero hs h₁

end ProbabilityTheory.Kernel
