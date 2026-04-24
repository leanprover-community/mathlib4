/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Class `IsDeterministic` of deterministic kernels

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `Kernel.IsDeterministic`: a kernel is deterministic if copying then applying the kernel to the
  two copies is the same as first applying the kernel then copying.
* `IsZeroOneMeasure`: a measure is a zero-one measure if it only takes the values `0`
  or `1`.

## Main statements

* `eq_zero_or_dirac`: in a standard Borel space, a zero-one measure is either the zero measure or a
  Dirac measure.
* `is_deterministic_iff_zero_one`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.
* `isDeterministic_eq_deterministic`: in a standard Borel space, a deterministic Markov kernel is
  a Dirac kernel of some measurable function.
* `parallelComp_id_comp_copy_comp`: if the composition of two Markov kernels `η ∘ₖ κ` is
  deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
  and `κ` independently. This corresponds to the equation of a Positive Markov category.
  See Example 11.25 of [fritz2020].

## Implementation notes

`parallelComp_id_comp_copy_comp` is true only when considering Markov kernels. To see why, consider
the counterexample with $X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_
{\varnothing}$ and $\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their
composition is deterministic, the equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
* [Moss and Perrone, *A category-theoretic proof of the ergodic decomposition theorem*][moss2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace ProbabilityTheory.Kernel

/-- A kernel is deterministic if copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
class IsDeterministic (κ : Kernel α β) : Prop where
  deterministic_comp_copy' : (κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ

lemma deterministic_comp_copy (κ : Kernel α β) [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ copy α = copy β ∘ₖ κ := IsDeterministic.deterministic_comp_copy'

instance {f : α → β} (hf : Measurable f) : IsDeterministic (deterministic f hf) where
  deterministic_comp_copy' := by
    simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
    deterministic_comp_deterministic, Function.comp_def]

instance : IsDeterministic (Kernel.id (α := α)) := by
  unfold Kernel.id
  infer_instance

instance : IsDeterministic (copy α) := by
  unfold copy
  infer_instance

instance : IsDeterministic (discard α) := by
  unfold discard
  infer_instance

instance : IsDeterministic (swap α β) := by
  unfold swap
  infer_instance

end ProbabilityTheory.Kernel

namespace MeasureTheory

/-- A measure is a zero-one measure if it only takes the values `0` or `1`. -/
class IsZeroOneMeasure (μ : Measure α) : Prop where
  zero_one₀ : ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1

lemma Measure.zero_one₀ (μ : Measure α) [IsZeroOneMeasure μ] :
    ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1 := IsZeroOneMeasure.zero_one₀

lemma Measure.zero_one (μ : Measure α) [IsZeroOneMeasure μ] :
    ∀ s, μ s = 0 ∨ μ s = 1 := by
  intro s
  by_cases hs : MeasurableSet s
  · exact μ.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact μ.zero_one₀ mt

variable {μ : Measure α} [IsZeroOneMeasure μ]

instance : IsZeroOrProbabilityMeasure μ where
  measure_univ := μ.zero_one univ

lemma exists_one_iff_univ_one : (∃ s, μ s = 1) ↔ μ univ = 1 := by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
    · have := measure_mono (μ := μ) <| subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩

lemma univ_one {s : Set α} (hμs : μ s = 1) : μ univ = 1 := (exists_one_iff_univ_one).mp ⟨s, hμs⟩

lemma compl_eq_zero {s : Set α} (hs : MeasurableSet s) (hμs : μ s = 1) : μ sᶜ = 0 := by
  rw [measure_compl hs (by simp), univ_one hμs, hμs, tsub_self]

lemma inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s = 1) (hμt : μ t = 1) : μ (s ∩ t) = 1 := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s ∩ t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s ∩ t)ᶜ ≤ 0 by
    rw [measure_compl (hs.inter ht) (by simp), univ_one ‹_›] at this
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
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s ∩ t)
  all_goals try simp_all [inter_eq_one]

/-- In a standard Borel space, a zero-one measure is either the zero measure or a Dirac measure. -/
theorem eq_zero_or_dirac [StandardBorelSpace α] : μ = 0 ∨ ∃ x₀, μ = Measure.dirac x₀ := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · right
    have : IsProbabilityMeasure μ := by
      rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
      · rw [← ne_eq, ← μ.measure_univ_ne_zero] at hμ
        contradiction
      · exact ⟨h⟩
    obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
    let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
    have mBn : MeasurableSet (⋂ n, B n) := by
      refine MeasurableSet.iInter fun n ↦ ?_
      simp only [dite_eq_ite, B]
      split_ifs
      · exact hAm n
      · exact (hAm n).compl
    have hBn : μ (⋂ n, B n) = 1 := by
      refine (prob_compl_eq_zero_iff mBn).mp ?_
      simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
      intro n
      split_ifs with h
      · simp_all
      · rw [compl_compl]
        rcases μ.zero_one (A n) with (h₀ | h₁)
        · exact h₀
        · simp_all
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, ⋂ n, B n = {x₀} := by
      have neBn : (⋂ n, B n).Nonempty := by
        by_contra! h
        rw [h] at hBn
        simp_all
      simp_rw [eq_singleton_iff_unique_mem]
      refine ⟨neBn.some, neBn.some_mem, fun y hy ↦ ?_⟩
      refine hAsep y (by trivial) neBn.some (by trivial) fun n ↦ ?_
      have hsome := neBn.some_mem
      simp only [dite_eq_ite, mem_iInter, B] at hsome hy
      specialize hsome n
      specialize hy n
      constructor
      · intro h
        split_ifs at hy with hμAn
        · simpa [hμAn] using hsome
        · contradiction
      · intro h
        split_ifs at hsome with hμAn
        · simpa [hμAn] using hy
        · contradiction
    use x₀
    ext s hs
    by_cases h : x₀ ∈ s
    · simp [h]
      have : {x₀} ⊆ s := by grind
      have := measure_mono (μ := μ) this
      rw [← hx₀, hBn] at this
      simp_all
    · simp [h]
      have : s ⊆ {x₀}ᶜ := by grind
      have := measure_mono (μ := μ) this
      rw [← hx₀, measure_compl mBn (by simp), measure_univ, hBn] at this
      simp_all

end MeasureTheory

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

lemma is_deterministic_iff_zero_one (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ ∀ a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs ↦ ?_⟩
    have := DFunLike.congr_fun κ.deterministic_comp_copy a |> DFunLike.congr_fun
      <| (s ×ˢ s)
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

instance (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] : ∀ a, IsZeroOneMeasure (κ a) :=
  (is_deterministic_iff_zero_one κ).mp ‹_›

/-- in a standard Borel space, a deterministic Markov kernel is a Dirac kernel of ome measurable
function. -/
theorem isDeterministic_eq_deterministic [StandardBorelSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] [IsDeterministic κ] :
    ∃ (f : α → β) (hf : Measurable f), κ = deterministic f hf := by
  have : ∀ a, ∃ x₀, κ a = Measure.dirac x₀ := by
    intro a
    rcases eq_zero_or_dirac (μ := κ a) with (h | h)
    · have : κ a univ = 0 := by simp [h]
      have : κ a univ = 1 := by simp
      simp_all
    · exact h
  choose f hf using this
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).symm
    rw [this]
    exact κ.measurable_coe hs <| measurableSet_singleton 1
  · ext a : 1
    exact hf a

/-- The equation of a Positive Markov category: if the composition of two Markov kernels `η ∘ₖ κ` is
 deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
and `κ` independently. -/
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
  rcases ((η ∘ₖ κ) a).zero_one s with (h₀ | h₁)
  · rw [h₀, zero_mul, setLIntegral_eq_zero_iff ht <| η.measurable_coe hs]
    rw [comp_apply' _ _ _ hs, lintegral_eq_zero_iff <| η.measurable_coe hs] at h₀
    filter_upwards [h₀] with x hx _ using hx
  · /- In Example 11.25 of [gritz2020], the case where `((η ∘ₖ κ) a) s = 1` is not explicitly
    treated. We prove it here by using the fact that the hypothesis implies that
    `((η ∘ₖ κ) a) sᶜ = 0`, and thus that the integral of `1 - (η b) s` over `κ a` is zero. -/
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
