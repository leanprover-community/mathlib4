/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.ParallelComp
import Batteries.Tactic.Congr
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Class `IsDeterministic` of deterministic kernels

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `Kernel.IsDeterministic`: a kernel is deterministic if copying then applying the kernel to the
  two copies is the same as first applying the kernel then copying.

## Main statements

* `isDeterministic_iff_isZeroOneMeasure`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.
* `IsDeterministic.exists_eq_deterministic`: in a standard Borel space, a deterministic Markov
  kernel is a Dirac kernel of some measurable function.
* `comp_parallelComp_comp_copy`: if the composition of two Markov kernels `η ∘ₖ κ` is
  deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
  and `κ` independently. This corresponds to the equation of a Positive Markov category.
  See Example 11.25 of [fritz2020].

## Implementation notes

`comp_parallelComp_comp_copy` is true only when considering Markov kernels. To see why, consider
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

namespace ProbabilityTheory

/-- A kernel is deterministic if copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
class IsDeterministic (κ : Kernel α β) : Prop where
  parallelComp_self_comp_copy' : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ

namespace Kernel

lemma parallelComp_self_comp_copy {κ : Kernel α β} [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ :=
  IsDeterministic.parallelComp_self_comp_copy'

instance {f : α → β} (hf : Measurable f) : IsDeterministic (deterministic f hf) where
  parallelComp_self_comp_copy' := by
    simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
      deterministic_comp_deterministic, Function.comp_def]

instance : IsDeterministic (mβ := mα) (Kernel.id (α := α)) := by unfold Kernel.id; infer_instance

instance : IsDeterministic (copy α) := by unfold copy; infer_instance

instance : IsDeterministic (discard α) := by unfold discard; infer_instance

instance : IsDeterministic (swap α β) := by unfold swap; infer_instance

open IsZeroOneMeasure

lemma isDeterministic_iff_isZeroOneMeasure (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ ∀ a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs ↦ ?_⟩
    have := DFunLike.congr_fun κ.parallelComp_self_comp_copy a |> DFunLike.congr_fun
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
    exact measure_inter_eq_prod hs ht

instance (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] : ∀ a, IsZeroOneMeasure (κ a) :=
  (isDeterministic_iff_isZeroOneMeasure κ).mp ‹_›

/-- in a standard Borel space, a deterministic Markov kernel is a Dirac kernel of one measurable
function. -/
theorem IsDeterministic.exists_eq_deterministic [StandardBorelSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] [IsDeterministic κ] :
    ∃ (f : α → β) (hf : Measurable f), κ = deterministic f hf := by
  choose f hf using fun a ↦ exists_eq_dirac (μ := κ a)
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
lemma comp_parallelComp_comp_copy {γ : Type*} [MeasurableSpace γ] {κ : Kernel α β}
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
    _ = 0 := by
      rw [measure_compl hs (by simp), measure_univ h₁, h₁, tsub_self]

end ProbabilityTheory.Kernel
