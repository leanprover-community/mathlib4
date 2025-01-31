/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Caratheodorys extension theorem

## Main declarations

`Measure.ofAddContent`: Construct a measure from a sigma-subadditive content on a semiring,
assuming the semiring
generates a given measurable structure. The measure is defined on this measurable structure.

## Main results
* `inducedOuterMeasure_addContent_of_subadditive`:
A semiadditive content on a semiring induces an outer measure.
* `isCaratheodory_inducedOuterMeasure`: The Caratheodory measurable sets are at least members of
  the SetSemiring

-/

open Set

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

namespace OuterMeasure

section OfFunction

theorem ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) {s : Set α} (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem _ _ m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  calc m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_sigma_subadd (fun i ↦ hC.inter_mem _ hs _ (hf i)) ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) := by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      exact addContent_mono hC (hC.inter_mem _ hs _ (hf i)) (hf i) Set.inter_subset_right

end OfFunction

end OuterMeasure

theorem inducedOuterMeasure_addContent_of_subadditive (hC : IsSetSemiring C) (m : AddContent C)
    (m_sigma_subadd : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : (⋃ i, f i) ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    {s : Set α} (hs : s ∈ C) :
    inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m s := by
  suffices inducedOuterMeasure (fun x _ ↦ m x) hC.empty_mem addContent_empty s = m.extend hC s by
    rwa [m.extend_eq hC hs] at this
  refine Eq.trans ?_ (OuterMeasure.ofFunction_addContent_eq hC (m.extend hC) ?_ ?_ hs)
  · congr
  · intro f hf hf_mem
    rw [m.extend_eq hC hf_mem]
    refine (m_sigma_subadd hf hf_mem).trans_eq ?_
    congr with i
    rw [m.extend_eq hC (hf i)]
  · exact fun _ ↦ m.extend_eq_top _

end MeasureTheory
