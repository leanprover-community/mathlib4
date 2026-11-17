/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Inner regular measures without atoms

A σ-finite measure on a Hausdorff space which is inner regular with respect to compact sets and
vanishes on singletons has no atoms.

## Main statements

* `MeasureTheory.NoAtoms.of_innerRegularCompactLTTop`: a σ-finite measure on a Hausdorff space
  which is inner regular with respect to compact sets and vanishes on singletons has no atoms.

## Implementation notes

`NoAtoms.of_innerRegularCompactLTTop` is not an instance: together with the instances deriving
`NullSingletonClass μ` from `NoAtoms μ`, instance search would loop.
-/

public section

namespace MeasureTheory

open Set Measure ENNReal

variable {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] {μ : Measure α}

namespace NoAtoms

/-- A σ-finite measure on a Hausdorff space which is inner regular with respect to compact sets
and vanishes on singletons has no atoms.
See https://math.stackexchange.com/questions/3881683/does-mu-x-0-imply-non-atomic-for-radon-measure

Proof sketch: an atom `s` has finite measure by `Measure.IsAtom.measure_ne_top`, and thus by
`MeasurableSet.exists_forall_nhds_measure_pos` contains some `x ∈ s` such that `s ∩ U` has
positive (hence full) measure for every neighborhood `U` of `x`. Now `s \ {x}` contains a compact
`L` of positive measure, and separating `x` from `L` by disjoint open sets yields two disjoint
subsets of `s` of full measure, a contradiction. -/
theorem of_innerRegularCompactLTTop [OpensMeasurableSpace α] [NullSingletonClass μ]
    [μ.InnerRegularCompactLTTop] [SigmaFinite μ] : NoAtoms μ := by
  refine ⟨fun s hs ↦ ?_⟩
  -- every subset of `s` of positive measure has full measure
  have full {t} (hts : t ⊆ s) (ht : μ t ≠ 0) : μ t = μ s :=
    (hs.measure_eq_zero_or_eq hts).resolve_left ht
  have hfin : μ s ≠ ∞ := hs.measure_ne_top
  -- a point all of whose neighborhoods meet `s` in positive measure
  obtain ⟨x, -, hx⟩ := hs.measurableSet.exists_forall_nhds_measure_pos hfin hs.pos
  -- a compact subset of `s \ {x}` of positive measure
  have hsx : μ (s \ {x}) = μ s := measure_sdiff_null (measure_singleton x)
  obtain ⟨L, hLs, hL, hL_pos⟩ := (hs.measurableSet.diff (measurableSet_singleton x))
    |>.exists_lt_isCompact_of_ne_top (hsx ▸ hfin) (hsx ▸ hs.pos)
  obtain ⟨U, V, hU, hV, hLU, hxV, hUV⟩ := hL.separation_of_notMem fun h ↦ (hLs h).2 rfl
  have hsU : μ (s ∩ U) = μ s := full inter_subset_left
    (hL_pos.trans_le (measure_mono (subset_inter (hLs.trans sdiff_subset) hLU))).ne'
  have hsV : μ (s ∩ V) = μ s := full inter_subset_left (hx V (hV.mem_nhds hxV)).ne'
  have : μ s + μ s ≤ μ s + 0 := calc
    _ = μ (s ∩ U) + μ (s ∩ V) := by rw [hsU, hsV]
    _ = μ ((s ∩ U) ∪ (s ∩ V)) := by
      symm
      apply measure_union
      · exact hUV.mono inter_subset_right inter_subset_right
      · exact hs.measurableSet.inter hV.measurableSet
    _ ≤ μ s := measure_mono (union_subset inter_subset_left inter_subset_left)
    _ = μ s + 0 := (add_zero _).symm
  exact hs.measure_ne_zero (nonpos_iff_eq_zero.mp (ENNReal.le_of_add_le_add_left hfin this))

end NoAtoms

end MeasureTheory
