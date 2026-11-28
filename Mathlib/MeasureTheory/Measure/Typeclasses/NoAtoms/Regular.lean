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
positive measure for every neighborhood `U` of `x`. Now `s \ {x}` contains a compact `L` of
positive measure. Separate `L` and `x` by disjoint open sets `U ⊇ L` and `V ∋ x`. Then `s ∩ U` has
positive, hence full measure, so `s ∩ V` is a null set, a contradiction. -/
theorem of_innerRegularCompactLTTop [OpensMeasurableSpace α] [NullSingletonClass μ]
    [μ.InnerRegularCompactLTTop] [SigmaFinite μ] : NoAtoms μ := by
  refine ⟨fun s hs ↦ ?_⟩
  -- a point all of whose neighborhoods meet `s` in positive measure
  obtain ⟨x, -, hx⟩ := hs.measurableSet.exists_forall_nhds_measure_pos hs.measure_ne_top hs.pos
  -- a compact subset of `s \ {x}` of positive measure
  have hsx : μ (s \ {x}) = μ s := measure_sdiff_null (measure_singleton x)
  obtain ⟨L, hLs, hL, hL_pos⟩ := (hs.measurableSet.diff (measurableSet_singleton x))
    |>.exists_lt_isCompact_of_ne_top (hsx ▸ hs.measure_ne_top) (hsx ▸ hs.pos)
  obtain ⟨U, V, hU, hV, hLU, hxV, hUV⟩ := hL.separation_of_notMem fun h ↦ (hLs h).2 rfl
  -- `s ∩ U` has positive, hence full measure, so `s ∩ V ⊆ s \ (s ∩ U)` is a null set
  have hsU : μ (s ∩ U) = μ s := (hs.measure_eq_zero_or_eq inter_subset_left).resolve_left
    (hL_pos.trans_le (measure_mono (subset_inter (hLs.trans sdiff_subset) hLU))).ne'
  have h := measure_sdiff inter_subset_left
    (hs.measurableSet.inter hU.measurableSet).nullMeasurableSet (hsU ▸ hs.measure_ne_top)
  rw [hsU, tsub_self] at h
  refine (hx V (hV.mem_nhds hxV)).ne' (measure_mono_null ?_ h)
  exact fun y hy ↦ ⟨hy.1, fun hyU ↦ disjoint_left.1 hUV hyU.2 hy.2⟩

end NoAtoms

end MeasureTheory
