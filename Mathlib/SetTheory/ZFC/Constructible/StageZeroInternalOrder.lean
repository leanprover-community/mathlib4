/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageInternalOrder

/-!
# The internally represented order on the zero constructible stage

The carrier of `L_0` is empty, so the empty constructible set represents its
unique strict well-order.
-/

@[expose] public section

universe u

namespace Constructible.Model

/-- The empty graph internally well-orders the zero stage. -/
theorem stageZeroInternallyWellOrdered :
    StageInternallyWellOrdered (0 : Ordinal.{u}) := by
  refine ⟨emptyLCarrier, ?_⟩
  refine
    { wf := WellFounded.intro (fun x => ?_)
      trichotomous := fun x => ?_ }
  · have hx : x.1 ∈ (∅ : ZFSet.{u}) := by
      simpa only [LStageZF_zero] using x.2
    exact (ZFSet.notMem_empty x.1 hx).elim
  · have hx : x.1 ∈ (∅ : ZFSet.{u}) := by
      simpa only [LStageZF_zero] using x.2
    exact (ZFSet.notMem_empty x.1 hx).elim

end Constructible.Model
