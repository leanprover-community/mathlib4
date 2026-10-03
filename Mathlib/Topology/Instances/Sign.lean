/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Topology.Order.Basic

/-!
# Topology on `SignType`

This file gives `SignType` the discrete topology, and proves continuity results for `SignType.sign`
in an `OrderTopology`.
-/

public section

instance : TopologicalSpace SignType :=
  ⊥

instance : DiscreteTopology SignType :=
  ⟨rfl⟩

variable {α : Type*} [Zero α] [TopologicalSpace α]

section PartialOrder

variable [PartialOrder α] [DecidableLT α] [OrderTopology α]

theorem continuousAt_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt SignType.sign a := by
  refine (continuousAt_const : ContinuousAt (fun _ => (1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩

theorem continuousAt_sign_of_neg {a : α} (h : a < 0) : ContinuousAt SignType.sign a := by
  refine (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr ?_
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

theorem continuousAt_sign_of_ne_zero {a : α} (h : a ≠ 0) : ContinuousAt SignType.sign a := by
  rcases h.lt_or_gt with (h_neg | h_pos)
  · exact continuousAt_sign_of_neg h_neg
  · exact continuousAt_sign_of_pos h_pos

/-- The sign of a continuous function is continuous wherever the function is nonzero. -/
theorem ContinuousOn.sign {β : Type*} [TopologicalSpace β] {f : β → α} {s : Set β}
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => SignType.sign (f x)) s := by
  refine (continuousOn_of_forall_continuousAt fun y hy => ?_).comp' hf (Set.mapsTo_image _ _)
  obtain ⟨x, hx, rfl⟩ := hy
  exact continuousAt_sign_of_ne_zero (h0 x hx)

end LinearOrder
