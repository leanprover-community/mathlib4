/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Sign
import Mathlib.Topology.Order.Basic

#align_import topology.instances.sign from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Topology on `SignType`

This file gives `SignType` the discrete topology, and proves continuity results for `SignType.sign`
in an `OrderTopology`.

-/


instance : TopologicalSpace SignType :=
  ⊥

instance : DiscreteTopology SignType :=
  ⟨rfl⟩

variable {α : Type*} [Zero α] [TopologicalSpace α]

section PartialOrder

variable [PartialOrder α] [DecidableRel ((· < ·) : α → α → Prop)] [OrderTopology α]

theorem continuousAt_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt SignType.sign a := by
  refine' (continuousAt_const : ContinuousAt (fun _ => (1 : SignType)) a).congr _
  -- ⊢ (fun x => 1) =ᶠ[nhds a] ↑SignType.sign
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  -- ⊢ ∃ t, (∀ (x : α), x ∈ t → 1 = ↑SignType.sign x) ∧ IsOpen t ∧ a ∈ t
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩
  -- 🎉 no goals
#align continuous_at_sign_of_pos continuousAt_sign_of_pos

theorem continuousAt_sign_of_neg {a : α} (h : a < 0) : ContinuousAt SignType.sign a := by
  refine' (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr _
  -- ⊢ (fun x => -1) =ᶠ[nhds a] ↑SignType.sign
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  -- ⊢ ∃ t, (∀ (x : α), x ∈ t → -1 = ↑SignType.sign x) ∧ IsOpen t ∧ a ∈ t
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩
  -- 🎉 no goals
#align continuous_at_sign_of_neg continuousAt_sign_of_neg

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

theorem continuousAt_sign_of_ne_zero {a : α} (h : a ≠ 0) : ContinuousAt SignType.sign a := by
  rcases h.lt_or_lt with (h_neg | h_pos)
  -- ⊢ ContinuousAt (↑SignType.sign) a
  · exact continuousAt_sign_of_neg h_neg
    -- 🎉 no goals
  · exact continuousAt_sign_of_pos h_pos
    -- 🎉 no goals
#align continuous_at_sign_of_ne_zero continuousAt_sign_of_ne_zero

end LinearOrder
