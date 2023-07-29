/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Order.Directed

/-!
# Order instances on ULift

We define order instances on `ULift α`, i.e., the lift of `α` to a higher universe, given
corresponding instances on `α`.
-/

instance Ulift.LE [LE α] : LE (ULift α) :=
  ⟨fun x y => x.down ≤ y.down ⟩

instance Ulift.LT [LT α] : LT (ULift α) :=
  ⟨fun x y => x.down < y.down ⟩

instance ULift.Preorder [Preorder α] : Preorder (ULift α) :=
  { le_refl := fun _a ↦ Eq.le rfl
    le_trans := fun _a _b _c ↦ le_trans
    lt_iff_le_not_le := fun _a _b ↦ lt_iff_le_not_le }

instance ULift.PartialOrder [PartialOrder α] : PartialOrder (ULift α) :=
  { le_antisymm := fun _x _y h h' ↦ down_inj.1 (le_antisymm h h') }

instance ULift.Min [Min α] : Min (ULift α) :=
  ⟨fun x y ↦ ULift.up (min x.down y.down)⟩

instance ULift.Max [Max α] : Max (ULift α) :=
  ⟨fun x y ↦ ULift.up (max x.down y.down)⟩

instance ULift.Ord [Ord α] : Ord (ULift α) :=
  ⟨fun x y ↦ compare x.down y.down⟩

instance ULift.LinearOrder [LinearOrder α] : LinearOrder (ULift α) :=
  { le_total := fun x y ↦ by
      rcases le_total x.down y.down with h|h
      exacts [Or.inl h, Or.inr h]
    decidableLE := fun x y ↦ by
      change Decidable (x.down ≤ y.down); infer_instance
    decidableEq := fun x y ↦ by rw [← down_inj]; infer_instance
    decidableLT := fun x y ↦ by
      change Decidable (x.down < y.down); infer_instance
    min_def := fun x y ↦ by
      by_cases h : x ≤ y
      · have h' : x.down ≤ y.down := h
        simp [h, min, h']
      · have h' : y.down ≤ x.down := le_of_not_ge h
        simp [h, min, h']
    max_def := fun x y ↦ by
      by_cases h : x ≤ y
      · have h' : x.down ≤ y.down := h
        simp [h, max, h']
      · have h' : y.down ≤ x.down := le_of_not_ge h
        simp [h, max, h']
    compare_eq_compareOfLessAndEq := by
      intro x y
      change compare x.down y.down = _
      rw [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
      congr 2
      simp [down_inj] }

instance [LE α] [h : IsDirected α (· ≤ ·)] : IsDirected (ULift α) (· ≤ ·) := by
  constructor
  intro a b
  rcases h.directed a.down b.down with ⟨c, hc⟩
  exact ⟨ULift.up c, hc⟩
