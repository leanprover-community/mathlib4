/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.InitialSeg

/-!
# Intervals as initial segments

We show that `Set.Iic` and `Set.Iio` are respectively initial and
principal segments, and that any principal segment `f` is order
isomorphic to `Set.Iio f.top`.

-/

/-- `Set.Iic j` is an initial segment. -/
@[simps]
def Set.initialSegIic {α : Type*} [Preorder α] (j : α) :
    Set.Iic j ≤i α where
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Set.Iio j` is a principal segment. -/
@[simps]
def Set.principalSegIio {α : Type*} [Preorder α] (j : α) :
    Set.Iio j <i α where
  top := j
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

/-- If `f : α <i β` is a principal segment, this is the induced order
isomorphism `α ≃o Set.Iio f.top`. -/
@[simps! apply_coe]
noncomputable def PrincipalSeg.orderIsoIio {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α <i β) :
    α ≃o Set.Iio f.top where
  toEquiv := Equiv.ofBijective (f := fun a ↦ ⟨f a, f.lt_top a⟩) (by
    constructor
    · intro x y hxy
      exact f.injective (by simpa using hxy)
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := f.mem_range_of_rel_top hz
      exact ⟨x, by simpa using hx⟩)
  map_rel_iff' := by simp
