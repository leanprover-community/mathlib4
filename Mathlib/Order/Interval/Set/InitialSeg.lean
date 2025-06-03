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

namespace Set

variable {α : Type*} [Preorder α]

/-- `Set.Iic j` is an initial segment. -/
@[simps]
def initialSegIic (j : α) :
    Set.Iic j ≤i α where
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Set.Iio j` is a principal segment. -/
@[simps]
def principalSegIio (j : α) :
    Set.Iio j <i α where
  top := j
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
lemma principalSegIio_toRelEmbedding {j : α} (k : Iio j) :
    (Set.principalSegIio j).toRelEmbedding k = k.1 := rfl

/-- If `i ≤ j`, then `Set.Iic i` is an initial segment of `Set.Iic j`. -/
@[simps]
def initialSegIicIicOfLE {i j : α} (h : i ≤ j) :
    Set.Iic i ≤i Set.Iic j where
  toFun := fun ⟨k, hk⟩ ↦ ⟨k, hk.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := ⟨⟨k.1, (Subtype.coe_le_coe.2 h.le).trans x.2⟩, rfl⟩

/-- If `i ≤ j`, then `Set.Iio i` is a principal segment of `Set.Iic j`. -/
@[simps top]
def principalSegIioIicOfLE {i j : α} (h : i ≤ j) :
    Set.Iio i <i Set.Iic j where
  top := ⟨i, h⟩
  toFun := fun ⟨k, hk⟩ ↦ ⟨k, hk.le.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
lemma principalSegIioIicOfLE_toRelEmbedding {i j : α} (h : i ≤ j)
    (k : Iio i) :
    (Set.principalSegIioIicOfLE h).toRelEmbedding k = ⟨k, k.2.le.trans h⟩ := rfl

end Set

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
