/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.InitialSeg

/-!
# Intervals as initial segments

We show that `Iic` and `Iio` are respectively initial and principal segments, and that any principal
segment `f` is order isomorphic to `Iio f.top`.
-/

@[expose] public section

namespace Set

variable {α : Type*} [Preorder α] {i j : α}

/-- `Iic j` is an initial segment. -/
@[simps]
def initialSegIic (j : α) : Iic j ≤i α where
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Iio j` is a principal segment. -/
@[simps]
def principalSegIio (j : α) : Iio j <i α where
  top := j
  toFun j := j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
lemma principalSegIio_apply (k : Iio j) : principalSegIio j k = k.1 :=
  rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIio_toRelEmbedding := principalSegIio_apply

/-- If `i ≤ j`, then `Iic i` is an initial segment of `Iic j`. -/
@[simps]
def initialSegIicIicOfLE (h : i ≤ j) : Iic i ≤i Iic j where
  toFun k := ⟨k, k.2.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := ⟨⟨k.1, (Subtype.coe_le_coe.2 h.le).trans x.2⟩, rfl⟩

/-- If `i ≤ j`, then `Iio i` is a principal segment of `Iic j`. -/
@[simps top]
def principalSegIioIicOfLE (h : i ≤ j) : Iio i <i Iic j where
  top := ⟨i, h⟩
  toFun k := ⟨k, k.2.le.trans h⟩
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simp]
lemma principalSegIioIicOfLE_apply (h : i ≤ j) (k : Iio i) :
    (principalSegIioIicOfLE h).toRelEmbedding k = ⟨k, k.2.le.trans h⟩ := rfl

@[deprecated (since := "2026-04-12")]
alias principalSegIioIicOfLE_toRelEmbedding := principalSegIioIicOfLE_apply

end Set

/-- If `f : α <i β` is a principal segment, this is the induced order
isomorphism `α ≃o Iio f.top`. -/
@[simps! apply_coe]
noncomputable def PrincipalSeg.orderIsoIio {α β : Type*} [PartialOrder α] [PartialOrder β]
    (f : α <i β) : α ≃o Set.Iio f.top :=
  .ofRelIsoLT f.subrelIso.symm
