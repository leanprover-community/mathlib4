/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Cardinalities of ZFC sets

In this file, we define the cardinalities of ZFC sets as `ZFSet.{u} → Cardinal.{u}`.

## Definitions

* `ZFSet.card`: Cardinality of a ZFC set.
-/

@[expose] public section

universe u v

open Cardinal

namespace ZFSet

/-- The cardinality of a ZFC set. -/
def card (x : ZFSet.{u}) : Cardinal.{u} := #(Shrink x)

variable {x y : ZFSet.{u}}

/-- `ZFSet.card x` is equal to the cardinality of `x` as a set of `ZFSet`s. -/
theorem cardinalMk_coe_sort : #x = lift.{u + 1, u} (card x) := by
  rw [card, lift_mk_shrink'']

@[gcongr]
theorem card_mono (h : x ⊆ y) : card x ≤ card y := by
  simpa [cardinalMk_coe_sort] using mk_le_mk_of_subset (coe_subset_coe.2 h)

@[simp]
theorem card_empty : card ∅ = 0 := by
  rw [← lift_inj, ← cardinalMk_coe_sort]
  simp

theorem card_insert_le : card (insert x y) ≤ card y + 1 := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_insert_le

theorem card_insert (h : x ∉ y) : card (insert x y) = card y + 1 := by
  rw [← lift_inj.{u, u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_insert (SetLike.mem_coe.not.2 h)

@[simp]
theorem card_singleton : card {x} = 1 := by
  simpa [notMem_singleton] using card_insert (notMem_empty x)

theorem card_pair_of_ne (h : x ≠ y) : card {x, y} = 2 := by
  convert card_insert (notMem_singleton.2 h)
  rw [card_singleton, one_add_one_eq_two]

theorem card_union_le : card (x ∪ y) ≤ card x + card y := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_union_le (x : Set ZFSet) y

@[simp]
theorem card_powerset (x : ZFSet.{u}) : card (powerset x) = 2 ^ card x := by
  rw [← lift_inj.{u, u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_congr (powersetEquiv x)

theorem card_image_le {f : ZFSet → ZFSet} [Definable₁ f] :
    card (image f x) ≤ card x := by
  simpa [cardinalMk_coe_sort, ← coe_image, -mem_image] using mk_image_le (f := f) (s := x)

theorem lift_card_range_le {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift.{u} (card (range f)) ≤ lift.{v} #α := by
  rw [← lift_le.{max u (v + 1)}, lift_lift.{v}, lift_umax.{u, v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_range, -mem_range] using mk_range_le_lift (f := f)

theorem iSup_card_le_card_iUnion {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    ⨆ i, card (f i) ≤ card (⋃ i, f i) := by
  simpa [cardinalMk_coe_sort, ← coe_iUnion, ← lift_iSup (bddAbove_of_small _), -mem_iUnion] using
    iSup_mk_le_mk_iUnion (f := SetLike.coe ∘ f)

theorem lift_card_iUnion_le_sum_card {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift (card (⋃ i, f i)) ≤ sum fun i => card (f i) := by
  rw [← lift_le.{max u (v + 1)}, lift_umax.{max u v, v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_iUnion, -mem_iUnion] using
    mk_iUnion_le_sum_mk_lift (f := SetLike.coe ∘ f)

end ZFSet
