/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.ZFC.Basic

/-!
# Cardinalities of ZFC sets

In this file, we define the cardinalities of ZFC sets as `ZFSet.{u} → Cardinal.{u}`.

## Definitions

* `ZFSet.card`: Cardinality of a ZFC set.
-/

universe u v

open Cardinal

namespace ZFSet

/-- The cardinality of a ZFC set. -/
def card (x : ZFSet.{u}) : Cardinal.{u} := #(Shrink x.toSet)

/-- `ZFSet.card x` is equal to the cardinality of `x` as a set of `ZFSet`s. -/
theorem card_eq {x : ZFSet.{u}} : lift.{u + 1, u} (card x) = #x.toSet := by
  rw [card, lift_mk_shrink'']

variable {x y : ZFSet.{u}}

@[gcongr]
theorem card_mono (h : x ⊆ y) : card x ≤ card y := by
  rw [← lift_le, card_eq, card_eq]
  apply mk_le_mk_of_subset
  simpa

@[simp]
theorem card_empty : card ∅ = 0 := by
  rw [← lift_inj, card_eq]
  simp

theorem card_insert_le : card (insert x y) ≤ card y + 1 := by
  rw [← lift_le.{u + 1}]
  simpa [card_eq] using mk_insert_le

theorem card_insert (h : x ∉ y) : card (insert x y) = card y + 1 := by
  rw [← lift_inj.{u, u + 1}]
  simpa [card_eq] using mk_insert ((mem_toSet x y).not.2 h)

@[simp]
theorem card_singleton : card {x} = 1 := by
  convert card_insert (notMem_empty x) using 1
  rw [card_empty, zero_add]

theorem card_pair_of_ne (h : x ≠ y) : card {x, y} = 2 := by
  convert card_insert (notMem_singleton.2 h)
  rw [card_singleton, one_add_one_eq_two]

theorem card_union_le : card (x ∪ y) ≤ card x + card y := by
  rw [← lift_le.{u + 1}]
  simpa [card_eq] using mk_union_le x.toSet y.toSet

@[simp]
theorem card_powerset (x : ZFSet) : card (powerset x) = 2 ^ card x := by
  rw [← lift_inj, card_eq, lift_power, lift_two, card_eq, ← mk_powerset, Cardinal.eq]
  refine ⟨⟨fun ⟨y, h⟩ => ⟨y.toSet, Set.mem_powerset (toSet_subset_iff.2 (mem_powerset.1 h))⟩,
    fun ⟨s, h⟩ => ⟨x.sep (· ∈ s), mem_powerset.2 (sep_subset _ _)⟩,
    fun ⟨y, h⟩ => ?_, fun ⟨s, h⟩ => ?_⟩⟩
  · simp only [mem_toSet, mem_powerset] at h
    ext z
    simpa using @h z
  · simp only [Set.mem_powerset_iff] at h
    ext y
    simpa using @h y

theorem card_image_le {f : ZFSet → ZFSet} [Definable₁ f] :
    card (image f x) ≤ card x := by
  rw [← lift_le, card_eq, card_eq, toSet_image]
  exact mk_image_le

theorem lift_card_range_le {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift.{u} (card (range f)) ≤ lift.{v} #α := by
  rw [← lift_le.{max u (v + 1)}, lift_lift, ← lift_lift.{v + 1}, card_eq, toSet_range, lift_lift,
    lift_umax.{u, v + 1}]
  exact mk_range_le_lift

theorem iSup_card_le_card_iUnion {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    ⨆ i, card (f i) ≤ card (⋃ i, f i) := by
  rw [← lift_le.{v + 1}, card_eq, toSet_iUnion, lift_iSup (bddAbove_of_small _)]
  simp_rw [card_eq]
  exact iSup_mk_le_mk_iUnion

theorem lift_card_iUnion_le_sum_card {α} [Small.{v, u} α] {f : α → ZFSet.{v}} :
    lift (card (⋃ i, f i)) ≤ sum fun i => card (f i) := by
  rw [← lift_le.{max u (v + 1)}, lift_lift, ← lift_lift.{v + 1}, card_eq, toSet_iUnion,
    lift_umax.{max u v, v + 1}, lift_sum.{u, v, v + 1}]
  simp_rw [card_eq]
  exact mk_iUnion_le_sum_mk_lift

end ZFSet
