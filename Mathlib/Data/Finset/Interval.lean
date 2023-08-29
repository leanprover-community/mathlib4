/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.LocallyFinite

#align_import data.finset.interval from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Intervals of finsets as finsets

This file provides the `LocallyFiniteOrder` instance for `Finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : Finset α`, then `Finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`Finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`Finset.Icc {0, 1, 2} {0, 1, 3} = {}`.
-/


variable {α : Type*}

namespace Finset

variable [DecidableEq α] (s t : Finset α)

instance : LocallyFiniteOrder (Finset α)
    where
  finsetIcc s t := t.powerset.filter ((· ⊆ ·) s)
  finsetIco s t := t.ssubsets.filter ((· ⊆ ·) s)
  finsetIoc s t := t.powerset.filter ((· ⊂ ·) s)
  finsetIoo s t := t.ssubsets.filter ((· ⊂ ·) s)
  finset_mem_Icc s t u := by
    rw [mem_filter, mem_powerset]
    exact and_comm
  finset_mem_Ico s t u := by
    rw [mem_filter, mem_ssubsets]
    exact and_comm
  finset_mem_Ioc s t u := by
    rw [mem_filter, mem_powerset]
    exact and_comm
  finset_mem_Ioo s t u := by
    rw [mem_filter, mem_ssubsets]
    exact and_comm

theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filter ((· ⊆ ·) s) :=
  rfl
#align finset.Icc_eq_filter_powerset Finset.Icc_eq_filter_powerset

theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filter ((· ⊆ ·) s) :=
  rfl
#align finset.Ico_eq_filter_ssubsets Finset.Ico_eq_filter_ssubsets

theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filter ((· ⊂ ·) s) :=
  rfl
#align finset.Ioc_eq_filter_powerset Finset.Ioc_eq_filter_powerset

theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filter ((· ⊂ ·) s) :=
  rfl
#align finset.Ioo_eq_filter_ssubsets Finset.Ioo_eq_filter_ssubsets

theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iic_eq_powerset Finset.Iic_eq_powerset

theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iio_eq_ssubsets Finset.Iio_eq_ssubsets

variable {s t}

theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Icc, mem_image, mem_powerset]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h <| hv.trans <| sdiff_subset _ _⟩
#align finset.Icc_eq_image_powerset Finset.Icc_eq_image_powerset

theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩
#align finset.Ico_eq_image_ssubsets Finset.Ico_eq_image_ssubsets

/-- Cardinality of a non-empty `Icc` of finsets. -/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  rw [← card_sdiff h, ← card_powerset, Icc_eq_image_powerset h, Finset.card_image_iff]
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v)
  rw [mem_coe, mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left, ←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left, huv]
#align finset.card_Icc_finset Finset.card_Icc_finset

/-- Cardinality of an `Ico` of finsets. -/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ico_finset Finset.card_Ico_finset

/-- Cardinality of an `Ioc` of finsets. -/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ioc_finset Finset.card_Ioc_finset

/-- Cardinality of an `Ioo` of finsets. -/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]
#align finset.card_Ioo_finset Finset.card_Ioo_finset

/-- Cardinality of an `Iic` of finsets. -/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]
#align finset.card_Iic_finset Finset.card_Iic_finset

/-- Cardinality of an `Iio` of finsets. -/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]
#align finset.card_Iio_finset Finset.card_Iio_finset

end Finset
