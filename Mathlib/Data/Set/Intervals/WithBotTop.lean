/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
! This file was ported from Lean 3 source module data.set.intervals.with_bot_top
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.Basic

/-!
# Intervals in `with_top α` and `with_bot α`
In this file we prove various lemmas about `set.image`s and `set.preimage`s of intervals under
`coe : α → with_top α` and `coe : α → with_bot α`.
-/


open Set

variable {α : Type _}

/-! ### `with_top` -/


namespace WithTop

@[simp]
theorem preimage_coe_top : (coe : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun a => coe_ne_top
#align with_top.preimage_coe_top WithTop.preimage_coe_top

variable [PartialOrder α] {a b : α}

theorem range_coe : range (coe : α → WithTop α) = iio ⊤ := by
  ext x
  rw [mem_Iio, lt_top_iff_ne_top, mem_range, ← none_eq_top, Option.ne_none_iff_exists]
  rfl
#align with_top.range_coe WithTop.range_coe

@[simp]
theorem preimage_coe_Ioi : (coe : α → WithTop α) ⁻¹' ioi a = ioi a :=
  ext fun x => coe_lt_coe
#align with_top.preimage_coe_Ioi WithTop.preimage_coe_Ioi

@[simp]
theorem preimage_coe_Ici : (coe : α → WithTop α) ⁻¹' ici a = ici a :=
  ext fun x => coe_le_coe
#align with_top.preimage_coe_Ici WithTop.preimage_coe_Ici

@[simp]
theorem preimage_coe_Iio : (coe : α → WithTop α) ⁻¹' iio a = iio a :=
  ext fun x => coe_lt_coe
#align with_top.preimage_coe_Iio WithTop.preimage_coe_Iio

@[simp]
theorem preimage_coe_Iic : (coe : α → WithTop α) ⁻¹' iic a = iic a :=
  ext fun x => coe_le_coe
#align with_top.preimage_coe_Iic WithTop.preimage_coe_Iic

@[simp]
theorem preimage_coe_Icc : (coe : α → WithTop α) ⁻¹' icc a b = icc a b := by simp [← Ici_inter_Iic]
#align with_top.preimage_coe_Icc WithTop.preimage_coe_Icc

@[simp]
theorem preimage_coe_Ico : (coe : α → WithTop α) ⁻¹' ico a b = ico a b := by simp [← Ici_inter_Iio]
#align with_top.preimage_coe_Ico WithTop.preimage_coe_Ico

@[simp]
theorem preimage_coe_Ioc : (coe : α → WithTop α) ⁻¹' ioc a b = ioc a b := by simp [← Ioi_inter_Iic]
#align with_top.preimage_coe_Ioc WithTop.preimage_coe_Ioc

@[simp]
theorem preimage_coe_Ioo : (coe : α → WithTop α) ⁻¹' ioo a b = ioo a b := by simp [← Ioi_inter_Iio]
#align with_top.preimage_coe_Ioo WithTop.preimage_coe_Ioo

@[simp]
theorem preimage_coe_Iio_top : (coe : α → WithTop α) ⁻¹' iio ⊤ = univ := by
  rw [← range_coe, preimage_range]
#align with_top.preimage_coe_Iio_top WithTop.preimage_coe_Iio_top

@[simp]
theorem preimage_coe_Ico_top : (coe : α → WithTop α) ⁻¹' ico a ⊤ = ici a := by
  simp [← Ici_inter_Iio]
#align with_top.preimage_coe_Ico_top WithTop.preimage_coe_Ico_top

@[simp]
theorem preimage_coe_Ioo_top : (coe : α → WithTop α) ⁻¹' ioo a ⊤ = ioi a := by
  simp [← Ioi_inter_Iio]
#align with_top.preimage_coe_Ioo_top WithTop.preimage_coe_Ioo_top

theorem image_coe_Ioi : (coe : α → WithTop α) '' ioi a = ioo a ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]
#align with_top.image_coe_Ioi WithTop.image_coe_Ioi

theorem image_coe_Ici : (coe : α → WithTop α) '' ici a = ico a ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]
#align with_top.image_coe_Ici WithTop.image_coe_Ici

theorem image_coe_Iio : (coe : α → WithTop α) '' iio a = iio a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]
#align with_top.image_coe_Iio WithTop.image_coe_Iio

theorem image_coe_Iic : (coe : α → WithTop α) '' iic a = iic a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]
#align with_top.image_coe_Iic WithTop.image_coe_Iic

theorem image_coe_Icc : (coe : α → WithTop α) '' icc a b = icc a b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]
#align with_top.image_coe_Icc WithTop.image_coe_Icc

theorem image_coe_Ico : (coe : α → WithTop α) '' ico a b = ico a b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]
#align with_top.image_coe_Ico WithTop.image_coe_Ico

theorem image_coe_Ioc : (coe : α → WithTop α) '' ioc a b = ioc a b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]
#align with_top.image_coe_Ioc WithTop.image_coe_Ioc

theorem image_coe_Ioo : (coe : α → WithTop α) '' ioo a b = ioo a b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]
#align with_top.image_coe_Ioo WithTop.image_coe_Ioo

end WithTop

/-! ### `with_bot` -/


namespace WithBot

@[simp]
theorem preimage_coe_bot : (coe : α → WithBot α) ⁻¹' {⊥} = (∅ : Set α) :=
  @WithTop.preimage_coe_top αᵒᵈ
#align with_bot.preimage_coe_bot WithBot.preimage_coe_bot

variable [PartialOrder α] {a b : α}

theorem range_coe : range (coe : α → WithBot α) = ioi ⊥ :=
  @WithTop.range_coe αᵒᵈ _
#align with_bot.range_coe WithBot.range_coe

@[simp]
theorem preimage_coe_Ioi : (coe : α → WithBot α) ⁻¹' ioi a = ioi a :=
  ext fun x => coe_lt_coe
#align with_bot.preimage_coe_Ioi WithBot.preimage_coe_Ioi

@[simp]
theorem preimage_coe_Ici : (coe : α → WithBot α) ⁻¹' ici a = ici a :=
  ext fun x => coe_le_coe
#align with_bot.preimage_coe_Ici WithBot.preimage_coe_Ici

@[simp]
theorem preimage_coe_Iio : (coe : α → WithBot α) ⁻¹' iio a = iio a :=
  ext fun x => coe_lt_coe
#align with_bot.preimage_coe_Iio WithBot.preimage_coe_Iio

@[simp]
theorem preimage_coe_Iic : (coe : α → WithBot α) ⁻¹' iic a = iic a :=
  ext fun x => coe_le_coe
#align with_bot.preimage_coe_Iic WithBot.preimage_coe_Iic

@[simp]
theorem preimage_coe_Icc : (coe : α → WithBot α) ⁻¹' icc a b = icc a b := by simp [← Ici_inter_Iic]
#align with_bot.preimage_coe_Icc WithBot.preimage_coe_Icc

@[simp]
theorem preimage_coe_Ico : (coe : α → WithBot α) ⁻¹' ico a b = ico a b := by simp [← Ici_inter_Iio]
#align with_bot.preimage_coe_Ico WithBot.preimage_coe_Ico

@[simp]
theorem preimage_coe_Ioc : (coe : α → WithBot α) ⁻¹' ioc a b = ioc a b := by simp [← Ioi_inter_Iic]
#align with_bot.preimage_coe_Ioc WithBot.preimage_coe_Ioc

@[simp]
theorem preimage_coe_Ioo : (coe : α → WithBot α) ⁻¹' ioo a b = ioo a b := by simp [← Ioi_inter_Iio]
#align with_bot.preimage_coe_Ioo WithBot.preimage_coe_Ioo

@[simp]
theorem preimage_coe_Ioi_bot : (coe : α → WithBot α) ⁻¹' ioi ⊥ = univ := by
  rw [← range_coe, preimage_range]
#align with_bot.preimage_coe_Ioi_bot WithBot.preimage_coe_Ioi_bot

@[simp]
theorem preimage_coe_Ioc_bot : (coe : α → WithBot α) ⁻¹' ioc ⊥ a = iic a := by
  simp [← Ioi_inter_Iic]
#align with_bot.preimage_coe_Ioc_bot WithBot.preimage_coe_Ioc_bot

@[simp]
theorem preimage_coe_Ioo_bot : (coe : α → WithBot α) ⁻¹' ioo ⊥ a = iio a := by
  simp [← Ioi_inter_Iio]
#align with_bot.preimage_coe_Ioo_bot WithBot.preimage_coe_Ioo_bot

theorem image_coe_Iio : (coe : α → WithBot α) '' iio a = ioo ⊥ a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iio]
#align with_bot.image_coe_Iio WithBot.image_coe_Iio

theorem image_coe_Iic : (coe : α → WithBot α) '' iic a = ioc ⊥ a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iic]
#align with_bot.image_coe_Iic WithBot.image_coe_Iic

theorem image_coe_Ioi : (coe : α → WithBot α) '' ioi a = ioi a := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioi WithBot.image_coe_Ioi

theorem image_coe_Ici : (coe : α → WithBot α) '' ici a = ici a := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Ici WithBot.image_coe_Ici

theorem image_coe_Icc : (coe : α → WithBot α) '' icc a b = icc a b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (subset.trans Icc_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Icc WithBot.image_coe_Icc

theorem image_coe_Ioc : (coe : α → WithBot α) '' ioc a b = ioc a b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioc_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioc WithBot.image_coe_Ioc

theorem image_coe_Ico : (coe : α → WithBot α) '' ico a b = ico a b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (subset.trans Ico_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Ico WithBot.image_coe_Ico

theorem image_coe_Ioo : (coe : α → WithBot α) '' ioo a b = ioo a b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioo_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioo WithBot.image_coe_Ioo

end WithBot
