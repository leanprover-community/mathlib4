/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Data.Set.Intervals.Basic

#align_import data.set.intervals.with_bot_top from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Intervals in `WithTop α` and `WithBot α`

In this file we prove various lemmas about `Set.image`s and `Set.preimage`s of intervals under
`some : α → WithTop α` and `some : α → WithBot α`.
-/

set_option autoImplicit true

open Set

/-! ### `WithTop` -/

namespace WithTop

@[simp]
theorem preimage_coe_top : (some : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun _ => coe_ne_top
#align with_top.preimage_coe_top WithTop.preimage_coe_top

variable [PartialOrder α] {a b : α}

theorem range_coe : range (some : α → WithTop α) = Iio ⊤ := by
  ext x
  rw [mem_Iio, lt_top_iff_ne_top, mem_range, ← none_eq_top, Option.ne_none_iff_exists]
  rfl
#align with_top.range_coe WithTop.range_coe

@[simp]
theorem preimage_coe_Ioi : (some : α → WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe
#align with_top.preimage_coe_Ioi WithTop.preimage_coe_Ioi

@[simp]
theorem preimage_coe_Ici : (some : α → WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe
#align with_top.preimage_coe_Ici WithTop.preimage_coe_Ici

@[simp]
theorem preimage_coe_Iio : (some : α → WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe
#align with_top.preimage_coe_Iio WithTop.preimage_coe_Iio

@[simp]
theorem preimage_coe_Iic : (some : α → WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe
#align with_top.preimage_coe_Iic WithTop.preimage_coe_Iic

@[simp]
theorem preimage_coe_Icc : (some : α → WithTop α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]
#align with_top.preimage_coe_Icc WithTop.preimage_coe_Icc

@[simp]
theorem preimage_coe_Ico : (some : α → WithTop α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]
#align with_top.preimage_coe_Ico WithTop.preimage_coe_Ico

@[simp]
theorem preimage_coe_Ioc : (some : α → WithTop α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]
#align with_top.preimage_coe_Ioc WithTop.preimage_coe_Ioc

@[simp]
theorem preimage_coe_Ioo : (some : α → WithTop α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]
#align with_top.preimage_coe_Ioo WithTop.preimage_coe_Ioo

@[simp]
theorem preimage_coe_Iio_top : (some : α → WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe, preimage_range]
#align with_top.preimage_coe_Iio_top WithTop.preimage_coe_Iio_top

@[simp]
theorem preimage_coe_Ico_top : (some : α → WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [← Ici_inter_Iio]
#align with_top.preimage_coe_Ico_top WithTop.preimage_coe_Ico_top

@[simp]
theorem preimage_coe_Ioo_top : (some : α → WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [← Ioi_inter_Iio]
#align with_top.preimage_coe_Ioo_top WithTop.preimage_coe_Ioo_top

theorem image_coe_Ioi : (some : α → WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]
#align with_top.image_coe_Ioi WithTop.image_coe_Ioi

theorem image_coe_Ici : (some : α → WithTop α) '' Ici a = Ico (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]
#align with_top.image_coe_Ici WithTop.image_coe_Ici

theorem image_coe_Iio : (some : α → WithTop α) '' Iio a = Iio (a : WithTop α) := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]
#align with_top.image_coe_Iio WithTop.image_coe_Iio

theorem image_coe_Iic : (some : α → WithTop α) '' Iic a = Iic (a : WithTop α) := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]
#align with_top.image_coe_Iic WithTop.image_coe_Iic

theorem image_coe_Icc : (some : α → WithTop α) '' Icc a b = Icc (a : WithTop α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]
#align with_top.image_coe_Icc WithTop.image_coe_Icc

theorem image_coe_Ico : (some : α → WithTop α) '' Ico a b = Ico (a : WithTop α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]
#align with_top.image_coe_Ico WithTop.image_coe_Ico

theorem image_coe_Ioc : (some : α → WithTop α) '' Ioc a b = Ioc (a : WithTop α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]
#align with_top.image_coe_Ioc WithTop.image_coe_Ioc

theorem image_coe_Ioo : (some : α → WithTop α) '' Ioo a b = Ioo (a : WithTop α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]
#align with_top.image_coe_Ioo WithTop.image_coe_Ioo

end WithTop

/-! ### `WithBot` -/

namespace WithBot

@[simp]
theorem preimage_coe_bot : (some : α → WithBot α) ⁻¹' {⊥} = (∅ : Set α) :=
  @WithTop.preimage_coe_top αᵒᵈ
#align with_bot.preimage_coe_bot WithBot.preimage_coe_bot

variable [PartialOrder α] {a b : α}

theorem range_coe : range (some : α → WithBot α) = Ioi ⊥ :=
  @WithTop.range_coe αᵒᵈ _
#align with_bot.range_coe WithBot.range_coe

@[simp]
theorem preimage_coe_Ioi : (some : α → WithBot α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe
#align with_bot.preimage_coe_Ioi WithBot.preimage_coe_Ioi

@[simp]
theorem preimage_coe_Ici : (some : α → WithBot α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe
#align with_bot.preimage_coe_Ici WithBot.preimage_coe_Ici

@[simp]
theorem preimage_coe_Iio : (some : α → WithBot α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe
#align with_bot.preimage_coe_Iio WithBot.preimage_coe_Iio

@[simp]
theorem preimage_coe_Iic : (some : α → WithBot α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe
#align with_bot.preimage_coe_Iic WithBot.preimage_coe_Iic

@[simp]
theorem preimage_coe_Icc : (some : α → WithBot α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]
#align with_bot.preimage_coe_Icc WithBot.preimage_coe_Icc

@[simp]
theorem preimage_coe_Ico : (some : α → WithBot α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]
#align with_bot.preimage_coe_Ico WithBot.preimage_coe_Ico

@[simp]
theorem preimage_coe_Ioc : (some : α → WithBot α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]
#align with_bot.preimage_coe_Ioc WithBot.preimage_coe_Ioc

@[simp]
theorem preimage_coe_Ioo : (some : α → WithBot α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]
#align with_bot.preimage_coe_Ioo WithBot.preimage_coe_Ioo

@[simp]
theorem preimage_coe_Ioi_bot : (some : α → WithBot α) ⁻¹' Ioi ⊥ = univ := by
  rw [← range_coe, preimage_range]
#align with_bot.preimage_coe_Ioi_bot WithBot.preimage_coe_Ioi_bot

@[simp]
theorem preimage_coe_Ioc_bot : (some : α → WithBot α) ⁻¹' Ioc ⊥ a = Iic a := by
  simp [← Ioi_inter_Iic]
#align with_bot.preimage_coe_Ioc_bot WithBot.preimage_coe_Ioc_bot

@[simp]
theorem preimage_coe_Ioo_bot : (some : α → WithBot α) ⁻¹' Ioo ⊥ a = Iio a := by
  simp [← Ioi_inter_Iio]
#align with_bot.preimage_coe_Ioo_bot WithBot.preimage_coe_Ioo_bot

theorem image_coe_Iio : (some : α → WithBot α) '' Iio a = Ioo (⊥ : WithBot α) a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iio]
#align with_bot.image_coe_Iio WithBot.image_coe_Iio

theorem image_coe_Iic : (some : α → WithBot α) '' Iic a = Ioc (⊥ : WithBot α) a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iic]
#align with_bot.image_coe_Iic WithBot.image_coe_Iic

theorem image_coe_Ioi : (some : α → WithBot α) '' Ioi a = Ioi (a : WithBot α) := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioi WithBot.image_coe_Ioi

theorem image_coe_Ici : (some : α → WithBot α) '' Ici a = Ici (a : WithBot α) := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Ici WithBot.image_coe_Ici

theorem image_coe_Icc : (some : α → WithBot α) '' Icc a b = Icc (a : WithBot α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Icc WithBot.image_coe_Icc

theorem image_coe_Ioc : (some : α → WithBot α) '' Ioc a b = Ioc (a : WithBot α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioc_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioc WithBot.image_coe_Ioc

theorem image_coe_Ico : (some : α → WithBot α) '' Ico a b = Ico (a : WithBot α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ico_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]
#align with_bot.image_coe_Ico WithBot.image_coe_Ico

theorem image_coe_Ioo : (some : α → WithBot α) '' Ioo a b = Ioo (a : WithBot α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]
#align with_bot.image_coe_Ioo WithBot.image_coe_Ioo

end WithBot
