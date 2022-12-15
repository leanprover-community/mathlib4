/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne

! This file was ported from Lean 3 source module data.set.intervals.group
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Algebra.Order.Group.Abs

/-! ### Lemmas about arithmetic operations and intervals. -/


variable {α : Type _}

namespace Set

section OrderedCommGroup

variable [OrderedCommGroup α] {a b c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.icc c d ↔ a ∈ Set.icc d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' le_inv'
#align set.inv_mem_Icc_iff Set.inv_mem_Icc_iff

@[to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.ico c d ↔ a ∈ Set.ioc d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' le_inv'
#align set.inv_mem_Ico_iff Set.inv_mem_Ico_iff

@[to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.ioc c d ↔ a ∈ Set.ico d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' lt_inv'
#align set.inv_mem_Ioc_iff Set.inv_mem_Ioc_iff

@[to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.ioo c d ↔ a ∈ Set.ioo d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' lt_inv'
#align set.inv_mem_Ioo_iff Set.inv_mem_Ioo_iff

end OrderedCommGroup

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/


theorem add_mem_Icc_iff_left : a + b ∈ Set.icc c d ↔ a ∈ Set.icc (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm
#align set.add_mem_Icc_iff_left Set.add_mem_Icc_iff_left

theorem add_mem_Ico_iff_left : a + b ∈ Set.ico c d ↔ a ∈ Set.ico (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm
#align set.add_mem_Ico_iff_left Set.add_mem_Ico_iff_left

theorem add_mem_Ioc_iff_left : a + b ∈ Set.ioc c d ↔ a ∈ Set.ioc (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm
#align set.add_mem_Ioc_iff_left Set.add_mem_Ioc_iff_left

theorem add_mem_Ioo_iff_left : a + b ∈ Set.ioo c d ↔ a ∈ Set.ioo (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm
#align set.add_mem_Ioo_iff_left Set.add_mem_Ioo_iff_left

/-! `add_mem_Ixx_iff_right` -/


theorem add_mem_Icc_iff_right : a + b ∈ Set.icc c d ↔ b ∈ Set.icc (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm
#align set.add_mem_Icc_iff_right Set.add_mem_Icc_iff_right

theorem add_mem_Ico_iff_right : a + b ∈ Set.ico c d ↔ b ∈ Set.ico (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm
#align set.add_mem_Ico_iff_right Set.add_mem_Ico_iff_right

theorem add_mem_Ioc_iff_right : a + b ∈ Set.ioc c d ↔ b ∈ Set.ioc (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm
#align set.add_mem_Ioc_iff_right Set.add_mem_Ioc_iff_right

theorem add_mem_Ioo_iff_right : a + b ∈ Set.ioo c d ↔ b ∈ Set.ioo (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm
#align set.add_mem_Ioo_iff_right Set.add_mem_Ioo_iff_right

/-! `sub_mem_Ixx_iff_left` -/


theorem sub_mem_Icc_iff_left : a - b ∈ Set.icc c d ↔ a ∈ Set.icc (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add
#align set.sub_mem_Icc_iff_left Set.sub_mem_Icc_iff_left

theorem sub_mem_Ico_iff_left : a - b ∈ Set.ico c d ↔ a ∈ Set.ico (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add
#align set.sub_mem_Ico_iff_left Set.sub_mem_Ico_iff_left

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.ioc c d ↔ a ∈ Set.ioc (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add
#align set.sub_mem_Ioc_iff_left Set.sub_mem_Ioc_iff_left

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.ioo c d ↔ a ∈ Set.ioo (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add
#align set.sub_mem_Ioo_iff_left Set.sub_mem_Ioo_iff_left

/-! `sub_mem_Ixx_iff_right` -/


theorem sub_mem_Icc_iff_right : a - b ∈ Set.icc c d ↔ b ∈ Set.icc (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le_comm le_sub_comm
#align set.sub_mem_Icc_iff_right Set.sub_mem_Icc_iff_right

theorem sub_mem_Ico_iff_right : a - b ∈ Set.ico c d ↔ b ∈ Set.ioc (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt_comm le_sub_comm
#align set.sub_mem_Ico_iff_right Set.sub_mem_Ico_iff_right

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.ioc c d ↔ b ∈ Set.ico (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le_comm lt_sub_comm
#align set.sub_mem_Ioc_iff_right Set.sub_mem_Ioc_iff_right

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.ioo c d ↔ b ∈ Set.ioo (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt_comm lt_sub_comm
#align set.sub_mem_Ioo_iff_right Set.sub_mem_Ioo_iff_right

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
theorem mem_Icc_iff_abs_le {R : Type _} [LinearOrderedAddCommGroup R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ icc (x - z) (x + z) :=
  abs_le.trans <| (and_comm' _ _).trans <| and_congr sub_le_comm neg_le_sub_iff_le_add
#align set.mem_Icc_iff_abs_le Set.mem_Icc_iff_abs_le

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↥(ico x (x + dx) \ ico y (y + dy)) := by
  cases' lt_or_le x y with h' h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*, le_refl]
#align set.nonempty_Ico_sdiff Set.nonempty_Ico_sdiff

end LinearOrderedAddCommGroup

end Set
