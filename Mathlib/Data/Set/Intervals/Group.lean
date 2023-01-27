/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
Ported by: Winston Yin

! This file was ported from Lean 3 source module data.set.intervals.group
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
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
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.Icc c d ↔ a ∈ Set.Icc d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_le' le_inv'
#align set.inv_mem_Icc_iff Set.inv_mem_Icc_iff
#align set.neg_mem_Icc_iff Set.neg_mem_Icc_iff

@[to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.Ico c d ↔ a ∈ Set.Ioc d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_lt' le_inv'
#align set.inv_mem_Ico_iff Set.inv_mem_Ico_iff
#align set.neg_mem_Ico_iff Set.neg_mem_Ico_iff

@[to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.Ioc c d ↔ a ∈ Set.Ico d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_le' lt_inv'
#align set.inv_mem_Ioc_iff Set.inv_mem_Ioc_iff
#align set.neg_mem_Ioc_iff Set.neg_mem_Ioc_iff

@[to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.Ioo c d ↔ a ∈ Set.Ioo d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_lt' lt_inv'
#align set.inv_mem_Ioo_iff Set.inv_mem_Ioo_iff
#align set.neg_mem_Ioo_iff Set.neg_mem_Ioo_iff

end OrderedCommGroup

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/


-- Porting note: instance search needs help `(α := α)`
theorem add_mem_Icc_iff_left : a + b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c - b) (d - b) :=
  (and_congr (sub_le_iff_le_add (α := α)) (le_sub_iff_add_le (α := α))).symm
#align set.add_mem_Icc_iff_left Set.add_mem_Icc_iff_left

theorem add_mem_Ico_iff_left : a + b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c - b) (d - b) :=
  (and_congr (sub_le_iff_le_add (α := α)) (lt_sub_iff_add_lt (α := α))).symm
#align set.add_mem_Ico_iff_left Set.add_mem_Ico_iff_left

theorem add_mem_Ioc_iff_left : a + b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c - b) (d - b) :=
  (and_congr (sub_lt_iff_lt_add (α := α)) (le_sub_iff_add_le (α := α))).symm
#align set.add_mem_Ioc_iff_left Set.add_mem_Ioc_iff_left

theorem add_mem_Ioo_iff_left : a + b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c - b) (d - b) :=
  (and_congr (sub_lt_iff_lt_add (α := α)) (lt_sub_iff_add_lt (α := α))).symm
#align set.add_mem_Ioo_iff_left Set.add_mem_Ioo_iff_left

/-! `add_mem_Ixx_iff_right` -/


theorem add_mem_Icc_iff_right : a + b ∈ Set.Icc c d ↔ b ∈ Set.Icc (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm
#align set.add_mem_Icc_iff_right Set.add_mem_Icc_iff_right

theorem add_mem_Ico_iff_right : a + b ∈ Set.Ico c d ↔ b ∈ Set.Ico (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm
#align set.add_mem_Ico_iff_right Set.add_mem_Ico_iff_right

theorem add_mem_Ioc_iff_right : a + b ∈ Set.Ioc c d ↔ b ∈ Set.Ioc (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm
#align set.add_mem_Ioc_iff_right Set.add_mem_Ioc_iff_right

theorem add_mem_Ioo_iff_right : a + b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm
#align set.add_mem_Ioo_iff_right Set.add_mem_Ioo_iff_right

/-! `sub_mem_Ixx_iff_left` -/


theorem sub_mem_Icc_iff_left : a - b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add
#align set.sub_mem_Icc_iff_left Set.sub_mem_Icc_iff_left

theorem sub_mem_Ico_iff_left : a - b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add
#align set.sub_mem_Ico_iff_left Set.sub_mem_Ico_iff_left

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add
#align set.sub_mem_Ioc_iff_left Set.sub_mem_Ioc_iff_left

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add
#align set.sub_mem_Ioo_iff_left Set.sub_mem_Ioo_iff_left

/-! `sub_mem_Ixx_iff_right` -/


theorem sub_mem_Icc_iff_right : a - b ∈ Set.Icc c d ↔ b ∈ Set.Icc (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm le_sub_comm
#align set.sub_mem_Icc_iff_right Set.sub_mem_Icc_iff_right

theorem sub_mem_Ico_iff_right : a - b ∈ Set.Ico c d ↔ b ∈ Set.Ioc (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_lt_comm le_sub_comm
#align set.sub_mem_Ico_iff_right Set.sub_mem_Ico_iff_right

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.Ioc c d ↔ b ∈ Set.Ico (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm lt_sub_comm
#align set.sub_mem_Ioc_iff_right Set.sub_mem_Ioc_iff_right

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_lt_comm lt_sub_comm
#align set.sub_mem_Ioo_iff_right Set.sub_mem_Ioo_iff_right

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
theorem mem_Icc_iff_abs_le {R : Type _} [LinearOrderedAddCommGroup R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
  abs_le.trans <| and_comm.trans <| and_congr sub_le_comm neg_le_sub_iff_le_add
#align set.mem_Icc_iff_abs_le Set.mem_Icc_iff_abs_le

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy)) := by
  cases' lt_or_le x y with h' h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*, le_refl]
#align set.nonempty_Ico_sdiff Set.nonempty_Ico_sdiff

end LinearOrderedAddCommGroup

end Set
