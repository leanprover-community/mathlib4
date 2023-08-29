/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.GroupPower.Lemmas

#align_import data.set.intervals.group from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-! ### Lemmas about arithmetic operations and intervals. -/


variable {α : Type*}

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
theorem mem_Icc_iff_abs_le {R : Type*} [LinearOrderedAddCommGroup R] {x y z : R} :
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
  -- ⊢ Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy))
  · use x
    -- ⊢ x ∈ Ico x (x + dx) \ Ico y (y + dy)
    simp [*, not_le.2 h']
    -- 🎉 no goals
  · use max x (x + dy)
    -- ⊢ max x (x + dy) ∈ Ico x (x + dx) \ Ico y (y + dy)
    simp [*, le_refl]
    -- 🎉 no goals
#align set.nonempty_Ico_sdiff Set.nonempty_Ico_sdiff

end LinearOrderedAddCommGroup

/-! ### Lemmas about disjointness of translates of intervals -/

section PairwiseDisjoint

section OrderedCommGroup

variable [OrderedCommGroup α] (a b : α)

@[to_additive]
theorem pairwise_disjoint_Ioc_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a * b ^ n) (a * b ^ (n + 1))) := by
  simp_rw [Function.onFun, Set.disjoint_iff]
  -- ⊢ Pairwise fun x y => Ioc (a * b ^ x) (a * b ^ (x + 1)) ∩ Ioc (a * b ^ y) (a * …
  intro m n hmn x hx
  -- ⊢ x ∈ ∅
  apply hmn
  -- ⊢ m = n
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_le hx.2.2
  -- ⊢ m = n
  have i2 := hx.2.1.trans_le hx.1.2
  -- ⊢ m = n
  rw [mul_lt_mul_iff_left, zpow_lt_zpow_iff hb, Int.lt_add_one_iff] at i1 i2
  -- ⊢ m = n
  exact le_antisymm i1 i2
  -- 🎉 no goals
#align set.pairwise_disjoint_Ioc_mul_zpow Set.pairwise_disjoint_Ioc_mul_zpow
#align set.pairwise_disjoint_Ioc_add_zsmul Set.pairwise_disjoint_Ioc_add_zsmul

@[to_additive]
theorem pairwise_disjoint_Ico_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (a * b ^ n) (a * b ^ (n + 1))) := by
  simp_rw [Function.onFun, Set.disjoint_iff]
  -- ⊢ Pairwise fun x y => Ico (a * b ^ x) (a * b ^ (x + 1)) ∩ Ico (a * b ^ y) (a * …
  intro m n hmn x hx
  -- ⊢ x ∈ ∅
  apply hmn
  -- ⊢ m = n
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_lt hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_lt hx.2.2
  -- ⊢ m = n
  have i2 := hx.2.1.trans_lt hx.1.2
  -- ⊢ m = n
  rw [mul_lt_mul_iff_left, zpow_lt_zpow_iff hb, Int.lt_add_one_iff] at i1 i2
  -- ⊢ m = n
  exact le_antisymm i1 i2
  -- 🎉 no goals
#align set.pairwise_disjoint_Ico_mul_zpow Set.pairwise_disjoint_Ico_mul_zpow
#align set.pairwise_disjoint_Ico_add_zsmul Set.pairwise_disjoint_Ico_add_zsmul

@[to_additive]
theorem pairwise_disjoint_Ioo_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a * b ^ n) (a * b ^ (n + 1))) := fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self
#align set.pairwise_disjoint_Ioo_mul_zpow Set.pairwise_disjoint_Ioo_mul_zpow
#align set.pairwise_disjoint_Ioo_add_zsmul Set.pairwise_disjoint_Ioo_add_zsmul

@[to_additive]
theorem pairwise_disjoint_Ioc_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioc_mul_zpow 1 b
  -- 🎉 no goals
#align set.pairwise_disjoint_Ioc_zpow Set.pairwise_disjoint_Ioc_zpow
#align set.pairwise_disjoint_Ioc_zsmul Set.pairwise_disjoint_Ioc_zsmul

@[to_additive]
theorem pairwise_disjoint_Ico_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b
  -- 🎉 no goals
#align set.pairwise_disjoint_Ico_zpow Set.pairwise_disjoint_Ico_zpow
#align set.pairwise_disjoint_Ico_zsmul Set.pairwise_disjoint_Ico_zsmul

@[to_additive]
theorem pairwise_disjoint_Ioo_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioo_mul_zpow 1 b
  -- 🎉 no goals
#align set.pairwise_disjoint_Ioo_zpow Set.pairwise_disjoint_Ioo_zpow
#align set.pairwise_disjoint_Ioo_zsmul Set.pairwise_disjoint_Ioo_zsmul

end OrderedCommGroup

section OrderedRing

variable [OrderedRing α] (a : α)

theorem pairwise_disjoint_Ioc_add_int_cast :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioc_add_zsmul a (1 : α)
#align set.pairwise_disjoint_Ioc_add_int_cast Set.pairwise_disjoint_Ioc_add_int_cast

theorem pairwise_disjoint_Ico_add_int_cast :
    Pairwise (Disjoint on fun n : ℤ => Ico (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)
#align set.pairwise_disjoint_Ico_add_int_cast Set.pairwise_disjoint_Ico_add_int_cast

theorem pairwise_disjoint_Ioo_add_int_cast :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioo_add_zsmul a (1 : α)
#align set.pairwise_disjoint_Ioo_add_int_cast Set.pairwise_disjoint_Ioo_add_int_cast

variable (α)

theorem pairwise_disjoint_Ico_int_cast : Pairwise (Disjoint on fun n : ℤ => Ico (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ico_add_int_cast (0 : α)
     -- 🎉 no goals
#align set.pairwise_disjoint_Ico_int_cast Set.pairwise_disjoint_Ico_int_cast

theorem pairwise_disjoint_Ioo_int_cast : Pairwise (Disjoint on fun n : ℤ => Ioo (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioo_add_int_cast (0 : α)
     -- 🎉 no goals
#align set.pairwise_disjoint_Ioo_int_cast Set.pairwise_disjoint_Ioo_int_cast

theorem pairwise_disjoint_Ioc_int_cast : Pairwise (Disjoint on fun n : ℤ => Ioc (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioc_add_int_cast (0 : α)
     -- 🎉 no goals
#align set.pairwise_disjoint_Ioc_int_cast Set.pairwise_disjoint_Ioc_int_cast

end OrderedRing

end PairwiseDisjoint

end Set
