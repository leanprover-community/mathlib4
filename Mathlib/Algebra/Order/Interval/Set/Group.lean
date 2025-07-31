/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Pairwise

/-! ### Lemmas about arithmetic operations and intervals. -/


variable {α : Type*}

namespace Set

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.Icc c d ↔ a ∈ Set.Icc d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_le' le_inv'

@[to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.Ico c d ↔ a ∈ Set.Ioc d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_lt' le_inv'

@[to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.Ioc c d ↔ a ∈ Set.Ico d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_le' lt_inv'

@[to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.Ioo c d ↔ a ∈ Set.Ioo d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_lt' lt_inv'

end OrderedCommGroup

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/

theorem add_mem_Icc_iff_left : a + b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

theorem add_mem_Ico_iff_left : a + b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

theorem add_mem_Ioc_iff_left : a + b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

theorem add_mem_Ioo_iff_left : a + b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

/-! `add_mem_Ixx_iff_right` -/

theorem add_mem_Icc_iff_right : a + b ∈ Set.Icc c d ↔ b ∈ Set.Icc (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

theorem add_mem_Ico_iff_right : a + b ∈ Set.Ico c d ↔ b ∈ Set.Ico (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

theorem add_mem_Ioc_iff_right : a + b ∈ Set.Ioc c d ↔ b ∈ Set.Ioc (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

theorem add_mem_Ioo_iff_right : a + b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

/-! `sub_mem_Ixx_iff_left` -/

theorem sub_mem_Icc_iff_left : a - b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add

theorem sub_mem_Ico_iff_left : a - b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/

theorem sub_mem_Icc_iff_right : a - b ∈ Set.Icc c d ↔ b ∈ Set.Icc (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm le_sub_comm

theorem sub_mem_Ico_iff_right : a - b ∈ Set.Ico c d ↔ b ∈ Set.Ioc (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_lt_comm le_sub_comm

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.Ioc c d ↔ b ∈ Set.Ico (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm lt_sub_comm

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_lt_comm lt_sub_comm

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
theorem mem_Icc_iff_abs_le {R : Type*}
    [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
  abs_le.trans <| and_comm.trans <| and_congr sub_le_comm neg_le_sub_iff_le_add

/-! `sub_mem_Ixx_zero_right` and `sub_mem_Ixx_zero_iff_right`; this specializes the previous
lemmas to the case of reflecting the interval. -/

theorem sub_mem_Icc_zero_iff_right : b - a ∈ Icc 0 b ↔ a ∈ Icc 0 b := by
  simp only [sub_mem_Icc_iff_right, sub_self, sub_zero]

theorem sub_mem_Ico_zero_iff_right : b - a ∈ Ico 0 b ↔ a ∈ Ioc 0 b := by
  simp only [sub_mem_Ico_iff_right, sub_self, sub_zero]

theorem sub_mem_Ioc_zero_iff_right : b - a ∈ Ioc 0 b ↔ a ∈ Ico 0 b := by
  simp only [sub_mem_Ioc_iff_right, sub_self, sub_zero]

theorem sub_mem_Ioo_zero_iff_right : b - a ∈ Ioo 0 b ↔ a ∈ Ioo 0 b := by
  simp only [sub_mem_Ioo_iff_right, sub_self, sub_zero]

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy)) := by
  rcases lt_or_ge x y with h' | h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*]

end LinearOrderedAddCommGroup

/-! ### Lemmas about disjointness of translates of intervals -/

open scoped Function -- required for scoped `on` notation
section PairwiseDisjoint

section OrderedCommGroup

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b : α)

@[to_additive]
theorem pairwise_disjoint_Ioc_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a * b ^ n) (a * b ^ (n + 1))) := by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_le hx.2.2
  have i2 := hx.2.1.trans_le hx.1.2
  rw [mul_lt_mul_iff_left, zpow_lt_zpow_iff_right hb, Int.lt_add_one_iff] at i1 i2
  exact le_antisymm i1 i2

@[to_additive]
theorem pairwise_disjoint_Ico_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (a * b ^ n) (a * b ^ (n + 1))) := by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_lt hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_lt hx.2.2
  have i2 := hx.2.1.trans_lt hx.1.2
  rw [mul_lt_mul_iff_left, zpow_lt_zpow_iff_right hb, Int.lt_add_one_iff] at i1 i2
  exact le_antisymm i1 i2

@[to_additive]
theorem pairwise_disjoint_Ioo_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a * b ^ n) (a * b ^ (n + 1))) := fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

@[to_additive]
theorem pairwise_disjoint_Ioc_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioc_mul_zpow 1 b

@[to_additive]
theorem pairwise_disjoint_Ico_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b

@[to_additive]
theorem pairwise_disjoint_Ioo_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ioo_mul_zpow 1 b

end OrderedCommGroup

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] (a : α)

theorem pairwise_disjoint_Ioc_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioc_add_zsmul a (1 : α)

theorem pairwise_disjoint_Ico_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)

theorem pairwise_disjoint_Ioo_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ioo_add_zsmul a (1 : α)

variable (α)

theorem pairwise_disjoint_Ico_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ico_add_intCast (0 : α)

theorem pairwise_disjoint_Ioo_intCast : Pairwise (Disjoint on fun n : ℤ => Ioo (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

theorem pairwise_disjoint_Ioc_intCast : Pairwise (Disjoint on fun n : ℤ => Ioc (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioc_add_intCast (0 : α)

end OrderedRing

end PairwiseDisjoint

end Set
