/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Membership in intervals via `Int.floor` / `Nat.floor`

For a `FloorRing` (resp. `FloorSemiring`) `α`, we relate membership of a cast `↑n` in an interval
of `α` to membership of the integer (resp. natural number) `n` in the corresponding interval with
floor/ceil endpoints, for instance `Int.coe_mem_Ioc_iff : ↑n ∈ Set.Ioc a b ↔ n ∈ Set.Ioc ⌊a⌋ ⌊b⌋`.
If the right-hand side set is finite, we express it as `Finset` instead.

In the natural number case, non-negativity hypotheses are required when the `Nat.floor` function
is involved.  In the `IsStrictOrderedRing` case, one of these hypotheses can be omitted.
-/

@[expose] public section

namespace Int

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α] {a b : α} {n : ℤ}

lemma coe_mem_Ioc_iff : ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ := by
  simp [floor_lt, le_floor]

lemma coe_mem_Ico_iff : ↑n ∈ Set.Ico a b ↔ n ∈ Finset.Ico ⌈a⌉ ⌈b⌉ := by
  simp [ceil_le, lt_ceil]

lemma coe_mem_Icc_iff : ↑n ∈ Set.Icc a b ↔ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋ := by
  simp [ceil_le, le_floor]

lemma coe_mem_Ioo_iff : ↑n ∈ Set.Ioo a b ↔ n ∈ Finset.Ioo ⌊a⌋ ⌈b⌉ := by
  simp [floor_lt, lt_ceil]

lemma coe_mem_Ioi_iff : ↑n ∈ Set.Ioi a ↔ n ∈ Set.Ioi ⌊a⌋ := by simp [floor_lt]

lemma coe_mem_Ici_iff : ↑n ∈ Set.Ici a ↔ n ∈ Set.Ici ⌈a⌉ := by simp [ceil_le]

lemma coe_mem_Iic_iff : ↑n ∈ Set.Iic b ↔ n ∈ Set.Iic ⌊b⌋ := by simp [le_floor]

lemma coe_mem_Iio_iff : ↑n ∈ Set.Iio b ↔ n ∈ Set.Iio ⌈b⌉ := by simp [lt_ceil]

end Int

namespace Nat

variable {α : Type*} [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : ℕ}

lemma coe_mem_Ioc_iff (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by simp [floor_lt ha, le_floor_iff hb]

/-- The `0 ≤ b` hypothesis in `coe_mem_Ioc_iff` can be dropped if `IsStrictOrderedRing α`. -/
lemma coe_mem_Ioc_iff' [IsStrictOrderedRing α] (ha : 0 ≤ a) :
    ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  rcases le_or_gt 0 b with hb | hb
  · exact coe_mem_Ioc_iff ha hb
  · grind [floor_of_nonpos hb.le]

lemma coe_mem_Ico_iff : ↑n ∈ Set.Ico a b ↔ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  simp [ceil_le, lt_ceil]

lemma coe_mem_Icc_iff (hb : 0 ≤ b) : ↑n ∈ Set.Icc a b ↔ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  simp [ceil_le, le_floor_iff hb]

lemma coe_mem_Ioo_iff (ha : 0 ≤ a) : ↑n ∈ Set.Ioo a b ↔ n ∈ Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  simp [floor_lt ha, lt_ceil]

lemma coe_mem_Iic_iff (hb : 0 ≤ b) : ↑n ∈ Set.Iic b ↔ n ∈ Finset.Iic ⌊b⌋₊ := by
  simp [le_floor_iff hb]

lemma coe_mem_Iio_iff : ↑n ∈ Set.Iio b ↔ n ∈ Finset.Iio ⌈b⌉₊ := by simp [lt_ceil]

lemma coe_mem_Ioi_iff (ha : 0 ≤ a) : ↑n ∈ Set.Ioi a ↔ n ∈ Set.Ioi ⌊a⌋₊ := by simp [floor_lt ha]

lemma coe_mem_Ici_iff : ↑n ∈ Set.Ici a ↔ n ∈ Set.Ici ⌈a⌉₊ := by simp [ceil_le]

end Nat
