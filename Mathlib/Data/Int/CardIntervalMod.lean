/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Count
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting elements in an interval with given residue

The theorems in this file generalise `Nat.card_multiples` in `Mathlib.Data.Nat.Factorization.Basic`
to all integer intervals and any fixed residue (not just zero, which reduces to the multiples).
Theorems are given for `Ico` and `Ioc` intervals.
-/


open Finset Int

namespace Int

variable (a b : ℤ) {r : ℤ} (hr : 0 < r)

lemma Ico_filter_dvd_eq : (Ico a b).filter (r ∣ ·) =
    (Ico ⌈a / (r : ℚ)⌉ ⌈b / (r : ℚ)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff, lt_div_iff,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

lemma Ioc_filter_dvd_eq : (Ioc a b).filter (r ∣ ·) =
    (Ioc ⌊a / (r : ℚ)⌋ ⌊b / (r : ℚ)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff, le_div_iff,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/-- There are `⌈b / r⌉ - ⌈a / r⌉` multiples of `r` in `[a, b)`, if `a ≤ b`. -/
theorem Ico_filter_dvd_card : ((Ico a b).filter (r ∣ ·)).card =
    max (⌈b / (r : ℚ)⌉ - ⌈a / (r : ℚ)⌉) 0 := by
  rw [Ico_filter_dvd_eq _ _ hr, card_map, card_Ico, toNat_eq_max]

/-- There are `⌊b / r⌋ - ⌊a / r⌋` multiples of `r` in `(a, b]`, if `a ≤ b`. -/
theorem Ioc_filter_dvd_card : ((Ioc a b).filter (r ∣ ·)).card =
    max (⌊b / (r : ℚ)⌋ - ⌊a / (r : ℚ)⌋) 0 := by
  rw [Ioc_filter_dvd_eq _ _ hr, card_map, card_Ioc, toNat_eq_max]

lemma Ico_filter_modEq_eq (v : ℤ) : (Ico a b).filter (· ≡ v [ZMOD r]) =
    ((Ico (a - v) (b - v)).filter (r ∣ ·)).map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

lemma Ioc_filter_modEq_eq (v : ℤ) : (Ioc a b).filter (· ≡ v [ZMOD r]) =
    ((Ioc (a - v) (b - v)).filter (r ∣ ·)).map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. -/
theorem Ico_filter_modEq_card (v : ℤ) : ((Ico a b).filter (· ≡ v [ZMOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, toNat_eq_max, hr]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. -/
theorem Ioc_filter_modEq_card (v : ℤ) : ((Ioc a b).filter (· ≡ v [ZMOD r])).card =
    max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, toNat_eq_max, hr]

end Int

namespace Nat

variable (a b : ℕ) {r : ℕ} (hr : 0 < r)

lemma Ico_filter_modEq_cast {v : ℕ} : ((Ico a b).filter (· ≡ v [MOD r])).map castEmbedding =
    (Ico (a : ℤ) (b : ℤ)).filter (· ≡ v [ZMOD r]) := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by linarith); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

lemma Ioc_filter_modEq_cast {v : ℕ} : ((Ioc a b).filter (· ≡ v [MOD r])).map castEmbedding =
    (Ioc (a : ℤ) (b : ℤ)).filter (· ≡ v [ZMOD r]) := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by linarith); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. `Nat` version of `Int.Ico_filter_modEq_card`. -/
theorem Ico_filter_modEq_card (v : ℕ) : ((Ico a b).filter (· ≡ v [MOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌊(b - v) / r⌋ - ⌊(a - v) / r⌋` numbers congruent to `v` mod `r` in `(a, b]`,
if `a ≤ b`. `Nat` version of `Int.Ioc_filter_modEq_card`. -/
theorem Ioc_filter_modEq_card (v : ℕ) : ((Ioc a b).filter (· ≡ v [MOD r])).card =
    max (⌊(b - v) / (r : ℚ)⌋ - ⌊(a - v) / (r : ℚ)⌋) 0 := by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/-- There are `⌈(b - v % r) / r⌉` numbers in `[0, b)` congruent to `v` mod `r`. -/
theorem count_modEq_card_eq_ceil (v : ℕ) :
    b.count (· ≡ v [MOD r]) = ⌈(b - (v % r : ℕ)) / (r : ℚ)⌉ := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [count_eq_card_filter_range, ← Ico_zero_eq_range, Ico_filter_modEq_card _ _ hr,
    max_eq_left (sub_nonneg.mpr <| by gcongr <;> positivity)]
  conv_lhs =>
    rw [← div_add_mod v r, cast_add, cast_mul, add_comm]
    tactic => simp_rw [← sub_sub, sub_div (_ - _), mul_div_cancel_left₀ _ hr'.ne', ceil_sub_nat]
    rw [sub_sub_sub_cancel_right, cast_zero, zero_sub]
  rw [sub_eq_self, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff hr', lt_div_iff hr', neg_one_mul,
    zero_mul, neg_lt_neg_iff, cast_lt]
  exact ⟨mod_lt _ hr, by simp⟩

/-- There are `b / r + [v % r < b % r]` numbers in `[0, b)` congruent to `v` mod `r`,
where `[·]` is the Iverson bracket. -/
theorem count_modEq_card (v : ℕ) :
    b.count (· ≡ v [MOD r]) = b / r + if v % r < b % r then 1 else 0 := by
  have hr' : 0 < (r : ℚ) := by positivity
  rw [← ofNat_inj, count_modEq_card_eq_ceil _ hr, cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_nat, add_comm]
  rw [add_right_inj]
  split_ifs with h
  · rw [← cast_sub h.le, Int.ceil_eq_iff, div_le_iff hr', lt_div_iff hr', cast_one, Int.cast_one,
      sub_self, zero_mul, cast_pos, tsub_pos_iff_lt, one_mul, cast_le, tsub_le_iff_right]
    exact ⟨h, ((mod_lt _ hr).trans_le (by simp)).le⟩
  · rw [cast_zero, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff hr', lt_div_iff hr', zero_mul,
      tsub_nonpos, ← neg_eq_neg_one_mul, neg_lt_sub_iff_lt_add, ← cast_add, cast_lt, cast_le]
    exact ⟨(mod_lt _ hr).trans_le (by simp), not_lt.mp h⟩

end Nat
