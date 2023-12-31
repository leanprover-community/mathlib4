/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Count
import Mathlib.Data.Rat.Floor

/-!
# Number of elements in an integer/natural number interval congruent to a given number

Pass
-/


open Finset Int

theorem Int.Ico_filter_dvd_eq (a b : ℤ) {r : ℤ} (hr : 0 < r) : (Ico a b).filter (r ∣ ·) =
    (Ico ⌈a / (r : ℚ)⌉ ⌈b / (r : ℚ)⌉).map ⟨_, mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff, lt_div_iff,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/-- There are `⌈b / r⌉ - ⌈a / r⌉` multiples of `r` in `[a, b)`, if `a ≤ b`. -/
theorem Int.Ico_filter_dvd_card (a b : ℤ) {r : ℤ} (hr : 0 < r) :
    ((Ico a b).filter (r ∣ ·)).card = max (⌈b / (r : ℚ)⌉ - ⌈a / (r : ℚ)⌉) 0 := by
  rw [Ico_filter_dvd_eq _ _ hr, card_map, card_Ico, Int.toNat_eq_max]

theorem Int.Ico_filter_modEq_eq (a b v : ℤ) {r : ℤ} : (Ico a b).filter (· ≡ v [ZMOD r]) =
    ((Ico (a - v) (b - v)).filter (r ∣ ·)).map ⟨_, add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` mod `r` in `[a, b)`,
if `a ≤ b`. -/
theorem Int.Ico_filter_modEq_card (a b v : ℤ) {r : ℤ} (hr : 0 < r) :
    ((Ico a b).filter (· ≡ v [ZMOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, Int.toNat_eq_max, hr]

theorem Nat.Ico_filter_modEq_cast (a b v r : ℕ) :
    ((Ico a b).filter (· ≡ v [MOD r])).map castEmbedding = (Ico ↑a ↑b).filter (· ≡ v [ZMOD r]) := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← coe_nat_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to ℕ using (by linarith); exact ⟨x, by simp_all [coe_nat_modEq_iff]⟩

/-- `Int.Ico_filter_modEq_card` restricted to natural numbers. -/
theorem Nat.Ico_filter_modEq_card (a b v : ℕ) {r : ℕ} (hr : 0 < r) :
    ((Ico a b).filter (· ≡ v [MOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  have := Nat.Ico_filter_modEq_cast a b v r ▸ card_map _
  simp_rw [← this, Int.Ico_filter_modEq_card _ _ _ (ofNat_pos.mpr hr), Int.cast_ofNat]

/-- There are `⌈(n - v % r) / r⌉` numbers in `[0, n)` congruent to `v` mod `r`. -/
theorem Nat.count_modEq_card' (n v : ℕ) {r : ℕ} (hr : 0 < r) :
    n.count (· ≡ v [MOD r]) = ⌈(n - (v % r : ℕ)) / (r : ℚ)⌉ := by
  rw [count_eq_card_filter_range, ← Ico_zero_eq_range, Ico_filter_modEq_card _ _ _ hr]
  have : 0 ≤ (⌈(↑n - ↑v) / (r : ℚ)⌉ - ⌈(↑0 - ↑v) / (r : ℚ)⌉) := by
    rw [sub_nonneg]
    apply Int.ceil_mono
    rw [div_le_div_right (by norm_cast)]
    apply tsub_le_tsub_right
    exact cast_nonneg n
  rw [max_eq_left (by exact_mod_cast this)]
  conv_lhs =>
    rw [← div_add_mod v r, cast_add, cast_mul, add_comm,
      ← sub_sub, sub_div, mul_div_cancel_left, ceil_sub_nat,
      ← sub_sub, sub_div (_ - _), mul_div_cancel_left, ceil_sub_nat,
      sub_sub_sub_cancel_right, cast_zero, zero_sub]
    case ha => tactic => exact_mod_cast hr.ne.symm
    case ha => tactic => exact_mod_cast hr.ne.symm
  have : ⌈-↑(v % r) / (r : ℚ)⌉ = 0 := by
    rw [ceil_eq_zero_iff, Set.mem_Ioc,
      div_le_iff (by exact_mod_cast hr), lt_div_iff (by exact_mod_cast hr),
      neg_one_mul, zero_mul, neg_lt_neg_iff, cast_lt]
    exact ⟨Nat.mod_lt _ hr, by simp⟩
  rw [this, sub_zero]

/-- There are `n / r + [v % r < n % r]` numbers in `[0, n)` congruent to `v` mod `r`,
where `[·]` is the Iverson bracket. -/
theorem Nat.count_modEq_card (n v : ℕ) {r : ℕ} (hr : 0 < r) :
    n.count (· ≡ v [MOD r]) = n / r + if v % r < n % r then 1 else 0 := by
  zify; rw [count_modEq_card' n v hr]
  conv_lhs =>
    rw [← div_add_mod n r, cast_add, cast_mul, ← add_sub,
      _root_.add_div, mul_div_cancel_left, add_comm, Int.ceil_add_nat, add_comm]
    case ha => tactic => exact_mod_cast hr.ne.symm
  rw [ofNat_ediv, add_right_inj]
  cases' le_or_gt (n % r) (v % r) with h h
  · conv_rhs => tactic => norm_cast
    rw [← ite_not]
    push_neg
    simp only [h, ite_true, cast_zero]
    rw [ceil_eq_zero_iff, Set.mem_Ioc,
      div_le_iff (by exact_mod_cast hr), lt_div_iff (by exact_mod_cast hr), neg_mul, one_mul,
      neg_lt_sub_iff_lt_add, zero_mul, tsub_le_iff_right, zero_add]
    norm_cast
    exact ⟨(Nat.mod_lt v hr).trans_le (by simp), h⟩
  · conv_rhs => tactic => norm_cast
    simp only [h, ite_true, cast_one]
    rw [Int.ceil_eq_iff, div_le_iff (by exact_mod_cast hr), lt_div_iff (by exact_mod_cast hr),
      Int.cast_one, sub_self, zero_mul, sub_pos, cast_lt, one_mul, tsub_le_iff_right]
    norm_cast
    exact ⟨h, ((Nat.mod_lt n hr).trans_le (by simp)).le⟩
