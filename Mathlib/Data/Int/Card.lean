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
  rw [Ico_filter_dvd_eq a b hr, card_map, card_Ico, Int.toNat_eq_max]

/-- There are `⌈(b - v) / r⌉ - ⌈(a - v) / r⌉` numbers congruent to `v` modulo `r` in `[a, b)`,
if `a ≤ b`. -/
theorem Int.Ico_filter_modEq_card (a b v : ℤ) {r : ℤ} (hr : 0 < r) :
    ((Ico a b).filter (· ≡ v [ZMOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  suffices : ((Ico a b).filter (· ≡ v [ZMOD r])).card = ((Ico (a - v) (b - v)).filter (r ∣ ·)).card
  · simp only [this, Ico_filter_dvd_card _ _ hr, cast_sub]
  refine card_congr (fun x _ => x - v) ?_ (fun _ _ _ _ => (add_left_inj _).mp) ?_
  · simp only [mem_filter, mem_Ico, tsub_le_iff_right, sub_add_cancel, sub_lt_sub_iff_right,
      and_imp]
    intro c l u m
    exact ⟨⟨l, u⟩, modEq_iff_dvd.mp m.symm⟩
  · simp only [mem_filter, mem_Ico, lt_tsub_iff_right, and_imp]
    intro c l u d
    exact ⟨c + v, by simp_all [(modEq_of_dvd ((add_sub_cancel c v).symm ▸ d)).symm]⟩

/-- `Int.Ico_filter_modEq_card` restricted to natural numbers. -/
theorem Nat.Ico_filter_modEq_card (a b v : ℕ) {r : ℕ} (hr : 0 < r) :
    ((Ico a b).filter (· ≡ v [MOD r])).card =
    max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 := by
  suffices : ((Ico a b).filter (· ≡ v [MOD r])).card = ((Ico ↑a ↑b).filter (· ≡ v [ZMOD r])).card
  · rw [this, Int.Ico_filter_modEq_card _ _ _ (cast_pos.mpr hr)]; norm_cast
  refine card_congr (fun x _ => x) ?_ (fun _ _ _ _ e => by simpa only [cast_inj] using e) ?_
  · simp only [mem_filter, mem_Ico, cast_le, cast_lt, and_imp]
    intro c l u m
    exact ⟨⟨l, u⟩, coe_nat_modEq_iff.mpr m⟩
  · simp only [mem_filter, mem_Ico, and_imp]
    intro c l u d
    lift c to ℕ using (by linarith)
    exact ⟨c, ⟨⟨⟨ofNat_le.mp l, ofNat_lt.mp u⟩, coe_nat_modEq_iff.mp d⟩, rfl⟩⟩

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
