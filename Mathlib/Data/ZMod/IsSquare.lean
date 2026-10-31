/-
Copyright (c) 2026 Arsen A. Khachatryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arsen A. Khachatryan
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Squares of odd integers in `ZMod (2 ^ n)`

For an odd integer `a`, `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ min n 3)`.

## Main results

* `ZMod.isSquare_two_pow_iff_of_odd_three_le`: for `3 ≤ n`, `↔ a ≡ 1 (mod 8)`.
* `ZMod.isSquare_two_pow_iff_of_odd_le_three`: for `n ≤ 3`, `↔ a ≡ 1 (mod 2 ^ n)`.
* `ZMod.isSquare_two_pow_iff_of_odd`: the statement for all `n` at once, using `min n 3`;
  the two results above are its specializations.
-/

@[expose] public section

namespace ZMod

/-- The square of an odd integer is `1` modulo `8`. -/
private theorem odd_sq_modEq_one_eight (w : ℤ) (hw : Odd w) : w ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨i, hi⟩ := Int.even_mul_succ_self j
  exact Int.modEq_iff_dvd.mpr ⟨-i, by linear_combination (-4 : ℤ) * hi⟩

/-- Lifting a square root of `c ≡ 1 (mod 8)` to all moduli `8 * 2 ^ j`.
The usual Hensel lemma does not apply here, since the derivative `2 * y` of `y ^ 2 - c`
is never a unit at `p = 2`. -/
private theorem sq_lift_aux (c : ℤ) (hc : c ≡ 1 [ZMOD 8]) :
    ∀ j : ℕ, ∃ y : ℤ, Odd y ∧ y ^ 2 ≡ c [ZMOD 8 * 2 ^ j] := by
  intro j
  induction j with
  | zero => exact ⟨1, odd_one, by simpa using hc.symm⟩
  | succ j ih =>
    obtain ⟨y, ⟨m, rfl⟩, hy⟩ := ih
    obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hy
    refine ⟨2 * m + 1 + 4 * 2 ^ j * d, ⟨m + 2 * 2 ^ j * d, by ring⟩,
      Int.modEq_iff_dvd.mpr ⟨-(m * d) - 2 ^ j * d ^ 2, ?_⟩⟩
    rw [pow_succ]
    linear_combination hd

/-- If `c ≡ 1 (mod 8)`, then `c` is a square modulo every power of `2`. -/
private theorem exists_sq_modEq_of_modEq_one_eight (c : ℤ) (hc : c ≡ 1 [ZMOD 8]) (k : ℕ) :
    ∃ y : ℤ, y ^ 2 ≡ c [ZMOD 2 ^ k] := by
  rcases le_or_gt 3 k with hk | hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨y, -, hy⟩ := sq_lift_aux c hc j
    exact ⟨y, by rwa [show (2 : ℤ) ^ (3 + j) = 8 * 2 ^ j by rw [pow_add]; norm_num]⟩
  · refine ⟨1, Int.modEq_iff_dvd.mpr ?_⟩
    have h : (2 : ℤ) ^ k ∣ 8 := by simpa using pow_dvd_pow (2 : ℤ) (by omega : k ≤ 3)
    simpa using h.trans (Int.modEq_iff_dvd.mp hc.symm)

/-- A square in `ZMod (2 ^ n)` comes from an integer square. -/
private theorem exists_int_sq {n : ℕ} {a : ℤ} (h : IsSquare (a : ZMod (2 ^ n))) :
    ∃ y : ℤ, a ≡ y ^ 2 [ZMOD (2 : ℤ) ^ n] := by
  have : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  obtain ⟨r, hr⟩ := h
  refine ⟨r.val, ?_⟩
  have key := (ZMod.intCast_eq_intCast_iff a ((r.val : ℤ) ^ 2) (2 ^ n)).mp <| by
    rw [hr]; push_cast [ZMod.natCast_zmod_val]; ring
  exact_mod_cast key

/-- Necessity: an odd square in `ZMod (2 ^ n)` is `1` modulo `2 ^ min n 3`. -/
private theorem modEq_one_of_isSquare {a : ℤ} {n : ℕ} (ha : Odd a)
    (h : IsSquare (a : ZMod (2 ^ n))) : a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3] := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [Nat.zero_min, pow_zero]
    exact Int.modEq_one
  obtain ⟨y, hy⟩ := exists_int_sq h
  have hyodd : Odd y := by
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self (y - 1)
    have ha2 : a ≡ y [ZMOD 2] := (hy.of_dvd (dvd_pow_self 2 hn.ne')).trans
      (Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩)
    rw [Int.odd_iff] at ha ⊢
    rw [Int.ModEq] at ha2
    omega
  exact (hy.of_dvd (pow_dvd_pow 2 (min_le_left n 3))).trans <|
    (odd_sq_modEq_one_eight y hyodd).of_dvd <|
      (pow_dvd_pow 2 (min_le_right n 3)).trans (by norm_num)

/-- Sufficiency: an integer `a ≡ 1 (mod 2 ^ min n 3)` is a square in `ZMod (2 ^ n)`. -/
private theorem isSquare_of_modEq_one {a : ℤ} {n : ℕ}
    (h : a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3]) : IsSquare (a : ZMod (2 ^ n)) := by
  rcases lt_or_ge n 3 with hn | hn
  · rw [min_eq_left hn.le] at h
    have h1 : (a : ZMod (2 ^ n)) = 1 := by
      simpa using (ZMod.intCast_eq_intCast_iff a 1 (2 ^ n)).mpr (by exact_mod_cast h)
    rw [h1]
    exact ⟨1, by ring⟩
  · rw [min_eq_right hn, show (2 : ℤ) ^ 3 = 8 by norm_num] at h
    obtain ⟨y, hy⟩ := exists_sq_modEq_of_modEq_one_eight a h n
    refine ⟨(y : ZMod (2 ^ n)), ?_⟩
    have key := (ZMod.intCast_eq_intCast_iff a (y ^ 2) (2 ^ n)).mpr (by exact_mod_cast hy.symm)
    push_cast at key
    rw [key]
    ring

/-- An odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ min n 3)`. -/
theorem isSquare_two_pow_iff_of_odd (a : ℤ) (n : ℕ) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3] :=
  ⟨modEq_one_of_isSquare ha, isSquare_of_modEq_one⟩

/-- For `3 ≤ n`, an odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 8)`. -/
theorem isSquare_two_pow_iff_of_odd_three_le (a : ℤ) {n : ℕ} (hn : 3 ≤ n) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD 8] := by
  rw [isSquare_two_pow_iff_of_odd a n ha, min_eq_right hn, show (2 : ℤ) ^ 3 = 8 by norm_num]

/-- For `n ≤ 3`, an odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ n)`. -/
theorem isSquare_two_pow_iff_of_odd_le_three (a : ℤ) {n : ℕ} (hn : n ≤ 3) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD (2 : ℤ) ^ n] := by
  rw [isSquare_two_pow_iff_of_odd a n ha, min_eq_left hn]

end ZMod
