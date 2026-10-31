/-
Copyright (c) 2026 Arsen A. Khachatryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arsen A. Khachatryan
-/
module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic.LinearCombination

/-!
# Squares of odd integers in `ZMod (2 ^ n)`

For an odd integer `a`, `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ min n 3)`.

The nontrivial direction uses the decomposition `(ZMod (2 ^ n))ˣ = ⟨5⟩ · ⟨-1⟩`
(`ZMod.isComplement'_zpowers_unitFive_neg_one`): writing `a = 5 ^ k * (-1) ^ l`, the
condition `a ≡ 1 (mod 8)` forces `k` and `l` to be even.

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

/-- Sufficiency for `3 ≤ n`, via `(ZMod (2 ^ n))ˣ = ⟨5⟩ · ⟨-1⟩`: if `a = 5 ^ k * (-1) ^ l` and
`a ≡ 1 (mod 8)`, then `k` and `l` are even, so `a` is a square. -/
private theorem isSquare_of_three_le {a : ℤ} {n : ℕ} (hn : 3 ≤ n) (ha : Odd a)
    (h : a ≡ 1 [ZMOD (2 : ℤ) ^ 3]) : IsSquare (a : ZMod (2 ^ n)) := by
  have : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  have hu : IsUnit (a : ZMod (2 ^ n)) := by
    rw [ZMod.isUnit_intCast_iff_isCoprime]
    obtain ⟨j, rfl⟩ := ha
    push_cast
    exact IsCoprime.pow_left ⟨-j, 1, by ring⟩
  have hmem : hu.unit ∈ Subgroup.zpowers unitFive ⊔ Subgroup.zpowers (-1) := by
    rw [(isComplement'_zpowers_unitFive_neg_one n).sup_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
  obtain ⟨l, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have hval : (a : ZMod (2 ^ n)) = 5 ^ k * (-1) ^ l := by
    rw [← hu.unit_spec, ← hyz]
    simp
  -- Reduce modulo `8`, where `5 ^ 2 = 1`, to see that `k` and `l` are even.
  have h8 := congrArg (ZMod.castHom (Nat.pow_dvd_pow 2 hn) (ZMod (2 ^ 3))) hval
  rw [map_intCast, (ZMod.intCast_eq_intCast_iff a 1 (2 ^ 3)).mpr (by exact_mod_cast h)] at h8
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat, Int.cast_one] at h8
  have h5 : (5 : ZMod (2 ^ 3)) ^ k = 5 ^ (k % 2) := by
    conv_lhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul,
      show (5 : ZMod (2 ^ 3)) ^ 2 = 1 by decide, one_pow, mul_one]
  rw [h5, neg_one_pow_eq_pow_mod_two] at h8
  have key : ∀ r < 2, ∀ s < 2, (1 : ZMod (2 ^ 3)) = 5 ^ r * (-1) ^ s → r = 0 ∧ s = 0 := by
    decide
  obtain ⟨hk, hl⟩ := key _ (Nat.mod_lt _ two_pos) _ (Nat.mod_lt _ two_pos) h8
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hk
  obtain ⟨p, rfl⟩ := Nat.dvd_of_mod_eq_zero hl
  exact ⟨5 ^ q * (-1) ^ p, by rw [hval]; ring⟩

/-- Sufficiency: an odd integer `a ≡ 1 (mod 2 ^ min n 3)` is a square in `ZMod (2 ^ n)`. -/
private theorem isSquare_of_modEq_one {a : ℤ} {n : ℕ} (ha : Odd a)
    (h : a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3]) : IsSquare (a : ZMod (2 ^ n)) := by
  rcases lt_or_ge n 3 with hn | hn
  · rw [min_eq_left hn.le] at h
    have h1 : (a : ZMod (2 ^ n)) = 1 := by
      simpa using (ZMod.intCast_eq_intCast_iff a 1 (2 ^ n)).mpr (by exact_mod_cast h)
    rw [h1]
    exact ⟨1, by ring⟩
  · rw [min_eq_right hn] at h
    exact isSquare_of_three_le hn ha h

/-- An odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ min n 3)`. -/
theorem isSquare_two_pow_iff_of_odd (a : ℤ) (n : ℕ) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3] :=
  ⟨modEq_one_of_isSquare ha, isSquare_of_modEq_one ha⟩

/-- For `3 ≤ n`, an odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 8)`. -/
theorem isSquare_two_pow_iff_of_odd_three_le (a : ℤ) {n : ℕ} (hn : 3 ≤ n) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD 8] := by
  rw [isSquare_two_pow_iff_of_odd a n ha, min_eq_right hn, show (2 : ℤ) ^ 3 = 8 by norm_num]

/-- For `n ≤ 3`, an odd integer `a` is a square in `ZMod (2 ^ n)` iff `a ≡ 1 (mod 2 ^ n)`. -/
theorem isSquare_two_pow_iff_of_odd_le_three (a : ℤ) {n : ℕ} (hn : n ≤ 3) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD (2 : ℤ) ^ n] := by
  rw [isSquare_two_pow_iff_of_odd a n ha, min_eq_left hn]

end ZMod
