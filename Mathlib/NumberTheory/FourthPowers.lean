/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Tactic

/-!
# Fourth powers modulo small numbers

Residue facts for fourth powers of natural numbers: an even fourth power is
divisible by `16`, an odd fourth power is congruent to `1` modulo `16`, and
modulo `3` a fourth power is `0` or `1` according as the base is divisible
by `3` or not. These are the elementary congruence inputs to descent
arguments for fourth-power equations.
-/

public section

namespace Nat

/-- An even fourth power is divisible by `16`. -/
theorem sixteen_dvd_pow_four_of_even {n : ℕ} (h : Even n) :
    16 ∣ n ^ 4 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k + k = 2 * k := (two_mul k).symm
  rw [hk]
  have h4 : (2 * k) ^ 4 = 16 * k ^ 4 := by ring
  rw [h4]
  exact dvd_mul_right _ _

/-- An odd fourth power is congruent to `1` modulo `16`. -/
theorem pow_four_mod_sixteen_of_odd {n : ℕ} (h : Odd n) :
    n ^ 4 % 16 = 1 := by
  obtain ⟨k, rfl⟩ := h
  have hexp : (2 * k + 1) ^ 4 =
      16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * k * (k + 1) + 1 := by
    ring
  have heven : Even (k * (k + 1)) :=
    (Nat.even_or_odd k).elim
      (fun hk => hk.mul_right (k + 1))
      (fun hk => (hk.add_odd odd_one).mul_left k)
  obtain ⟨m, hm⟩ := heven
  have h8 : 8 * (k * (k + 1)) = 16 * m := by
    rw [hm]
    ring
  have hrw : (2 * k + 1) ^ 4 =
      16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2 + m) + 1 := by
    calc
      (2 * k + 1) ^ 4
        = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * k * (k + 1) + 1 := hexp
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * (k * (k + 1)) + 1 := by
          ring
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 16 * m + 1 := by
          rw [h8]
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2 + m) + 1 := by
          ring
  rw [hrw]
  have hmod : ∀ t : ℕ, (16 * t + 1) % 16 = 1 := fun t => by
    rw [Nat.add_mod, Nat.mul_mod_right]
  exact hmod _

/-- Modulo `3`, a fourth power is `0` if the base is divisible by `3`,
and `1` otherwise. -/
theorem pow_four_mod_three_cases {n : ℕ} :
    n ^ 4 % 3 = 0 ∧ n % 3 = 0 ∨
      n ^ 4 % 3 = 1 ∧ n % 3 ≠ 0 := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  interval_cases h : n % 3
  · refine Or.inl ⟨?_, rfl⟩
    rw [Nat.pow_mod, h]
  · refine Or.inr ⟨?_, by decide⟩
    rw [Nat.pow_mod, h]
  · refine Or.inr ⟨?_, by decide⟩
    rw [Nat.pow_mod, h]

/-- `3` divides a natural number if and only if it divides its fourth power. -/
theorem three_dvd_iff_pow_four {n : ℕ} :
    3 ∣ n ↔ 3 ∣ n ^ 4 := by
  constructor
  · intro h
    exact dvd_pow h (by decide)
  · intro h
    exact Nat.prime_three.dvd_of_dvd_pow h

/-- If `3` divides a sum of two fourth powers, it divides both bases. -/
theorem three_dvd_both_of_three_dvd_add_pow_four {a b : ℕ}
    (h : 3 ∣ a ^ 4 + b ^ 4) : 3 ∣ a ∧ 3 ∣ b := by
  have h0 : (a ^ 4 + b ^ 4) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have ha := pow_four_mod_three_cases (n := a)
  have hb := pow_four_mod_three_cases (n := b)
  rw [Nat.add_mod] at h0
  rcases ha with ⟨ha0, ha3⟩ | ⟨ha1, _han⟩
  · rcases hb with ⟨_hb0, hb3⟩ | ⟨hb1, _hbn⟩
    · exact ⟨Nat.dvd_iff_mod_eq_zero.mpr ha3,
        Nat.dvd_iff_mod_eq_zero.mpr hb3⟩
    · rw [ha0, hb1] at h0
      exact absurd h0 (by decide : ¬ (0 + 1) % 3 = 0)
  · rcases hb with ⟨hb0, _hb3⟩ | ⟨hb1, _hbn⟩
    · rw [ha1, hb0] at h0
      exact absurd h0 (by decide : ¬ (1 + 0) % 3 = 0)
    · rw [ha1, hb1] at h0
      exact absurd h0 (by decide : ¬ (1 + 1) % 3 = 0)

end Nat
