/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Lemmas about divisibility in rings

## Main results:
* `dvd_smul_of_dvd`: stating that `x ∣ y → x ∣ m • y` for any scalar `m`.
* `Commute.pow_dvd_add_pow_of_pow_eq_zero_right`: stating that if `y` is nilpotent then
  `x ^ m ∣ (x + y) ^ p` for sufficiently large `p` (together with many variations for convenience).
-/

variable {R : Type*}

lemma dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
    (m : M) (h : x ∣ y) : x ∣ m • y :=
  let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩

lemma dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : ℕ) (h : x ∣ y) : x ∣ n • y :=
  dvd_smul_of_dvd n h

lemma dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : ℤ) (h : x ∣ y) : x ∣ z • y :=
  dvd_smul_of_dvd z h

namespace Commute

variable {x y : R} {n m p : ℕ}

section Semiring

variable [Semiring R]

lemma pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p := by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij ↦ ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m ≤ i) | (hi : i + 1 ≤ m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by cutsat : n ≤ j) hy]

lemma pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p :=
  add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

end Semiring

section Ring

variable [Ring R]

lemma pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← sub_add_cancel y x]
  apply (h_comm.symm.sub_left rfl).pow_dvd_add_pow_of_pow_eq_zero_left hp _
  rw [← neg_sub x y, neg_pow, h, mul_zero]

lemma pow_dvd_pow_of_add_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← neg_neg y, neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa

lemma pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p :=
  (sub_right rfl h_comm).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

lemma pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p := by
  rw [← neg_sub y x, neg_pow']
  apply dvd_mul_of_dvd_left
  exact h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right hp hx

lemma add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p :=
  (h_comm.add_left rfl).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

lemma add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p :=
  add_comm x y ▸ h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right hp hy

end Ring

end Commute
section CommRing

variable [CommRing R]

lemma dvd_mul_sub_mul_mul_left_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * x := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  grind

lemma dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y :=
  (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))

lemma dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [IsDomain R] [GCDMonoid R]
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y := by
  rw [← (gcd_mul_left' (a*d - b*c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

end CommRing

section misc

variable [Ring R] [LinearOrder R] {x y : R}

@[simp]
theorem associated_abs_left_iff :
    Associated |x| y ↔ Associated x y := by
  obtain h | h := abs_choice x <;>
  simp [h]

@[simp]
theorem associated_abs_right_iff :
    Associated x |y| ↔ Associated x y := by
  rw [Associated.comm, associated_abs_left_iff, Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

end misc
