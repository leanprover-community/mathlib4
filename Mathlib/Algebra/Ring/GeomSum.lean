/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Opposite

/-!
# Partial sums of geometric series in a ring

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

assert_not_exists Field IsOrderedRing

open Finset MulOpposite

variable {R S : Type*}

section Semiring
variable [Semiring R] [Semiring S] {x y : R}

lemma geom_sum_succ {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

lemma geom_sum_succ' {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)

lemma geom_sum_zero (x : R) : ∑ i ∈ range 0, x ^ i = 0 :=
  rfl

lemma geom_sum_one (x : R) : ∑ i ∈ range 1, x ^ i = 1 := by simp

@[simp]
lemma geom_sum_two {x : R} : ∑ i ∈ range 2, x ^ i = x + 1 := by simp [geom_sum_succ']

@[simp]
lemma zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : R) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]

lemma one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : R) ^ i = n := by simp

lemma op_geom_sum (x : R) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp

@[simp]
lemma op_geom_sum₂ (x y : R) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  grind

lemma geom_sum₂_with_one (x : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected lemma Commute.geom_sum₂_mul_add {x y : R} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f :  ℕ → ℕ → R := fun m i : ℕ => (x + y) ^ i * y ^ (m - 1 - i)
  change (∑ i ∈ range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction n with
  | zero => rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  | succ n ih =>
    have f_last : f (n + 1) n = (x + y) ^ n := by
      dsimp only [f]
      rw [← tsub_add_eq_tsub_tsub, Nat.add_comm, tsub_self, pow_zero, mul_one]
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i := fun i hi => by
      dsimp only [f]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ' y (n - 1 - i), add_tsub_cancel_right,
        ← tsub_add_eq_tsub_tsub, add_comm 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_comm (i + 1)] at this
      rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc, add_tsub_cancel_right]
    rw [pow_succ' (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc,
      (((Commute.refl x).add_right h).pow_right n).eq, sum_congr rfl f_succ, ← mul_sum,
      pow_succ' y, mul_assoc, ← mul_add y, ih]

lemma geom_sum₂_self (x : R) (n : ℕ) : ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i ∈ Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| Finset.mem_range.1 hi
    _ = #(range n) • x ^ (n - 1) := sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]

lemma geom_sum_mul_add (x : R) (n : ℕ) : (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

protected lemma Commute.geom_sum₂_comm (n : ℕ) (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
lemma RingHom.map_geom_sum (x : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]

lemma RingHom.map_geom_sum₂ (x y : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]

end Semiring

section CommSemiring
variable [CommSemiring R]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
lemma geom_sum₂_mul_add (x y : R) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

lemma geom_sum₂_comm (x y : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

lemma geom_sum₂_mul_of_ge (hxy : y ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

lemma geom_sum₂_mul_of_le (hxy : x ≤ y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  omega

lemma geom_sum_mul_of_one_le (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by simpa using geom_sum₂_mul_of_ge hx n

lemma geom_sum_mul_of_le_one (hx : x ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by simpa using geom_sum₂_mul_of_le hx n

end CommSemiring

section Ring
variable [Ring R] {x y : R}

@[simp]
lemma neg_one_geom_sum {n : ℕ} : ∑ i ∈ range n, (-1 : R) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

protected lemma Commute.geom_sum₂_mul (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]

lemma Commute.mul_neg_geom_sum₂ (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

lemma Commute.mul_geom_sum₂ (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]

lemma Commute.sub_dvd_pow_sub_pow (h : Commute x y) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  Dvd.intro _ <| h.mul_geom_sum₂ _

lemma one_sub_dvd_one_sub_pow (x : R) (n : ℕ) : 1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

lemma sub_one_dvd_pow_sub_one (x : R) (n : ℕ) : x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

lemma pow_one_sub_dvd_pow_mul_sub_one (x : R) (m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  rw [pow_mul]; exact sub_one_dvd_pow_sub_one (x ^ m) n

lemma geom_sum_mul (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

lemma mul_geom_sum (x : R) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by simpa using geom_sum_mul (op x) n

lemma geom_sum_mul_neg (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this

lemma mul_neg_geom_sum (x : R) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n

protected lemma Commute.mul_geom_sum₂_Ico (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k ∈ range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k ∈ range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    omega
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]

protected lemma Commute.geom_sum₂_succ_eq (h : Commute x y) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  omega

protected lemma Commute.geom_sum₂_Ico_mul (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  simp only [op_sub, op_mul, op_pow, op_sum]
  have : (∑ k ∈ Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k ∈ Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine sum_congr rfl fun k _ => ?_
    have hp := Commute.pow_pow (Commute.op h.symm) (n - 1 - k) k
    simpa [Commute, SemiconjBy] using hp
  simp only [this]
  convert (Commute.op h).mul_geom_sum₂_Ico hmn

lemma geom_sum_Ico_mul (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

lemma geom_sum_Ico_mul_neg (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

end Ring

section CommRing
variable [CommRing R]

lemma geom_sum₂_mul (x y : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n

lemma sub_dvd_pow_sub_pow (x y : R) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  (Commute.all x y).sub_dvd_pow_sub_pow n

lemma Odd.add_dvd_pow_add_pow (x y : R) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

lemma geom_sum₂_succ_eq (x y : R) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) = x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq

lemma mul_geom_sum₂_Ico (x y : R) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

end CommRing

lemma nat_sub_dvd_pow_sub_pow (x y n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_gt y x with h | h
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)

lemma nat_pow_one_sub_dvd_pow_mul_sub_one (x m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  nth_rw 2 [← Nat.one_pow n]
  rw [Nat.pow_mul x m n]
  apply nat_sub_dvd_pow_sub_pow (x ^ m) 1

lemma Odd.nat_add_dvd_pow_add_pow (x y : ℕ) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h

/-- Value of a geometric sum over the naturals. Note: see `geom_sum_mul_add` for a formulation
that avoids division and subtraction. -/
lemma Nat.geomSum_eq {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (by omega : 1 ≤ m), eq_comm] using geom_sum_mul_add (m - 1) n
