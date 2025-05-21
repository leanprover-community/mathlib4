/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Regular

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^iy^{n - 1 - i}=\frac{x^n-y^{n-m}x^m}{x-y}$
  in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

variable {R K : Type*}

open Finset MulOpposite

section Semiring

variable [Semiring R]

theorem geom_sum_succ {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

theorem geom_sum_succ' {x : R} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)

theorem geom_sum_zero (x : R) : ∑ i ∈ range 0, x ^ i = 0 :=
  rfl

theorem geom_sum_one (x : R) : ∑ i ∈ range 1, x ^ i = 1 := by simp [geom_sum_succ']

@[simp]
theorem geom_sum_two {x : R} : ∑ i ∈ range 2, x ^ i = x + 1 := by simp [geom_sum_succ']

@[simp]
theorem zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : R) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]

theorem one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : R) ^ i = n := by simp

theorem op_geom_sum (x : R) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp

@[simp]
theorem op_geom_sum₂ (x y : R) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  rw [mem_range, Nat.lt_iff_add_one_le] at j_in
  congr
  apply tsub_tsub_cancel_of_le
  exact le_tsub_of_add_le_right j_in

theorem geom_sum₂_with_one (x : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem Commute.geom_sum₂_mul_add {x y : R} (h : Commute x y) (n : ℕ) :
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

end Semiring

@[simp]
theorem neg_one_geom_sum [Ring R] {n : ℕ} :
    ∑ i ∈ range n, (-1 : R) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k hk =>
    simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, neg_add_cancel]

theorem geom_sum₂_self {R : Type*} [Semiring R] (x : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i ∈ Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun _ hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| Finset.mem_range.1 hi
    _ = #(range n) • x ^ (n - 1) := sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [CommSemiring R] (x y : R) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [Semiring R] (x : R) (n : ℕ) :
    (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

protected theorem Commute.geom_sum₂_mul [Ring R] {x y : R} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]

theorem Commute.mul_neg_geom_sum₂ [Ring R] {x y : R} (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

theorem Commute.mul_geom_sum₂ [Ring R] {x y : R} (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]

theorem geom_sum₂_mul [CommRing R] (x y : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n

theorem geom_sum₂_mul_of_ge [CommSemiring R] [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R]
    [ExistsAddOfLE R] [Sub R] [OrderedSub R] {x y : R} (hxy : y ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

theorem geom_sum₂_mul_of_le [CommSemiring R] [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R]
    [ExistsAddOfLE R] [Sub R] [OrderedSub R] {x y : R} (hxy : x ≤ y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  omega

theorem Commute.sub_dvd_pow_sub_pow [Ring R] {x y : R} (h : Commute x y) (n : ℕ) :
    x - y ∣ x ^ n - y ^ n :=
  Dvd.intro _ <| h.mul_geom_sum₂ _

theorem sub_dvd_pow_sub_pow [CommRing R] (x y : R) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  (Commute.all x y).sub_dvd_pow_sub_pow n

theorem nat_sub_dvd_pow_sub_pow (x y n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_gt y x with h | h
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)

theorem one_sub_dvd_one_sub_pow [Ring R] (x : R) (n : ℕ) :
    1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

theorem sub_one_dvd_pow_sub_one [Ring R] (x : R) (n : ℕ) :
    x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

lemma pow_one_sub_dvd_pow_mul_sub_one [Ring R] (x : R) (m n : ℕ) :
    ((x ^ m) - 1 : R) ∣ (x ^ (m * n) - 1) := by
  rw [npow_mul]
  exact sub_one_dvd_pow_sub_one (x := x ^ m) (n := n)

lemma nat_pow_one_sub_dvd_pow_mul_sub_one (x m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
  nth_rw 2 [← Nat.one_pow n]
  rw [Nat.pow_mul x m n]
  apply nat_sub_dvd_pow_sub_pow (x ^ m) 1

theorem Odd.add_dvd_pow_add_pow [CommRing R] (x y : R) {n : ℕ} (h : Odd n) :
    x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

theorem Odd.nat_add_dvd_pow_add_pow (x y : ℕ) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h

theorem geom_sum_mul [Ring R] (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

theorem geom_sum_mul_of_one_le [CommSemiring R] [PartialOrder R] [AddLeftReflectLE R]
    [AddLeftMono R] [ExistsAddOfLE R] [Sub R] [OrderedSub R] {x : R} (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  simpa using geom_sum₂_mul_of_ge hx n

theorem geom_sum_mul_of_le_one [CommSemiring R] [PartialOrder R] [AddLeftReflectLE R]
    [AddLeftMono R] [ExistsAddOfLE R] [Sub R] [OrderedSub R] {x : R} (hx : x ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  simpa using geom_sum₂_mul_of_le hx n

theorem mul_geom_sum [Ring R] (x : R) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by simpa using geom_sum_mul (op x) n

theorem geom_sum_mul_neg [Ring R] (x : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this

theorem mul_neg_geom_sum [Ring R] (x : R) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n

protected theorem Commute.geom_sum₂_comm [Semiring R] {x y : R} (n : ℕ)
    (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _

theorem geom_sum₂_comm [CommSemiring R] (x y : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n

protected theorem Commute.geom_sum₂ [DivisionRing K] {x y : K} (h' : Commute x y) (h : x ≠ y)
    (n : ℕ) : ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul, mul_div_cancel_right₀ _ this]

theorem geom₂_sum [Field K] {x y : K} (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

theorem geom₂_sum_of_gt [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [CanonicallyOrderedAdd K] [Sub K] [OrderedSub K]
    {x y : K} (h : y < x) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

theorem geom₂_sum_of_lt [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [CanonicallyOrderedAdd K] [Sub K] [OrderedSub K]
    {x y : K} (h : x < y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

theorem geom_sum_eq [DivisionRing K] {x : K} (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul, mul_div_cancel_right₀ _ this]

lemma geom_sum_of_one_lt {x : K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [CanonicallyOrderedAdd K] [Sub K] [OrderedSub K]
    (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

lemma geom_sum_of_lt_one {x : K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [CanonicallyOrderedAdd K] [Sub K] [OrderedSub K]
    (h : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (1 - x ^ n) / (1 - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

theorem geom_sum_lt {x : K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    [CanonicallyOrderedAdd K] [Sub K] [OrderedSub K]
    (h0 : x ≠ 0) (h1 : x < 1) (n : ℕ) : ∑ i ∈ range n, x ^ i < (1 - x)⁻¹ := by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1, div_lt_iff₀, inv_mul_cancel₀, tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

protected theorem Commute.mul_geom_sum₂_Ico [Ring R] {x y : R} (h : Commute x y) {m n : ℕ}
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

protected theorem Commute.geom_sum₂_succ_eq [Ring R] {x y : R} (h : Commute x y) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  omega

theorem geom_sum₂_succ_eq [CommRing R] (x y : R) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [CommRing R] (x y : R) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn

protected theorem Commute.geom_sum₂_Ico_mul [Ring R] {x y : R} (h : Commute x y) {m n : ℕ}
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

theorem geom_sum_Ico_mul [Ring R] (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [Ring R] (x : R) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

protected theorem Commute.geom_sum₂_Ico [DivisionRing K] {x y : K} (h : Commute x y) (hxy : x ≠ y)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel_right₀ _ this]

theorem geom_sum₂_Ico [Field K] {x y : K} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [DivisionRing K] {x : K} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

theorem geom_sum_Ico' [DivisionRing K] {x : K} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simp only [geom_sum_Ico hx hmn]
  convert neg_div_neg_eq (x ^ m - x ^ n) (1 - x) using 2 <;> abel

theorem geom_sum_Ico_le_of_lt_one [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : 0 ≤ x) (h'x : x < 1)
    {m n : ℕ} : ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le

theorem geom_sum_inv [DivisionRing K] {x : K} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    ∑ i ∈ range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ ≠ 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ', mul_inv_rev, ← mul_assoc, h, mul_assoc, mul_inv_cancel₀ hx0, mul_assoc,
        inv_mul_cancel₀ hx0]
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ h₃]
  simp [mul_add, add_mul, mul_inv_cancel₀ hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm,
    add_left_comm]
  rw [add_comm _ (-x), add_assoc, add_assoc _ _ 1]

variable {S : Type*}

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
theorem RingHom.map_geom_sum [Semiring R] [Semiring S] (x : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]

theorem RingHom.map_geom_sum₂ [Semiring R] [Semiring S] (x y : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]

/-! ### Geometric sum with `ℕ`-division -/


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) :
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) ≤ a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) =
    (∑ i ∈ range n, a / b ^ (i + 1) * b) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, pow_zero,
        Nat.div_one]
    _ ≤ (∑ i ∈ range n, a / b ^ i) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      gcongr with i hi
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ range n, a / b ^ i ≤ a * b / (b - 1) := by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ Ico 1 n, a / b ^ i ≤ a / (b - 1) := by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (zero_le_one' ℕ), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i ∈ Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i ∈ Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero, Nat.div_one]
    _ = ∑ i ∈ range n.succ, a / b ^ i := by
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (Nat.succ_pos _), sum_insert]
      · rfl
      exact fun h => zero_lt_one.not_ge (mem_Ico.1 h).1
    _ ≤ a * b / (b - 1) := Nat.geom_sum_le hb a _
    _ = (a * 1 + a * (b - 1)) / (b - 1) := by
      rw [← mul_add, add_tsub_cancel_of_le (one_le_two.trans hb)]
    _ = a + a / (b - 1) := by rw [mul_one, Nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]

section Order

variable {n : ℕ} {x : R}

theorem geom_sum_pos [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (hx : 0 ≤ x) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i :=
  sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

theorem geom_sum_pos_and_lt_one [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    (0 < ∑ i ∈ range n, x ^ i) ∧ ∑ i ∈ range n, x ^ i < 1 := by
  refine Nat.le_induction ?_ ?_ n (show 2 ≤ n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
  clear hn
  intro n _ ihn
  rw [geom_sum_succ, add_lt_iff_neg_right, ← neg_lt_iff_pos_add', neg_mul_eq_neg_mul]
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_left (neg_nonneg.2 hx.le) (neg_lt_iff_pos_add'.2 hx') ihn.2.le,
      mul_neg_of_neg_of_pos hx ihn.1⟩

theorem geom_sum_alternating_of_le_neg_one [Ring R] [PartialOrder R] [IsOrderedRing R]
    (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i ∈ range n, x ^ i) ≤ 0 else 1 ≤ ∑ i ∈ range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih with h
    · rw [if_neg (not_not_intro h), le_add_iff_nonneg_left]
      exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    · rw [if_pos h]
      refine (add_le_add_right ?_ _).trans hx
      simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0

theorem geom_sum_alternating_of_lt_neg_one [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then (∑ i ∈ range n, x ^ i) < 0 else 1 < ∑ i ∈ range n, x ^ i := by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 ≤ n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, gt_iff_lt, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  by_cases hn' : Even n
  · rw [if_pos hn'] at ihn
    rw [if_neg, lt_add_iff_pos_left]
    · exact mul_pos_of_neg_of_neg hx0 ihn
    · exact not_not_intro hn'
  · rw [if_neg hn'] at ihn
    rw [if_pos]
    swap
    · exact hn'
    have := add_lt_add_right (mul_lt_mul_of_neg_left ihn hx0) 1
    rw [mul_one] at this
    exact this.trans hx

theorem geom_sum_pos' [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (hx : 0 < x + 1) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp only [Nat.succ_ne_zero, Ne, not_false_iff])

theorem Odd.geom_sum_pos [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (h : Odd n) : 0 < ∑ i ∈ range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [h, if_false] at this
    exact zero_lt_one.trans this
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one]
  · exact geom_sum_pos' hx k.succ.succ_ne_zero

theorem geom_sum_pos_iff [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (hn : n ≠ 0) :
    (0 < ∑ i ∈ range n, x ^ i) ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

theorem geom_sum_ne_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (hx : x ≠ -1) (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i ≠ 0 := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne, eq_neg_iff_add_eq_zero, ← Ne] at hx
  obtain h | h := hx.lt_or_gt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
    split_ifs at this
    · exact this.ne
    · exact (zero_lt_one.trans this).ne'
  · exact (geom_sum_pos' h n.succ.succ_ne_zero).ne'

theorem geom_sum_eq_zero_iff_neg_one [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

theorem geom_sum_neg_iff [Ring R] [LinearOrder R] [IsStrictOrderedRing R] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), ← Nat.not_even_iff_odd, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]

end Order

variable {m n : ℕ} {s : Finset ℕ}

/-- Value of a geometric sum over the naturals. Note: see `geom_sum_mul_add` for a formulation
that avoids division and subtraction. -/
lemma Nat.geomSum_eq (hm : 2 ≤ m) (n : ℕ) :
    ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (one_le_two.trans hm), eq_comm] using geom_sum_mul_add (m - 1) n

/-- If all the elements of a finset of naturals are less than `n`, then the sum of their powers of
`m ≥ 2` is less than `m ^ n`. -/
lemma Nat.geomSum_lt (hm : 2 ≤ m) (hs : ∀ k ∈ s, k < n) : ∑ k ∈ s, m ^ k < m ^ n :=
  calc
    ∑ k ∈ s, m ^ k ≤ ∑ k ∈ range n, m ^ k := sum_le_sum_of_subset fun _ hk ↦
      mem_range.2 <| hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ ≤ m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (by positivity) zero_lt_one
