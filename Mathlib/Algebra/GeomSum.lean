/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Regular

#align_import algebra.geom_sum from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

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

-- Porting note: corrected type in the description of `geom_sum₂_Ico` (in the doc string only).

universe u

variable {α : Type u}

open Finset MulOpposite

section Semiring

variable [Semiring α]

theorem geom_sum_succ {x : α} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]
#align geom_sum_succ geom_sum_succ

theorem geom_sum_succ' {x : α} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)
#align geom_sum_succ' geom_sum_succ'

theorem geom_sum_zero (x : α) : ∑ i ∈ range 0, x ^ i = 0 :=
  rfl
#align geom_sum_zero geom_sum_zero

theorem geom_sum_one (x : α) : ∑ i ∈ range 1, x ^ i = 1 := by simp [geom_sum_succ']
#align geom_sum_one geom_sum_one

@[simp]
theorem geom_sum_two {x : α} : ∑ i ∈ range 2, x ^ i = x + 1 := by simp [geom_sum_succ']
#align geom_sum_two geom_sum_two

@[simp]
theorem zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : α) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]
#align zero_geom_sum zero_geom_sum

theorem one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : α) ^ i = n := by simp
#align one_geom_sum one_geom_sum

-- porting note (#10618): simp can prove this
-- @[simp]
theorem op_geom_sum (x : α) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp
#align op_geom_sum op_geom_sum

-- Porting note: linter suggested to change left hand side
@[simp]
theorem op_geom_sum₂ (x y : α) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j j_in => ?_
  rw [mem_range, Nat.lt_iff_add_one_le] at j_in
  congr
  apply tsub_tsub_cancel_of_le
  exact le_tsub_of_add_le_right j_in
#align op_geom_sum₂ op_geom_sum₂

theorem geom_sum₂_with_one (x : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]
#align geom_sum₂_with_one geom_sum₂_with_one

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem Commute.geom_sum₂_mul_add {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f :  ℕ → ℕ → α := fun m i : ℕ => (x + y) ^ i * y ^ (m - 1 - i)
  -- Porting note: adding `hf` here, because below in two places `dsimp [f]` didn't work
  have hf : ∀ m i : ℕ, f m i = (x + y) ^ i * y ^ (m - 1 - i) := by
    simp only [ge_iff_le, tsub_le_iff_right, forall_const]
  change (∑ i ∈ range n, (f n) i) * x + y ^ n = (x + y) ^ n
  induction' n with n ih
  · rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
  · have f_last : f (n + 1) n = (x + y) ^ n := by
      rw [hf, ← tsub_add_eq_tsub_tsub, Nat.add_comm, tsub_self, pow_zero, mul_one]
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i := fun i hi => by
      rw [hf]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ' y (n - 1 - i)]
      congr 2
      rw [add_tsub_cancel_right, ← tsub_add_eq_tsub_tsub, add_comm 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_comm (i + 1)] at this
      rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc, add_tsub_cancel_right]
    rw [pow_succ' (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc]
    rw [(((Commute.refl x).add_right h).pow_right n).eq]
    congr 1
    rw [sum_congr rfl f_succ, ← mul_sum, pow_succ' y, mul_assoc, ← mul_add y, ih]
#align commute.geom_sum₂_mul_add Commute.geom_sum₂_mul_add

end Semiring

@[simp]
theorem neg_one_geom_sum [Ring α] {n : ℕ} :
    ∑ i ∈ range n, (-1 : α) ^ i = if Even n then 0 else 1 := by
  induction' n with k hk
  · simp
  · simp only [geom_sum_succ', Nat.even_add_one, hk]
    split_ifs with h
    · rw [h.neg_one_pow, add_zero]
    · rw [(Nat.odd_iff_not_even.2 h).neg_one_pow, neg_add_self]
#align neg_one_geom_sum neg_one_geom_sum

theorem geom_sum₂_self {α : Type*} [CommRing α] (x : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i ∈ Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i ∈ Finset.range n, x ^ (i + (n - 1 - i)) := by
      simp_rw [← pow_add]
    _ = ∑ _i ∈ Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun i hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_sub_one_of_lt <| Finset.mem_range.1 hi
    _ = (Finset.range n).card • x ^ (n - 1) := Finset.sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]
#align geom_sum₂_self geom_sum₂_self

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [CommSemiring α] (x y : α) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n
#align geom_sum₂_mul_add geom_sum₂_mul_add

theorem geom_sum_mul_add [Semiring α] (x : α) (n : ℕ) :
    (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this
#align geom_sum_mul_add geom_sum_mul_add

protected theorem Commute.geom_sum₂_mul [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]
#align commute.geom_sum₂_mul Commute.geom_sum₂_mul

theorem Commute.mul_neg_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]
#align commute.mul_neg_geom_sum₂ Commute.mul_neg_geom_sum₂

theorem Commute.mul_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]
#align commute.mul_geom_sum₂ Commute.mul_geom_sum₂

theorem geom_sum₂_mul [CommRing α] (x y : α) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n
#align geom_sum₂_mul geom_sum₂_mul

theorem Commute.sub_dvd_pow_sub_pow [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    x - y ∣ x ^ n - y ^ n :=
  Dvd.intro _ <| h.mul_geom_sum₂ _

theorem sub_dvd_pow_sub_pow [CommRing α] (x y : α) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  (Commute.all x y).sub_dvd_pow_sub_pow n
#align sub_dvd_pow_sub_pow sub_dvd_pow_sub_pow

theorem one_sub_dvd_one_sub_pow [Ring α] (x : α) (n : ℕ) :
    1 - x ∣ 1 - x ^ n := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_left x).sub_dvd_pow_sub_pow n

theorem sub_one_dvd_pow_sub_one [Ring α] (x : α) (n : ℕ) :
    x - 1 ∣ x ^ n - 1 := by
  conv_rhs => rw [← one_pow n]
  exact (Commute.one_right x).sub_dvd_pow_sub_pow n

theorem nat_sub_dvd_pow_sub_pow (x y n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_lt y x with h | h
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)
#align nat_sub_dvd_pow_sub_pow nat_sub_dvd_pow_sub_pow

theorem Odd.add_dvd_pow_add_pow [CommRing α] (x y : α) {n : ℕ} (h : Odd n) :
    x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁
#align odd.add_dvd_pow_add_pow Odd.add_dvd_pow_add_pow

theorem Odd.nat_add_dvd_pow_add_pow (x y : ℕ) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h
#align odd.nat_add_dvd_pow_add_pow Odd.nat_add_dvd_pow_add_pow

theorem geom_sum_mul [Ring α] (x : α) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this
#align geom_sum_mul geom_sum_mul

theorem mul_geom_sum [Ring α] (x : α) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by simpa using geom_sum_mul (op x) n
#align mul_geom_sum mul_geom_sum

theorem geom_sum_mul_neg [Ring α] (x : α) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  rw [neg_sub, ← mul_neg, neg_sub] at this
  exact this
#align geom_sum_mul_neg geom_sum_mul_neg

theorem mul_neg_geom_sum [Ring α] (x : α) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n
#align mul_neg_geom_sum mul_neg_geom_sum

protected theorem Commute.geom_sum₂_comm {α : Type u} [Semiring α] {x y : α} (n : ℕ)
    (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _
#align commute.geom_sum₂_comm Commute.geom_sum₂_comm

theorem geom_sum₂_comm {α : Type u} [CommSemiring α] (x y : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n
#align geom_sum₂_comm geom_sum₂_comm

protected theorem Commute.geom_sum₂ [DivisionRing α] {x y : α} (h' : Commute x y) (h : x ≠ y)
    (n : ℕ) : ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h'.geom_sum₂_mul, mul_div_cancel_right₀ _ this]
#align commute.geom_sum₂ Commute.geom_sum₂

theorem geom₂_sum [Field α] {x y : α} (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n
#align geom₂_sum geom₂_sum

theorem geom_sum_eq [DivisionRing α] {x : α} (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul, mul_div_cancel_right₀ _ this]
#align geom_sum_eq geom_sum_eq

protected theorem Commute.mul_geom_sum₂_Ico [Ring α] {x y : α} (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k ∈ range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k ∈ range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range, Nat.lt_iff_add_one_le, add_comm] at j_in
    have h' : n - m + (m - (1 + j)) = n - (1 + j) := tsub_add_tsub_cancel hmn j_in
    rw [← tsub_add_eq_tsub_tsub m, h', ← tsub_add_eq_tsub_tsub]
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]
#align commute.mul_geom_sum₂_Ico Commute.mul_geom_sum₂_Ico

protected theorem Commute.geom_sum₂_succ_eq {α : Type u} [Ring α] {x y : α} (h : Commute x y)
    {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  cases' n with n
  · exact absurd (List.mem_range.mp hi) i.not_lt_zero
  · rw [tsub_add_eq_add_tsub (Nat.le_sub_one_of_lt (List.mem_range.mp hi)),
      tsub_add_cancel_of_le (Nat.succ_le_iff.mpr n.succ_pos)]
#align commute.geom_sum₂_succ_eq Commute.geom_sum₂_succ_eq

theorem geom_sum₂_succ_eq {α : Type u} [CommRing α] (x y : α) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq
#align geom_sum₂_succ_eq geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [CommRing α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn
#align mul_geom_sum₂_Ico mul_geom_sum₂_Ico

protected theorem Commute.geom_sum₂_Ico_mul [Ring α] {x y : α} (h : Commute x y) {m n : ℕ}
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
  -- Porting note: gives deterministic timeout without this intermediate `have`
  convert (Commute.op h).mul_geom_sum₂_Ico hmn
#align commute.geom_sum₂_Ico_mul Commute.geom_sum₂_Ico_mul

theorem geom_sum_Ico_mul [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]
#align geom_sum_Ico_mul geom_sum_Ico_mul

theorem geom_sum_Ico_mul_neg [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]
#align geom_sum_Ico_mul_neg geom_sum_Ico_mul_neg

protected theorem Commute.geom_sum₂_Ico [DivisionRing α] {x y : α} (h : Commute x y) (hxy : x ≠ y)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel_right₀ _ this]
#align commute.geom_sum₂_Ico Commute.geom_sum₂_Ico

theorem geom_sum₂_Ico [Field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn
#align geom_sum₂_Ico geom_sum₂_Ico

theorem geom_sum_Ico [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]
#align geom_sum_Ico geom_sum_Ico

theorem geom_sum_Ico' [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simp only [geom_sum_Ico hx hmn]
  convert neg_div_neg_eq (x ^ m - x ^ n) (1 - x) using 2 <;> abel
#align geom_sum_Ico' geom_sum_Ico'

theorem geom_sum_Ico_le_of_lt_one [LinearOrderedField α] {x : α} (hx : 0 ≤ x) (h'x : x < 1)
    {m n : ℕ} : ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_lt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le
#align geom_sum_Ico_le_of_lt_one geom_sum_Ico_le_of_lt_one

theorem geom_sum_inv [DivisionRing α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    ∑ i ∈ range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ ≠ 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ', mul_inv_rev, ← mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc,
        inv_mul_cancel hx0]
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel h₃]
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm,
    add_left_comm]
  rw [add_comm _ (-x), add_assoc, add_assoc _ _ 1]
#align geom_sum_inv geom_sum_inv

variable {β : Type*}

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
theorem RingHom.map_geom_sum [Semiring α] [Semiring β] (x : α) (n : ℕ) (f : α →+* β) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]
#align ring_hom.map_geom_sum RingHom.map_geom_sum

theorem RingHom.map_geom_sum₂ [Semiring α] [Semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]
#align ring_hom.map_geom_sum₂ RingHom.map_geom_sum₂

/-! ### Geometric sum with `ℕ`-division -/


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) :
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) ≤ a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) =
    (∑ i ∈ range n, a / b ^ (i + 1) * b) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, pow_zero,
        Nat.div_one]
    _ ≤ (∑ i ∈ range n, a / b ^ i) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      refine tsub_le_tsub_right (add_le_add_right (sum_le_sum fun i _ => ?_) _) _
      rw [pow_succ', mul_comm b]
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _
#align nat.pred_mul_geom_sum_le Nat.pred_mul_geom_sum_le

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ range n, a / b ^ i ≤ a * b / (b - 1) := by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  cases' n with n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self
#align nat.geom_sum_le Nat.geom_sum_le

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ Ico 1 n, a / b ^ i ≤ a / (b - 1) := by
  cases' n with n
  · rw [Ico_eq_empty_of_le (zero_le_one' ℕ), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i ∈ Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i ∈ Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero, Nat.div_one]
    _ = ∑ i ∈ range n.succ, a / b ^ i := by
      rw [range_eq_Ico, ← Nat.Ico_insert_succ_left (Nat.succ_pos _), sum_insert]
      exact fun h => zero_lt_one.not_le (mem_Ico.1 h).1
    _ ≤ a * b / (b - 1) := Nat.geom_sum_le hb a _
    _ = (a * 1 + a * (b - 1)) / (b - 1) := by
      rw [← mul_add, add_tsub_cancel_of_le (one_le_two.trans hb)]
    _ = a + a / (b - 1) := by rw [mul_one, Nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]
#align nat.geom_sum_Ico_le Nat.geom_sum_Ico_le

section Order

variable {n : ℕ} {x : α}

theorem geom_sum_pos [StrictOrderedSemiring α] (hx : 0 ≤ x) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i :=
  sum_pos' (fun k _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩
#align geom_sum_pos geom_sum_pos

theorem geom_sum_pos_and_lt_one [StrictOrderedRing α] (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
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
#align geom_sum_pos_and_lt_one geom_sum_pos_and_lt_one

theorem geom_sum_alternating_of_le_neg_one [StrictOrderedRing α] (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i ∈ range n, x ^ i) ≤ 0 else 1 ≤ ∑ i ∈ range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction' n with n ih
  · simp only [Nat.zero_eq, range_zero, sum_empty, le_refl, ite_true, even_zero]
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ih with h
  · rw [if_neg (not_not_intro h), le_add_iff_nonneg_left]
    exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
  · rw [if_pos h]
    refine (add_le_add_right ?_ _).trans hx
    simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0
#align geom_sum_alternating_of_le_neg_one geom_sum_alternating_of_le_neg_one

theorem geom_sum_alternating_of_lt_neg_one [StrictOrderedRing α] (hx : x + 1 < 0) (hn : 1 < n) :
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
#align geom_sum_alternating_of_lt_neg_one geom_sum_alternating_of_lt_neg_one

theorem geom_sum_pos' [LinearOrderedRing α] (hx : 0 < x + 1) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_le x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp only [Nat.succ_ne_zero, Ne, not_false_iff])
#align geom_sum_pos' geom_sum_pos'

theorem Odd.geom_sum_pos [LinearOrderedRing α] (h : Odd n) : 0 < ∑ i ∈ range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact ((show ¬Odd 0 by decide) h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [Nat.odd_iff_not_even] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [h, if_false] at this
    exact zero_lt_one.trans this
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one]
  · exact geom_sum_pos' hx k.succ.succ_ne_zero
#align odd.geom_sum_pos Odd.geom_sum_pos

theorem geom_sum_pos_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    (0 < ∑ i ∈ range n, x ^ i) ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, ← Nat.even_iff_not_odd]
    refine fun hn hx => h.not_le ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn
#align geom_sum_pos_iff geom_sum_pos_iff

theorem geom_sum_ne_zero [LinearOrderedRing α] (hx : x ≠ -1) (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i ≠ 0 := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne, eq_neg_iff_add_eq_zero, ← Ne] at hx
  obtain h | h := hx.lt_or_lt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
    split_ifs at this
    · exact this.ne
    · exact (zero_lt_one.trans this).ne'
  · exact (geom_sum_pos' h n.succ.succ_ne_zero).ne'
#align geom_sum_ne_zero geom_sum_ne_zero

theorem geom_sum_eq_zero_iff_neg_one [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  cases' hx with hx hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn
#align geom_sum_eq_zero_iff_neg_one geom_sum_eq_zero_iff_neg_one

theorem geom_sum_neg_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), Nat.odd_iff_not_even, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]
#align geom_sum_neg_iff geom_sum_neg_iff

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
    ∑ k ∈ s, m ^ k ≤ ∑ k ∈ range n, m ^ k := sum_le_sum_of_subset fun k hk ↦
      mem_range.2 <| hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ ≤ m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (by positivity) zero_lt_one
