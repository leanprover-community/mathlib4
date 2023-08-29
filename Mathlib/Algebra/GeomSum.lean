/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel
import Mathlib.Data.Nat.Parity

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

--porting note: corrected type in the description of `geom_sum₂_Ico` (in the doc string only).

universe u

variable {α : Type u}

open Finset MulOpposite

open BigOperators

section Semiring

variable [Semiring α]

theorem geom_sum_succ {x : α} {n : ℕ} :
    ∑ i in range (n + 1), x ^ i = (x * ∑ i in range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ, sum_range_succ', pow_zero]
  -- 🎉 no goals
#align geom_sum_succ geom_sum_succ

theorem geom_sum_succ' {x : α} {n : ℕ} :
    ∑ i in range (n + 1), x ^ i = x ^ n + ∑ i in range n, x ^ i :=
  (sum_range_succ _ _).trans (add_comm _ _)
#align geom_sum_succ' geom_sum_succ'

theorem geom_sum_zero (x : α) : ∑ i in range 0, x ^ i = 0 :=
  rfl
#align geom_sum_zero geom_sum_zero

theorem geom_sum_one (x : α) : ∑ i in range 1, x ^ i = 1 := by simp [geom_sum_succ']
                                                               -- 🎉 no goals
#align geom_sum_one geom_sum_one

@[simp]
theorem geom_sum_two {x : α} : ∑ i in range 2, x ^ i = x + 1 := by simp [geom_sum_succ']
                                                                   -- 🎉 no goals
#align geom_sum_two geom_sum_two

@[simp]
theorem zero_geom_sum : ∀ {n}, ∑ i in range n, (0 : α) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
            -- 🎉 no goals
  | 1 => by simp
            -- 🎉 no goals
  | n + 2 => by
    rw [geom_sum_succ']
    -- ⊢ 0 ^ (n + 1) + ∑ i in range (n + 1), 0 ^ i = if n + 2 = 0 then 0 else 1
    simp [zero_geom_sum]
    -- 🎉 no goals
#align zero_geom_sum zero_geom_sum

theorem one_geom_sum (n : ℕ) : ∑ i in range n, (1 : α) ^ i = n := by simp
                                                                     -- 🎉 no goals
#align one_geom_sum one_geom_sum

-- porting note: simp can prove this
-- @[simp]
theorem op_geom_sum (x : α) (n : ℕ) : op (∑ i in range n, x ^ i) = ∑ i in range n, op x ^ i := by
  simp
  -- 🎉 no goals
#align op_geom_sum op_geom_sum

--porting note: linter suggested to change left hand side
@[simp]
theorem op_geom_sum₂ (x y : α) (n : ℕ) : ∑ i in range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i in range n, op y ^ i * op x ^ (n - 1 - i):= by
  rw [← sum_range_reflect]
  -- ⊢ ∑ j in range n, op y ^ (n - 1 - (n - 1 - j)) * op x ^ (n - 1 - j) = ∑ i in r …
  refine' sum_congr rfl fun j j_in => _
  -- ⊢ op y ^ (n - 1 - (n - 1 - j)) * op x ^ (n - 1 - j) = op y ^ j * op x ^ (n - 1 …
  rw [mem_range, Nat.lt_iff_add_one_le] at j_in
  -- ⊢ op y ^ (n - 1 - (n - 1 - j)) * op x ^ (n - 1 - j) = op y ^ j * op x ^ (n - 1 …
  congr
  -- ⊢ n - 1 - (n - 1 - j) = j
  apply tsub_tsub_cancel_of_le
  -- ⊢ j ≤ n - 1
  exact le_tsub_of_add_le_right j_in
  -- 🎉 no goals
#align op_geom_sum₂ op_geom_sum₂

theorem geom_sum₂_with_one (x : α) (n : ℕ) :
    ∑ i in range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i in range n, x ^ i :=
  sum_congr rfl fun i _ => by rw [one_pow, mul_one]
                              -- 🎉 no goals
#align geom_sum₂_with_one geom_sum₂_with_one

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem Commute.geom_sum₂_mul_add {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := by
  let f :  ℕ → ℕ → α := fun m i : ℕ => (x + y) ^ i * y ^ (m - 1 - i)
  -- ⊢ (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n
  -- porting note: adding `hf` here, because below in two places `dsimp [f]` didn't work
  have hf : ∀ m i : ℕ, f m i = (x + y) ^ i * y ^ (m - 1 - i) := by
    simp only [ge_iff_le, tsub_le_iff_right, forall_const]
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n
  -- ⊢ (∑ i in range n, f n i) * x + y ^ n = (x + y) ^ n
  induction' n with n ih
  -- ⊢ (∑ i in range Nat.zero, f Nat.zero i) * x + y ^ Nat.zero = (x + y) ^ Nat.zero
  · rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero]
    -- 🎉 no goals
  · have f_last : f (n + 1) n = (x + y) ^ n := by
      rw [hf, ← tsub_add_eq_tsub_tsub, Nat.add_comm, tsub_self, pow_zero, mul_one]
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i := fun i hi => by
      rw [hf]
      have : Commute y ((x + y) ^ i) := (h.symm.add_right (Commute.refl y)).pow_right i
      rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ y (n - 1 - i)]
      congr 2
      rw [add_tsub_cancel_right, ← tsub_add_eq_tsub_tsub, add_comm 1 i]
      have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi)
      rw [add_comm (i + 1)] at this
      rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc, add_tsub_cancel_right]
    rw [pow_succ (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc]
    -- ⊢ (x + y) ^ n * x + ((∑ x in range n, f (Nat.succ n) x) * x + y ^ Nat.succ n)  …
    rw [(((Commute.refl x).add_right h).pow_right n).eq]
    -- ⊢ (x + y) ^ n * x + ((∑ x in range n, f (Nat.succ n) x) * x + y ^ Nat.succ n)  …
    congr 1
    -- ⊢ (∑ x in range n, f (Nat.succ n) x) * x + y ^ Nat.succ n = y * (x + y) ^ n
    rw [sum_congr rfl f_succ, ← mul_sum, pow_succ y, mul_assoc, ← mul_add y, ih]
    -- 🎉 no goals
#align commute.geom_sum₂_mul_add Commute.geom_sum₂_mul_add

end Semiring

@[simp]
theorem neg_one_geom_sum [Ring α] {n : ℕ} :
    ∑ i in range n, (-1 : α) ^ i = if Even n then 0 else 1 := by
  induction' n with k hk
  -- ⊢ ∑ i in range Nat.zero, (-1) ^ i = if Even Nat.zero then 0 else 1
  · simp
    -- 🎉 no goals
  · simp only [geom_sum_succ', Nat.even_add_one, hk]
    -- ⊢ ((-1) ^ k + if Even k then 0 else 1) = if ¬Even k then 0 else 1
    split_ifs with h
    -- ⊢ (-1) ^ k + 0 = 1
    · rw [h.neg_one_pow, add_zero]
      -- 🎉 no goals
    · rw [(Nat.odd_iff_not_even.2 h).neg_one_pow, neg_add_self]
      -- 🎉 no goals
#align neg_one_geom_sum neg_one_geom_sum

theorem geom_sum₂_self {α : Type*} [CommRing α] (x : α) (n : ℕ) :
    ∑ i in range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  calc
    ∑ i in Finset.range n, x ^ i * x ^ (n - 1 - i) =
        ∑ i in Finset.range n, x ^ (i + (n - 1 - i)) :=
      by simp_rw [← pow_add]
         -- 🎉 no goals
    _ = ∑ i in Finset.range n, x ^ (n - 1) :=
      Finset.sum_congr rfl fun i hi =>
        congr_arg _ <| add_tsub_cancel_of_le <| Nat.le_pred_of_lt <| Finset.mem_range.1 hi
    _ = (Finset.range n).card • x ^ (n - 1) := Finset.sum_const _
    _ = n * x ^ (n - 1) := by rw [Finset.card_range, nsmul_eq_mul]
                              -- 🎉 no goals
#align geom_sum₂_self geom_sum₂_self

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [CommSemiring α] (x y : α) (n : ℕ) :
    (∑ i in range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n
#align geom_sum₂_mul_add geom_sum₂_mul_add

theorem geom_sum_mul_add [Semiring α] (x : α) (n : ℕ) :
    (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  -- ⊢ (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n
  rw [one_pow, geom_sum₂_with_one] at this
  -- ⊢ (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n
  exact this
  -- 🎉 no goals
#align geom_sum_mul_add geom_sum_mul_add

protected theorem Commute.geom_sum₂_mul [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  -- ⊢ (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
  rw [sub_add_cancel] at this
  -- ⊢ (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
  rw [← this, add_sub_cancel]
  -- 🎉 no goals
#align commute.geom_sum₂_mul Commute.geom_sum₂_mul

theorem Commute.mul_neg_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  -- ⊢ MulOpposite.op ((y - x) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = MulOppo …
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow]
  -- ⊢ MulOpposite.op (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (MulOpposite.op y …
  simp [(Commute.op h.symm).geom_sum₂_mul n]
  -- 🎉 no goals
#align commute.mul_neg_geom_sum₂ Commute.mul_neg_geom_sum₂

theorem Commute.mul_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]
  -- 🎉 no goals
#align commute.mul_geom_sum₂ Commute.mul_geom_sum₂

theorem geom_sum₂_mul [CommRing α] (x y : α) (n : ℕ) :
    (∑ i in range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  (Commute.all x y).geom_sum₂_mul n
#align geom_sum₂_mul geom_sum₂_mul

theorem sub_dvd_pow_sub_pow [CommRing α] (x y : α) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  Dvd.intro_left _ (geom_sum₂_mul x y n)
#align sub_dvd_pow_sub_pow sub_dvd_pow_sub_pow

theorem nat_sub_dvd_pow_sub_pow (x y n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  cases' le_or_lt y x with h h
  -- ⊢ x - y ∣ x ^ n - y ^ n
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_of_le_left h _
    -- ⊢ x - y ∣ x ^ n - y ^ n
    exact_mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
    -- 🎉 no goals
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_of_le_left h.le _
    -- ⊢ x - y ∣ x ^ n - y ^ n
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)
    -- 🎉 no goals
#align nat_sub_dvd_pow_sub_pow nat_sub_dvd_pow_sub_pow

theorem Odd.add_dvd_pow_add_pow [CommRing α] (x y : α) {n : ℕ} (h : Odd n) :
    x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  -- ⊢ x + y ∣ x ^ n + y ^ n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  -- ⊢ x + y ∣ x ^ n + y ^ n
  exact Dvd.intro_left _ h₁
  -- 🎉 no goals
#align odd.add_dvd_pow_add_pow Odd.add_dvd_pow_add_pow

theorem Odd.nat_add_dvd_pow_add_pow (x y : ℕ) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n := by
  exact_mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h
  -- 🎉 no goals
#align odd.nat_add_dvd_pow_add_pow Odd.nat_add_dvd_pow_add_pow

theorem geom_sum_mul [Ring α] (x : α) (n : ℕ) : (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  -- ⊢ (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1
  rw [one_pow, geom_sum₂_with_one] at this
  -- ⊢ (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1
  exact this
  -- 🎉 no goals
#align geom_sum_mul geom_sum_mul

theorem mul_geom_sum [Ring α] (x : α) (n : ℕ) : ((x - 1) * ∑ i in range n, x ^ i) = x ^ n - 1 :=
  op_injective <| by simpa using geom_sum_mul (op x) n
                     -- 🎉 no goals
#align mul_geom_sum mul_geom_sum

theorem geom_sum_mul_neg [Ring α] (x : α) (n : ℕ) :
    (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  have := congr_arg Neg.neg (geom_sum_mul x n)
  -- ⊢ (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n
  rw [neg_sub, ← mul_neg, neg_sub] at this
  -- ⊢ (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n
  exact this
  -- 🎉 no goals
#align geom_sum_mul_neg geom_sum_mul_neg

theorem mul_neg_geom_sum [Ring α] (x : α) (n : ℕ) : ((1 - x) * ∑ i in range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n
                     -- 🎉 no goals
#align mul_neg_geom_sum mul_neg_geom_sum

protected theorem Commute.geom_sum₂_comm {α : Type u} [Semiring α] {x y : α} (n : ℕ)
    (h : Commute x y) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = ∑ i in range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  -- ⊢ ∑ i in range Nat.zero, x ^ i * y ^ (Nat.zero - 1 - i) = ∑ i in range Nat.zer …
             -- 🎉 no goals
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  -- ⊢ ∑ x_1 in range (n✝ + 1), x ^ x_1 * y ^ (n✝ - x_1) = ∑ x_1 in range (n✝ + 1), …
  rw [← Finset.sum_flip]
  -- ⊢ ∑ r in range (n✝ + 1), x ^ (n✝ - r) * y ^ (n✝ - (n✝ - r)) = ∑ x_1 in range ( …
  refine' Finset.sum_congr rfl fun i hi => _
  -- ⊢ x ^ (n✝ - i) * y ^ (n✝ - (n✝ - i)) = y ^ i * x ^ (n✝ - i)
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _
  -- 🎉 no goals
#align commute.geom_sum₂_comm Commute.geom_sum₂_comm

theorem geom_sum₂_comm {α : Type u} [CommSemiring α] (x y : α) (n : ℕ) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = ∑ i in range n, y ^ i * x ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_comm n
#align geom_sum₂_comm geom_sum₂_comm

protected theorem Commute.geom_sum₂ [DivisionRing α] {x y : α} (h' : Commute x y) (h : x ≠ y)
    (n : ℕ) : ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  -- ⊢ ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y)
  rw [← h'.geom_sum₂_mul, mul_div_cancel _ this]
  -- 🎉 no goals
#align commute.geom_sum₂ Commute.geom_sum₂

theorem geom₂_sum [Field α] {x y : α} (h : x ≠ y) (n : ℕ) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n
#align geom₂_sum geom₂_sum

theorem geom_sum_eq [DivisionRing α] {x : α} (h : x ≠ 1) (n : ℕ) :
    ∑ i in range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  -- ⊢ ∑ i in range n, x ^ i = (x ^ n - 1) / (x - 1)
  rw [← geom_sum_mul, mul_div_cancel _ this]
  -- 🎉 no goals
#align geom_sum_eq geom_sum_eq

protected theorem Commute.mul_geom_sum₂_Ico [Ring α] {x y : α} (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  -- ⊢ (x - y) * (∑ k in range n, x ^ k * y ^ (n - 1 - k) - ∑ k in range m, x ^ k * …
  have :
    ∑ k in range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine' sum_congr rfl fun j j_in => _
    rw [← pow_add]
    congr
    rw [mem_range, Nat.lt_iff_add_one_le, add_comm] at j_in
    have h' : n - m + (m - (1 + j)) = n - (1 + j) := tsub_add_tsub_cancel hmn j_in
    rw [← tsub_add_eq_tsub_tsub m, h', ← tsub_add_eq_tsub_tsub]
  rw [this]
  -- ⊢ (x - y) * (∑ k in range n, x ^ k * y ^ (n - 1 - k) - ∑ k in range m, x ^ k * …
  simp_rw [pow_mul_comm y (n - m) _]
  -- ⊢ (x - y) * (∑ k in range n, x ^ k * y ^ (n - 1 - k) - ∑ x_1 in range m, x ^ x …
  simp_rw [← mul_assoc]
  -- ⊢ (x - y) * (∑ k in range n, x ^ k * y ^ (n - 1 - k) - ∑ x_1 in range m, x ^ x …
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]
#align commute.mul_geom_sum₂_Ico Commute.mul_geom_sum₂_Ico

protected theorem Commute.geom_sum₂_succ_eq {α : Type u} [Ring α] {x y : α} (h : Commute x y)
    {n : ℕ} :
    ∑ i in range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ]
  refine' sum_congr rfl fun i hi => _
  -- ⊢ x ^ i * y ^ (n - i) = x ^ i * y ^ (n - 1 - i + 1)
  suffices n - 1 - i + 1 = n - i by rw [this]
  -- ⊢ n - 1 - i + 1 = n - i
  cases' n with n
  -- ⊢ Nat.zero - 1 - i + 1 = Nat.zero - i
  · exact absurd (List.mem_range.mp hi) i.not_lt_zero
    -- 🎉 no goals
  · rw [tsub_add_eq_add_tsub (Nat.le_pred_of_lt (List.mem_range.mp hi)),
      tsub_add_cancel_of_le (Nat.succ_le_iff.mpr n.succ_pos)]
#align commute.geom_sum₂_succ_eq Commute.geom_sum₂_succ_eq

theorem geom_sum₂_succ_eq {α : Type u} [CommRing α] (x y : α) {n : ℕ} :
    ∑ i in range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i in range n, x ^ i * y ^ (n - 1 - i) :=
  (Commute.all x y).geom_sum₂_succ_eq
#align geom_sum₂_succ_eq geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [CommRing α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  (Commute.all x y).mul_geom_sum₂_Ico hmn
#align mul_geom_sum₂_Ico mul_geom_sum₂_Ico

protected theorem Commute.geom_sum₂_Ico_mul [Ring α] {x y : α} (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    (∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ (n - m) * x ^ m := by
  apply op_injective
  -- ⊢ MulOpposite.op ((∑ i in Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y)) = MulOp …
  simp only [op_sub, op_mul, op_pow, op_sum]
  -- ⊢ (MulOpposite.op x - MulOpposite.op y) * ∑ x_1 in Ico m n, MulOpposite.op y ^ …
  have : (∑ k in Ico m n, MulOpposite.op y ^ (n - 1 - k) * MulOpposite.op x ^ k) =
      ∑ k in Ico m n, MulOpposite.op x ^ k * MulOpposite.op y ^ (n - 1 - k) := by
    refine' sum_congr rfl fun k _ => _
    have hp := Commute.pow_pow (Commute.op h.symm) (n - 1 - k) k
    simpa [Commute, SemiconjBy] using hp
  simp only [this]
  -- ⊢ (MulOpposite.op x - MulOpposite.op y) * ∑ k in Ico m n, MulOpposite.op x ^ k …
  -- porting note: gives deterministic timeout without this intermediate `have`
  convert (Commute.op h).mul_geom_sum₂_Ico hmn
  -- 🎉 no goals
#align commute.geom_sum₂_Ico_mul Commute.geom_sum₂_Ico_mul

theorem geom_sum_Ico_mul [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]
  -- 🎉 no goals
#align geom_sum_Ico_mul geom_sum_Ico_mul

theorem geom_sum_Ico_mul_neg [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by
  rw [sum_Ico_eq_sub _ hmn, sub_mul, geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]
  -- 🎉 no goals
#align geom_sum_Ico_mul_neg geom_sum_Ico_mul_neg

protected theorem Commute.geom_sum₂_Ico [DivisionRing α] {x y : α} (h : Commute x y) (hxy : x ≠ y)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := by
  have : x - y ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  -- ⊢ ∑ i in Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m) / (x …
  rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel _ this]
  -- 🎉 no goals
#align commute.geom_sum₂_Ico Commute.geom_sum₂_Ico

theorem geom_sum₂_Ico [Field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i in Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn
#align geom_sum₂_Ico geom_sum₂_Ico

theorem geom_sum_Ico [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i in Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]
  -- 🎉 no goals
#align geom_sum_Ico geom_sum_Ico

theorem geom_sum_Ico' [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i in Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simp only [geom_sum_Ico hx hmn]
  -- ⊢ (x ^ n - x ^ m) / (x - 1) = (x ^ m - x ^ n) / (1 - x)
  convert neg_div_neg_eq (x ^ m - x ^ n) (1 - x) using 2 <;> abel
  -- ⊢ x ^ n - x ^ m = -(x ^ m - x ^ n)
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
#align geom_sum_Ico' geom_sum_Ico'

theorem geom_sum_Ico_le_of_lt_one [LinearOrderedField α] {x : α} (hx : 0 ≤ x) (h'x : x < 1)
    {m n : ℕ} : ∑ i in Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_lt m n with (hmn | hmn)
  -- ⊢ ∑ i in Ico m n, x ^ i ≤ x ^ m / (1 - x)
  · rw [geom_sum_Ico' h'x.ne hmn]
    -- ⊢ (x ^ m - x ^ n) / (1 - x) ≤ x ^ m / (1 - x)
    apply div_le_div (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    -- ⊢ x ^ m - x ^ n ≤ x ^ m
    simpa using pow_nonneg hx _
    -- 🎉 no goals
  · rw [Ico_eq_empty, sum_empty]
    -- ⊢ 0 ≤ x ^ m / (1 - x)
    · apply div_nonneg (pow_nonneg hx _)
      -- ⊢ 0 ≤ 1 - x
      simpa using h'x.le
      -- 🎉 no goals
    · simpa using hmn.le
      -- 🎉 no goals
#align geom_sum_Ico_le_of_lt_one geom_sum_Ico_le_of_lt_one

theorem geom_sum_inv [DivisionRing α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    ∑ i in range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ ≠ 1 := by rwa [inv_eq_one_div, Ne.def, div_eq_iff_mul_eq hx0, one_mul]
  -- ⊢ ∑ i in range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x)
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁
  -- ⊢ ∑ i in range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x)
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1
  -- ⊢ ∑ i in range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x)
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc,
        inv_mul_cancel hx0]
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel h₃]
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm,
    add_left_comm]
  rw [add_comm _ (-x), add_assoc, add_assoc _ _ 1]
  -- 🎉 no goals
#align geom_sum_inv geom_sum_inv

variable {β : Type*}

theorem RingHom.map_geom_sum [Semiring α] [Semiring β] (x : α) (n : ℕ) (f : α →+* β) :
    f (∑ i in range n, x ^ i) = ∑ i in range n, f x ^ i := by simp [f.map_sum]
                                                              -- 🎉 no goals
#align ring_hom.map_geom_sum RingHom.map_geom_sum

theorem RingHom.map_geom_sum₂ [Semiring α] [Semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
    f (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = ∑ i in range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [f.map_sum]
  -- 🎉 no goals
#align ring_hom.map_geom_sum₂ RingHom.map_geom_sum₂

/-! ### Geometric sum with `ℕ`-division -/


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) :
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) ≤ a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) =
        (∑ i in range n, a / b ^ (i + 1) * b) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) :=
      by rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, pow_zero,
        Nat.div_one]
    _ ≤ (∑ i in range n, a / b ^ i) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      refine' tsub_le_tsub_right (add_le_add_right (sum_le_sum fun i _ => _) _) _
      -- ⊢ a / b ^ (i + 1) * b ≤ a / b ^ i
      rw [pow_succ', mul_comm b]
      -- ⊢ a / (b ^ i * b) * b ≤ a / b ^ i
      rw [← Nat.div_div_eq_div_mul]
      -- ⊢ a / b ^ i / b * b ≤ a / b ^ i
      exact Nat.div_mul_le_self _ _
      -- 🎉 no goals
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _
#align nat.pred_mul_geom_sum_le Nat.pred_mul_geom_sum_le

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i in range n, a / b ^ i ≤ a * b / (b - 1) := by
  refine' (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 _
  -- ⊢ (∑ i in range n, a / b ^ i) * (b - 1) ≤ a * b
  cases' n with n
  -- ⊢ (∑ i in range zero, a / b ^ i) * (b - 1) ≤ a * b
  · rw [sum_range_zero, zero_mul]
    -- ⊢ 0 ≤ a * b
    exact Nat.zero_le _
    -- 🎉 no goals
  rw [mul_comm]
  -- ⊢ (b - 1) * ∑ i in range (succ n), a / b ^ i ≤ a * b
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self
  -- 🎉 no goals
#align nat.geom_sum_le Nat.geom_sum_le

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i in Ico 1 n, a / b ^ i ≤ a / (b - 1) := by
  cases' n with n
  -- ⊢ ∑ i in Ico 1 zero, a / b ^ i ≤ a / (b - 1)
  · rw [zero_eq, Ico_eq_empty_of_le (zero_le_one' ℕ), sum_empty]
    -- ⊢ 0 ≤ a / (b - 1)
    exact Nat.zero_le _
    -- 🎉 no goals
  rw [← add_le_add_iff_left a]
  -- ⊢ a + ∑ i in Ico 1 (succ n), a / b ^ i ≤ a + a / (b - 1)
  calc
    (a + ∑ i : ℕ in Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i : ℕ in Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero, Nat.div_one]
    _ = ∑ i in range n.succ, a / b ^ i := by
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
    0 < ∑ i in range n, x ^ i :=
  sum_pos' (fun k _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩
                                                                      -- 🎉 no goals
#align geom_sum_pos geom_sum_pos

theorem geom_sum_pos_and_lt_one [StrictOrderedRing α] (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    (0 < ∑ i in range n, x ^ i) ∧ ∑ i in range n, x ^ i < 1 := by
  refine' Nat.le_induction _ _ n (show 2 ≤ n from hn)
  -- ⊢ 0 < ∑ i in range 2, x ^ i ∧ ∑ i in range 2, x ^ i < 1
  · rw [geom_sum_two]
    -- ⊢ 0 < x + 1 ∧ x + 1 < 1
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
    -- 🎉 no goals
  clear hn
  -- ⊢ ∀ (n : ℕ), 2 ≤ n → 0 < ∑ i in range n, x ^ i ∧ ∑ i in range n, x ^ i < 1 → 0 …
  intro n _ ihn
  -- ⊢ 0 < ∑ i in range (n + 1), x ^ i ∧ ∑ i in range (n + 1), x ^ i < 1
  rw [geom_sum_succ, add_lt_iff_neg_right, ← neg_lt_iff_pos_add', neg_mul_eq_neg_mul]
  -- ⊢ -x * ∑ i in range n, x ^ i < 1 ∧ x * ∑ i in range n, x ^ i < 0
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_left (neg_nonneg.2 hx.le) (neg_lt_iff_pos_add'.2 hx') ihn.2.le,
      mul_neg_of_neg_of_pos hx ihn.1⟩
#align geom_sum_pos_and_lt_one geom_sum_pos_and_lt_one

theorem geom_sum_alternating_of_le_neg_one [StrictOrderedRing α] (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i in range n, x ^ i) ≤ 0 else 1 ≤ ∑ i in range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  -- ⊢ if Even n then ∑ i in range n, x ^ i ≤ 0 else 1 ≤ ∑ i in range n, x ^ i
  induction' n with n ih
  -- ⊢ if Even Nat.zero then ∑ i in range Nat.zero, x ^ i ≤ 0 else 1 ≤ ∑ i in range …
  · simp only [Nat.zero_eq, range_zero, sum_empty, le_refl, ite_true]
    -- 🎉 no goals
  simp only [Nat.even_add_one, geom_sum_succ]
  -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 ≤ 0 else 1 ≤ x * ∑ i in range  …
  split_ifs at ih with h
  -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 ≤ 0 else 1 ≤ x * ∑ i in range  …
  · rw [if_neg (not_not_intro h), le_add_iff_nonneg_left]
    -- ⊢ 0 ≤ x * ∑ i in range n, x ^ i
    exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    -- 🎉 no goals
  · rw [if_pos h]
    -- ⊢ x * ∑ i in range n, x ^ i + 1 ≤ 0
    refine' (add_le_add_right _ _).trans hx
    -- ⊢ x * ∑ i in range n, x ^ i ≤ x
    simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0
    -- 🎉 no goals
#align geom_sum_alternating_of_le_neg_one geom_sum_alternating_of_le_neg_one

theorem geom_sum_alternating_of_lt_neg_one [StrictOrderedRing α] (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then (∑ i in range n, x ^ i) < 0 else 1 < ∑ i in range n, x ^ i := by
  have hx0 : x < 0 := ((le_add_iff_nonneg_right _).2 zero_le_one).trans_lt hx
  -- ⊢ if Even n then ∑ i in range n, x ^ i < 0 else 1 < ∑ i in range n, x ^ i
  refine' Nat.le_induction _ _ n (show 2 ≤ n from hn)
  -- ⊢ if Even 2 then ∑ i in range 2, x ^ i < 0 else 1 < ∑ i in range 2, x ^ i
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, gt_iff_lt, hx]
    -- 🎉 no goals
  clear hn
  -- ⊢ ∀ (n : ℕ), 2 ≤ n → (if Even n then ∑ i in range n, x ^ i < 0 else 1 < ∑ i in …
  intro n _ ihn
  -- ⊢ if Even (n + 1) then ∑ i in range (n + 1), x ^ i < 0 else 1 < ∑ i in range ( …
  simp only [Nat.even_add_one, geom_sum_succ]
  -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 < 0 else 1 < x * ∑ i in range  …
  by_cases hn' : Even n
  -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 < 0 else 1 < x * ∑ i in range  …
  · rw [if_pos hn'] at ihn
    -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 < 0 else 1 < x * ∑ i in range  …
    rw [if_neg, lt_add_iff_pos_left]
    -- ⊢ 0 < x * ∑ i in range n, x ^ i
    exact mul_pos_of_neg_of_neg hx0 ihn
    -- ⊢ ¬¬Even n
    exact not_not_intro hn'
    -- 🎉 no goals
  · rw [if_neg hn'] at ihn
    -- ⊢ if ¬Even n then x * ∑ i in range n, x ^ i + 1 < 0 else 1 < x * ∑ i in range  …
    rw [if_pos]
    -- ⊢ x * ∑ i in range n, x ^ i + 1 < 0
    swap
    -- ⊢ ¬Even n
    · exact hn'
      -- 🎉 no goals
    have := add_lt_add_right (mul_lt_mul_of_neg_left ihn hx0) 1
    -- ⊢ x * ∑ i in range n, x ^ i + 1 < 0
    rw [mul_one] at this
    -- ⊢ x * ∑ i in range n, x ^ i + 1 < 0
    exact this.trans hx
    -- 🎉 no goals
#align geom_sum_alternating_of_lt_neg_one geom_sum_alternating_of_lt_neg_one

theorem geom_sum_pos' [LinearOrderedRing α] (hx : 0 < x + 1) (hn : n ≠ 0) :
    0 < ∑ i in range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
    -- 🎉 no goals
  · simp only [Nat.zero_eq, ← Nat.one_eq_succ_zero, range_one, sum_singleton, pow_zero, zero_lt_one]
    -- 🎉 no goals
  obtain hx' | hx' := lt_or_le x 0
  -- ⊢ 0 < ∑ i in range (Nat.succ (Nat.succ n)), x ^ i
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
    -- 🎉 no goals
  · exact geom_sum_pos hx' (by simp only [Nat.succ_ne_zero, Ne.def, not_false_iff])
    -- 🎉 no goals
#align geom_sum_pos' geom_sum_pos'

theorem Odd.geom_sum_pos [LinearOrderedRing α] (h : Odd n) : 0 < ∑ i in range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact ((show ¬Odd 0 by decide) h).elim
    -- 🎉 no goals
  · simp only [Nat.zero_eq, ← Nat.one_eq_succ_zero, geom_sum_one, zero_lt_one]
    -- 🎉 no goals
  rw [Nat.odd_iff_not_even] at h
  -- ⊢ 0 < ∑ i in range (Nat.succ (Nat.succ k)), x ^ i
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    -- ⊢ 0 < ∑ i in range (Nat.succ (Nat.succ k)), x ^ i
    simp only [h, if_false] at this
    -- ⊢ 0 < ∑ i in range (Nat.succ (Nat.succ k)), x ^ i
    exact zero_lt_one.trans this
    -- 🎉 no goals
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one]
    -- 🎉 no goals
  · exact geom_sum_pos' hx k.succ.succ_ne_zero
    -- 🎉 no goals
#align odd.geom_sum_pos Odd.geom_sum_pos

theorem geom_sum_pos_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    (0 < ∑ i in range n, x ^ i) ↔ Odd n ∨ 0 < x + 1 := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ Odd n ∨ 0 < x + 1
  · rw [or_iff_not_imp_left, ← not_le, ← Nat.even_iff_not_odd]
    -- ⊢ Even n → ¬x + 1 ≤ 0
    refine' fun hn hx => h.not_le _
    -- ⊢ ∑ i in range n, x ^ i ≤ 0
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
    -- 🎉 no goals
  · rintro (hn | hx')
    -- ⊢ 0 < ∑ i in range n, x ^ i
    · exact hn.geom_sum_pos
      -- 🎉 no goals
    · exact geom_sum_pos' hx' hn
      -- 🎉 no goals
#align geom_sum_pos_iff geom_sum_pos_iff

theorem geom_sum_ne_zero [LinearOrderedRing α] (hx : x ≠ -1) (hn : n ≠ 0) :
    ∑ i in range n, x ^ i ≠ 0 := by
  obtain _ | _ | n := n
  · cases hn rfl
    -- 🎉 no goals
  · simp only [Nat.zero_eq, ← Nat.one_eq_succ_zero, range_one, sum_singleton, pow_zero, ne_eq,
      one_ne_zero, not_false_iff]
  rw [Ne.def, eq_neg_iff_add_eq_zero, ← Ne.def] at hx
  -- ⊢ ∑ i in range (Nat.succ (Nat.succ n)), x ^ i ≠ 0
  obtain h | h := hx.lt_or_lt
  -- ⊢ ∑ i in range (Nat.succ (Nat.succ n)), x ^ i ≠ 0
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
    -- ⊢ ∑ i in range (Nat.succ (Nat.succ n)), x ^ i ≠ 0
    split_ifs at this
    -- ⊢ ∑ i in range (Nat.succ (Nat.succ n)), x ^ i ≠ 0
    · exact this.ne
      -- 🎉 no goals
    · exact (zero_lt_one.trans this).ne'
      -- 🎉 no goals
  · exact (geom_sum_pos' h n.succ.succ_ne_zero).ne'
    -- 🎉 no goals
#align geom_sum_ne_zero geom_sum_ne_zero

theorem geom_sum_eq_zero_iff_neg_one [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i in range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine' ⟨fun h => _, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  -- ⊢ x = -1 ∧ Even n
  contrapose! h
  -- ⊢ ∑ i in range n, x ^ i ≠ 0
  have hx := eq_or_ne x (-1)
  -- ⊢ ∑ i in range n, x ^ i ≠ 0
  cases' hx with hx hx
  -- ⊢ ∑ i in range n, x ^ i ≠ 0
  · rw [hx, neg_one_geom_sum]
    -- ⊢ (if Even n then 0 else 1) ≠ 0
    simp only [h hx, ne_eq, ite_eq_left_iff, one_ne_zero, not_forall, exists_prop, and_true]
    -- 🎉 no goals
  · exact geom_sum_ne_zero hx hn
    -- 🎉 no goals
#align geom_sum_eq_zero_iff_neg_one geom_sum_eq_zero_iff_neg_one

theorem geom_sum_neg_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i in range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), Nat.odd_iff_not_even, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]
#align geom_sum_neg_iff geom_sum_neg_iff

end Order
