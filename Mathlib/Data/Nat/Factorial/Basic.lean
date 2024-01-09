/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.Common

#align_import data.nat.factorial.basic from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.

## Main declarations

* `Nat.factorial`: The factorial.
* `Nat.ascFactorial`: The ascending factorial. It is the product of natural numbers from `n` to
  `n + k - 1`.
* `Nat.descFactorial`: The descending factorial. It is the product of natural numbers from
  `n - k + 1` to `n`.
-/


namespace Nat

/-- `Nat.factorial n` is the factorial of `n`. -/
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n
#align nat.factorial Nat.factorial

/-- factorial notation `n!` -/
scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}

@[simp] theorem factorial_zero : 0! = 1 :=
  rfl
#align nat.factorial_zero Nat.factorial_zero

theorem factorial_succ (n : ℕ) : (n + 1)! = (n + 1) * n ! :=
  rfl
#align nat.factorial_succ Nat.factorial_succ


@[simp] theorem factorial_one : 1! = 1 :=
  rfl
#align nat.factorial_one Nat.factorial_one

@[simp] theorem factorial_two : 2! = 2 :=
  rfl
#align nat.factorial_two Nat.factorial_two

theorem mul_factorial_pred (hn : 0 < n) : n * (n - 1)! = n ! :=
  tsub_add_cancel_of_le (Nat.succ_le_of_lt hn) ▸ rfl
#align nat.mul_factorial_pred Nat.mul_factorial_pred

theorem factorial_pos : ∀ n, 0 < n !
  | 0 => zero_lt_one
  | succ n => mul_pos (succ_pos _) (factorial_pos n)
#align nat.factorial_pos Nat.factorial_pos

theorem factorial_ne_zero (n : ℕ) : n ! ≠ 0 :=
  ne_of_gt (factorial_pos _)
#align nat.factorial_ne_zero Nat.factorial_ne_zero

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m ! ∣ n ! := by
  induction' n with n IH
  · simp [Nat.eq_zero_of_le_zero h]
  obtain rfl | hl := h.eq_or_lt
  · simp
  exact (IH (le_of_lt_succ hl)).mul_left _
#align nat.factorial_dvd_factorial Nat.factorial_dvd_factorial

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n !
  | succ _, _, _, h => dvd_of_mul_right_dvd (factorial_dvd_factorial h)
#align nat.dvd_factorial Nat.dvd_factorial

@[mono, gcongr]
theorem factorial_le {m n} (h : m ≤ n) : m ! ≤ n ! :=
  le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)
#align nat.factorial_le Nat.factorial_le

theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m ! * (m + 1) ^ n ≤ (m + n)!
  | m, 0 => by simp
  | m, n + 1 => by
    rw [← add_assoc, factorial_succ, mul_comm (_ + 1), pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul factorial_mul_pow_le_factorial (succ_le_succ (le_add_right _ _))
#align nat.factorial_mul_pow_le_factorial Nat.factorial_mul_pow_le_factorial

theorem monotone_factorial : Monotone factorial := fun _ _ => factorial_le
#align nat.monotone_factorial Nat.monotone_factorial

theorem factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m := by
  refine' ⟨fun h => not_le.mp fun hmn => not_le_of_lt h (factorial_le hmn), fun h => _⟩
  have : ∀ {n}, 0 < n → n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ, succ_mul, lt_add_iff_pos_left]
    exact mul_pos hk k.factorial_pos
  induction' h with k hnk ih generalizing hn
  · exact this hn
  · exact (ih hn).trans (this <| hn.trans <| lt_of_succ_le hnk)
#align nat.factorial_lt Nat.factorial_lt

@[gcongr]
lemma factorial_lt_of_lt {m n : ℕ} (hn : 0 < n) (h : n < m) : n ! < m ! := (factorial_lt hn).mpr h

@[simp]
theorem one_lt_factorial : 1 < n ! ↔ 1 < n :=
  factorial_lt one_pos
#align nat.one_lt_factorial Nat.one_lt_factorial

@[simp]
theorem factorial_eq_one : n ! = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    rw [← not_lt, ← one_lt_factorial, h]
    apply lt_irrefl
  · rintro (_|_|_) <;> rfl
#align nat.factorial_eq_one Nat.factorial_eq_one

theorem factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m := by
  refine' ⟨fun h => _, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| pos_of_gt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial, h, one_lt_factorial] at hn
  rw [← factorial_lt <| pos_of_gt hn, h] at hnm
  cases lt_irrefl _ hnm
#align nat.factorial_inj Nat.factorial_inj

theorem factorial_inj' (h : 1 < n ∨ 1 < m) : n ! = m ! ↔ n = m := by
  obtain hn|hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]

theorem self_le_factorial : ∀ n : ℕ, n ≤ n !
  | 0 => zero_le_one
  | k + 1 => le_mul_of_one_le_right k.zero_lt_succ.le (Nat.one_le_of_lt <| Nat.factorial_pos _)
#align nat.self_le_factorial Nat.self_le_factorial

theorem lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n ! := by
  have : 0 < n := (zero_lt_two (α := ℕ)).trans (succ_le_iff.mp hi)
  have : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›, factorial_succ]
  exact
    lt_mul_of_one_lt_right (pred n).succ_pos
      ((‹1 < pred n›).trans_le (self_le_factorial _))
#align nat.lt_factorial_self Nat.lt_factorial_self

theorem add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
    i + (n + 1)! < (i + n + 1)! := by
  rw [factorial_succ (i + _), add_mul, one_mul]
  have : i ≤ i + n := le.intro rfl
  exact
    add_lt_add_of_lt_of_le
      (this.trans_lt
        ((lt_mul_iff_one_lt_right ((by decide : 0 < 2).trans_le (hi.trans this))).mpr
          (lt_iff_le_and_ne.mpr
            ⟨(i + n).factorial_pos, fun g =>
              Nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩)))
      (factorial_le
        ((le_of_eq (add_comm n 1)).trans
        ((add_le_add_iff_right n).mpr ((by decide : 1 ≤ 2).trans hi))))
#align nat.add_factorial_succ_lt_factorial_add_succ Nat.add_factorial_succ_lt_factorial_add_succ

theorem add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
    i + n ! < (i + n)! := by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi
#align nat.add_factorial_lt_factorial_add Nat.add_factorial_lt_factorial_add

theorem add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) :
    i + (n + 1)! ≤ (i + (n + 1))! := by
  cases (le_or_lt (2 : ℕ) i)
  · rw [← add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← add_assoc, factorial_succ (1 + n), add_mul, one_mul, add_comm 1 n, add_le_add_iff_right]
      apply one_le_mul
      · apply Nat.le_add_left
      · apply factorial_pos
    | succ (succ n) => contradiction
#align nat.add_factorial_succ_le_factorial_add_succ Nat.add_factorial_succ_le_factorial_add_succ

theorem add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) : i + n ! ≤ (i + n)! := by
  cases' n1 with h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h
#align nat.add_factorial_le_factorial_add Nat.add_factorial_le_factorial_add

theorem factorial_mul_pow_sub_le_factorial {n m : ℕ} (hnm : n ≤ m) : n ! * n ^ (m - n) ≤ m ! := by
  calc
    _ ≤ n ! * (n + 1) ^ (m - n) := mul_le_mul_left' (Nat.pow_le_pow_left n.le_succ _) _
    _ ≤ _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)
#align nat.factorial_mul_pow_sub_le_factorial Nat.factorial_mul_pow_sub_le_factorial

lemma factorial_le_pow : ∀ n, n ! ≤ n ^ n
  | 0 => le_rfl
  | n + 1 =>
    calc
      _ ≤ (n + 1) * n ^ n := mul_le_mul_left' n.factorial_le_pow _
      _ ≤ (n + 1) * (n + 1) ^ n := mul_le_mul_left' (Nat.pow_le_pow_left n.le_succ _) _
      _ = _ := by rw [pow_succ']

end Factorial

/-! ### Ascending and descending factorials -/


section AscFactorial

/-- `n.ascFactorial k = n (n + 1) ⋯ (n + k - 1)`. This is closely related to `ascPochhammer`, but
much less general. -/
def ascFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n + k) * ascFactorial n k
#align nat.asc_factorial Nat.ascFactorial

@[simp]
theorem ascFactorial_zero (n : ℕ) : n.ascFactorial 0 = 1 :=
  rfl
#align nat.asc_factorial_zero Nat.ascFactorial_zero

theorem ascFactorial_succ {n k : ℕ} : n.ascFactorial k.succ = (n + k) * n.ascFactorial k :=
  rfl
#align nat.asc_factorial_succ Nat.ascFactorial_succ

theorem zero_ascFactorial : ∀ (k : ℕ), (0 : ℕ).ascFactorial k.succ = 0
  | 0 => by
    rw [ascFactorial_succ, ascFactorial_zero, zero_add, zero_mul]
  | (k+1) => by
    rw [ascFactorial_succ, zero_ascFactorial k, mul_zero]

@[simp]
theorem one_ascFactorial : ∀ (k : ℕ), (1 : ℕ).ascFactorial k = k.factorial
  | 0 => ascFactorial_zero 1
  | (k+1) => by
    rw [ascFactorial_succ, one_ascFactorial k, add_comm, factorial_succ]

theorem succ_ascFactorial (n : ℕ) :
    ∀ k, n * n.succ.ascFactorial k = (n + k) * n.ascFactorial k
  | 0 => by rw [add_zero, ascFactorial_zero, ascFactorial_zero]
  | k + 1 => by
    rw [ascFactorial, mul_left_comm, succ_ascFactorial n k, ascFactorial, succ_add, ← add_assoc]
#align nat.succ_asc_factorial Nat.succ_ascFactorial

/-- `(n + 1).ascFactorial k = (n + k) ! / n !` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. -/
theorem factorial_mul_ascFactorial (n : ℕ) : ∀ k, n ! * (n + 1).ascFactorial k = (n + k)!
  | 0 => by
    rw [add_zero, ascFactorial_zero, mul_one]
  | k + 1 => by
    rw [ascFactorial_succ, ← add_assoc, factorial_succ, mul_comm (n + 1 + k), ← mul_assoc,
      factorial_mul_ascFactorial n k, mul_comm, add_right_comm]
#align nat.factorial_mul_asc_factorial Nat.factorial_mul_ascFactorial

/-- `n.ascFactorial k = (n + k - 1)! / (n - 1)!` for `n > 0` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. Consider using
`factorial_mul_ascFactorial` to avoid complications of ℕ-subtraction. -/
theorem factorial_mul_ascFactorial' (n k : ℕ) (h : 0 < n) :
    (n - 1) ! * n.ascFactorial k = (n + k - 1)! := by
  rw [Nat.sub_add_comm h, Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one, factorial_mul_ascFactorial]

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial` if you can. ℕ-division isn't worth it. -/
theorem ascFactorial_eq_div (n k : ℕ) :  (n + 1).ascFactorial k = (n + k)! / n ! := by
  apply mul_left_cancel₀ n.factorial_ne_zero
  rw [factorial_mul_ascFactorial]
  exact (Nat.mul_div_cancel_left' <| factorial_dvd_factorial <| le_add_right n k).symm

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial` if you can. -/
theorem ascFactorial_eq_div' (n k : ℕ) (h : 0 < n) :
    n.ascFactorial k = (n + k - 1)! / (n - 1) ! := by
  apply mul_left_cancel₀ (n-1).factorial_ne_zero
  rw [factorial_mul_ascFactorial' _ _ h]
  exact (Nat.mul_div_cancel_left' <| factorial_dvd_factorial <| Nat.sub_le_sub_right
    (le_add_right n k) 1).symm
#align nat.asc_factorial_eq_div Nat.ascFactorial_eq_div

theorem ascFactorial_of_sub {n k : ℕ}:
    (n - k) * (n - k + 1).ascFactorial k = (n - k).ascFactorial (k + 1) := by
  rw [succ_ascFactorial, ascFactorial_succ]
#align nat.asc_factorial_of_sub Nat.ascFactorial_of_sub

theorem pow_succ_le_ascFactorial (n : ℕ) : ∀ k : ℕ, n ^ k ≤ n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, pow_zero]
  | k + 1 => by
    rw [pow_succ, mul_comm, ascFactorial_succ, ← succ_ascFactorial]
    exact Nat.mul_le_mul (Nat.le_refl n)
      ((pow_le_pow_of_le_left (le_succ n) k).trans (pow_succ_le_ascFactorial n.succ k))
#align nat.pow_succ_le_asc_factorial Nat.pow_succ_le_ascFactorial

theorem pow_lt_ascFactorial' (n k : ℕ) : (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2) := by
  rw [pow_succ, ascFactorial, mul_comm]
  exact Nat.mul_lt_mul (lt_add_of_pos_right (n + 1) (succ_pos k))
    (pow_succ_le_ascFactorial n.succ _) (NeZero.pos ((n + 1) ^ (k + 1)))
#align nat.pow_lt_asc_factorial' Nat.pow_lt_ascFactorial'

theorem pow_lt_ascFactorial (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1) ^ k < (n + 1).ascFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => pow_lt_ascFactorial' n k
#align nat.pow_lt_asc_factorial Nat.pow_lt_ascFactorial

theorem ascFactorial_le_pow_add (n : ℕ) : ∀ k : ℕ, (n+1).ascFactorial k ≤ (n + k) ^ k
  | 0 => by rw [ascFactorial_zero, pow_zero]
  | k + 1 => by
    rw [ascFactorial_succ, pow_succ, mul_comm, ← add_assoc, add_right_comm n 1 k]
    exact Nat.mul_le_mul_of_nonneg_right
      ((ascFactorial_le_pow_add _ k).trans (Nat.pow_le_pow_of_le_left (le_succ _) _))
#align nat.asc_factorial_le_pow_add Nat.ascFactorial_le_pow_add

theorem ascFactorial_lt_pow_add (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1).ascFactorial k < (n + k) ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [pow_succ, mul_comm, ascFactorial_succ, succ_add_eq_add_succ n (k + 1)]
    exact Nat.mul_lt_mul' le_rfl ((ascFactorial_le_pow_add n _).trans_lt
      (pow_lt_pow_left (@lt_add_one ℕ _ _ _ _ _ _ _) (zero_le _) k.succ_ne_zero)) (succ_pos _)
#align nat.asc_factorial_lt_pow_add Nat.ascFactorial_lt_pow_add

theorem ascFactorial_pos (n k : ℕ) : 0 < (n + 1).ascFactorial k :=
  (pow_pos (succ_pos n) k).trans_le (pow_succ_le_ascFactorial (n + 1) k)
#align nat.asc_factorial_pos Nat.ascFactorial_pos

end AscFactorial

section DescFactorial

/-- `n.descFactorial k = n! / (n - k)!` (as seen in `Nat.descFactorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. This is closely
related to `descPochhammer`, but much less general. -/
def descFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k
#align nat.desc_factorial Nat.descFactorial

@[simp]
theorem descFactorial_zero (n : ℕ) : n.descFactorial 0 = 1 :=
  rfl
#align nat.desc_factorial_zero Nat.descFactorial_zero

@[simp]
theorem descFactorial_succ (n k : ℕ) : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
  rfl
#align nat.desc_factorial_succ Nat.descFactorial_succ

theorem zero_descFactorial_succ (k : ℕ) : (0 : ℕ).descFactorial (k + 1) = 0 := by
  rw [descFactorial_succ, zero_tsub, zero_mul]
#align nat.zero_desc_factorial_succ Nat.zero_descFactorial_succ

theorem descFactorial_one (n : ℕ) : n.descFactorial 1 = n := by simp
#align nat.desc_factorial_one Nat.descFactorial_one

theorem succ_descFactorial_succ (n : ℕ) :
    ∀ k : ℕ, (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
  | 0 => by rw [descFactorial_zero, descFactorial_one, mul_one]
  | succ k => by
    rw [descFactorial_succ, succ_descFactorial_succ _ k, descFactorial_succ, succ_sub_succ,
      mul_left_comm]
#align nat.succ_desc_factorial_succ Nat.succ_descFactorial_succ

theorem succ_descFactorial (n : ℕ) :
    ∀ k, (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFactorial k
  | 0 => by rw [tsub_zero, descFactorial_zero, descFactorial_zero]
  | k + 1 => by
    rw [descFactorial, succ_descFactorial _ k, descFactorial_succ, succ_sub_succ, mul_left_comm]
#align nat.succ_desc_factorial Nat.succ_descFactorial

theorem descFactorial_self : ∀ n : ℕ, n.descFactorial n = n !
  | 0 => by rw [descFactorial_zero, factorial_zero]
  | succ n => by rw [succ_descFactorial_succ, descFactorial_self n, factorial_succ]
#align nat.desc_factorial_self Nat.descFactorial_self

@[simp]
theorem descFactorial_eq_zero_iff_lt {n : ℕ} : ∀ {k : ℕ}, n.descFactorial k = 0 ↔ n < k
  | 0 => by simp only [descFactorial_zero, Nat.one_ne_zero, Nat.not_lt_zero]
  | succ k => by
    rw [descFactorial_succ, mul_eq_zero, descFactorial_eq_zero_iff_lt, lt_succ_iff,
      tsub_eq_zero_iff_le, lt_iff_le_and_ne, or_iff_left_iff_imp, and_imp]
    exact fun h _ => h
#align nat.desc_factorial_eq_zero_iff_lt Nat.descFactorial_eq_zero_iff_lt

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt
#align nat.desc_factorial_of_lt Nat.descFactorial_of_lt

theorem add_descFactorial_eq_ascFactorial (n : ℕ) : ∀ k : ℕ,
    (n + k).descFactorial k = (n + 1).ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [Nat.add_succ, succ_descFactorial_succ, ascFactorial_succ,
      add_descFactorial_eq_ascFactorial _ k, Nat.add_right_comm]
#align nat.add_desc_factorial_eq_asc_factorial Nat.add_descFactorial_eq_ascFactorial

theorem add_descFactorial_eq_ascFactorial' (n : ℕ) :
    ∀ k : ℕ, (n + k - 1).descFactorial k = n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [descFactorial_succ, ascFactorial_succ, ← succ_add_eq_add_succ,
      add_descFactorial_eq_ascFactorial' _ k, ← succ_ascFactorial, succ_add_sub_one,
      Nat.add_sub_cancel]

/-- `n.descFactorial k = n! / (n - k)!` but without ℕ-division. See `Nat.descFactorial_eq_div`
for the version using ℕ-division. -/
theorem factorial_mul_descFactorial : ∀ {n k : ℕ}, k ≤ n → (n - k)! * n.descFactorial k = n !
  | n, 0 => fun _ => by rw [descFactorial_zero, mul_one, tsub_zero]
  | 0, succ k => fun h => by
    exfalso
    exact not_succ_le_zero k h
  | succ n, succ k => fun h => by
    rw [succ_descFactorial_succ, succ_sub_succ, ← mul_assoc, mul_comm (n - k)!, mul_assoc,
      factorial_mul_descFactorial (Nat.succ_le_succ_iff.1 h), factorial_succ]
#align nat.factorial_mul_desc_factorial Nat.factorial_mul_descFactorial

/-- Avoid in favor of `Nat.factorial_mul_descFactorial` if you can. ℕ-division isn't worth it. -/
theorem descFactorial_eq_div {n k : ℕ} (h : k ≤ n) : n.descFactorial k = n ! / (n - k)! := by
  apply mul_left_cancel₀ (factorial_ne_zero (n - k))
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm
#align nat.desc_factorial_eq_div Nat.descFactorial_eq_div

theorem pow_sub_le_descFactorial (n : ℕ) : ∀ k : ℕ, (n + 1 - k) ^ k ≤ n.descFactorial k
  | 0 => by rw [descFactorial_zero, pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, pow_succ, succ_sub_succ, mul_comm]
    apply Nat.mul_le_mul_of_nonneg_left
    exact   (le_trans (Nat.pow_le_pow_left (tsub_le_tsub_right (le_succ _) _) k)
          (pow_sub_le_descFactorial n k))
#align nat.pow_sub_le_desc_factorial Nat.pow_sub_le_descFactorial

theorem pow_sub_lt_descFactorial' {n : ℕ} :
    ∀ {k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
  | 0 => fun h => by
    rw [descFactorial_succ, pow_succ, pow_one, descFactorial_one]
    exact
      Nat.mul_lt_mul_of_pos_left (tsub_lt_self (lt_of_lt_of_le zero_lt_two h) zero_lt_one)
        (tsub_pos_of_lt h)
  | k + 1 => fun h => by
    rw [descFactorial_succ, pow_succ, mul_comm]
    apply Nat.mul_lt_mul_of_pos_left
    · refine' ((Nat.pow_le_pow_left (tsub_le_tsub_right (le_succ n) _) _).trans_lt _)
      rw [succ_sub_succ]
      exact pow_sub_lt_descFactorial' ((le_succ _).trans h)
    · apply tsub_pos_of_lt; apply h
#align nat.pow_sub_lt_desc_factorial' Nat.pow_sub_lt_descFactorial'

theorem pow_sub_lt_descFactorial {n : ℕ} :
    ∀ {k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k) ^ k < n.descFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ h => by
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' h
#align nat.pow_sub_lt_desc_factorial Nat.pow_sub_lt_descFactorial

theorem descFactorial_le_pow (n : ℕ) : ∀ k : ℕ, n.descFactorial k ≤ n ^ k
  | 0 => by rw [descFactorial_zero, pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, pow_succ, mul_comm _ n]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (descFactorial_le_pow _ k)
#align nat.desc_factorial_le_pow Nat.descFactorial_le_pow

theorem descFactorial_lt_pow {n : ℕ} (hn : 1 ≤ n) : ∀ {k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [descFactorial_succ, pow_succ', mul_comm, mul_comm n]
    exact Nat.mul_lt_mul' (descFactorial_le_pow _ _) (tsub_lt_self hn k.zero_lt_succ)
      (pow_pos (Nat.lt_of_succ_le hn) _)
#align nat.desc_factorial_lt_pow Nat.descFactorial_lt_pow

end DescFactorial

lemma factorial_two_mul_le (n : ℕ) : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [two_mul, ← factorial_mul_ascFactorial, mul_comm]
  exact mul_le_mul_right' (ascFactorial_le_pow_add _ _) _

lemma two_pow_mul_factorial_le_factorial_two_mul (n : ℕ) : 2 ^ n * n ! ≤ (2 * n) ! := by
  obtain _ | n := n
  · simp
  rw [mul_comm, two_mul]
  calc
    _ ≤ (n + 1)! * (n + 2) ^ (n + 1) := mul_le_mul_left' (pow_le_pow_of_le_left le_add_self _) _
    _ ≤ _ := Nat.factorial_mul_pow_le_factorial

end Nat
