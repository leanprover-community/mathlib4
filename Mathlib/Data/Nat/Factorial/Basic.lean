/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Monotonicity.Attr

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.
For the proof that the factorial of `n` counts the permutations of an `n`-element set,
see `Fintype.card_perm`.

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

/-- factorial notation `(n)!` for `Nat.factorial n`.
In Lean, names can end with exclamation marks (e.g. `List.get!`), so you cannot write
`n!` in Lean, but must write `(n)!` or `n !` instead. The former is preferred, since
Lean can confuse the `!` in `n !` as the (prefix) Boolean negation operation in some
cases.
For numerals the parentheses are not required, so e.g. `0!` or `1!` work fine.
Todo: replace occurrences of `n !` with `(n)!` in Mathlib. -/
scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}

@[simp] theorem factorial_zero : 0! = 1 :=
  rfl

theorem factorial_succ (n : ℕ) : (n + 1)! = (n + 1) * n ! :=
  rfl


@[simp] theorem factorial_one : 1! = 1 :=
  rfl

@[simp] theorem factorial_two : 2! = 2 :=
  rfl

theorem mul_factorial_pred (hn : n ≠ 0) : n * (n - 1)! = n ! :=
  Nat.sub_add_cancel (one_le_iff_ne_zero.mpr hn) ▸ rfl

theorem factorial_pos : ∀ n, 0 < n !
  | 0 => Nat.zero_lt_one
  | succ n => Nat.mul_pos (succ_pos _) (factorial_pos n)

theorem factorial_ne_zero (n : ℕ) : n ! ≠ 0 :=
  ne_of_gt (factorial_pos _)

@[gcongr]
theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m ! ∣ n ! := by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n !
  | succ _, _, _, h => Nat.dvd_trans (Nat.dvd_mul_right _ _) (factorial_dvd_factorial h)

@[mono, gcongr]
theorem factorial_le {m n} (h : m ≤ n) : m ! ≤ n ! :=
  le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)

theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m ! * (m + 1) ^ n ≤ (m + n)!
  | m, 0 => by simp
  | m, n + 1 => by
    rw [← Nat.add_assoc, factorial_succ, Nat.mul_comm (_ + 1), Nat.pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_le_mul factorial_mul_pow_le_factorial (succ_le_succ (le_add_right _ _))

theorem factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m := by
  refine ⟨fun h => not_le.mp fun hmn => Nat.not_le_of_gt h (factorial_le hmn), fun h => ?_⟩
  have : ∀ {n}, 0 < n → n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ, succ_mul, Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos hk k.factorial_pos
  induction h generalizing hn with
  | refl => exact this hn
  | step hnk ih => exact lt_trans (ih hn) <| this <| lt_trans hn <| lt_of_succ_le hnk

@[gcongr]
lemma factorial_lt_of_lt {m n : ℕ} (hn : 0 < n) (h : n < m) : n ! < m ! := (factorial_lt hn).mpr h

@[simp] lemma one_lt_factorial : 1 < n ! ↔ 1 < n := factorial_lt Nat.one_pos

@[simp]
theorem factorial_eq_one : n ! = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    rw [← not_lt, ← one_lt_factorial, h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl

theorem factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m := by
  refine ⟨fun h => ?_, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial, h, one_lt_factorial] at hn
  rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
  cases lt_irrefl _ hnm

theorem factorial_inj' (h : 1 < n ∨ 1 < m) : n ! = m ! ↔ n = m := by
  obtain hn | hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]

theorem self_le_factorial : ∀ n : ℕ, n ≤ n !
  | 0 => Nat.zero_le _
  | k + 1 => Nat.le_mul_of_pos_right _ (Nat.one_le_of_lt k.factorial_pos)

theorem lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n ! := by
  have : 0 < n := by omega
  have hn : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›, factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (pred n).succ_pos).2
    ((Nat.lt_of_lt_of_le hn (self_le_factorial _)))

theorem add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
    i + (n + 1)! < (i + n + 1)! := by
  rw [factorial_succ (i + _), Nat.add_mul, Nat.one_mul]
  have := (i + n).self_le_factorial
  refine Nat.add_lt_add_of_lt_of_le (Nat.lt_of_le_of_lt ?_ ((Nat.lt_mul_iff_one_lt_right ?_).2 ?_))
    (factorial_le ?_) <;> omega

theorem add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
    i + n ! < (i + n)! := by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi

theorem add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) :
    i + (n + 1)! ≤ (i + (n + 1))! := by
  cases (le_or_gt (2 : ℕ) i)
  · rw [← Nat.add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← Nat.add_assoc, factorial_succ (1 + n), Nat.add_mul, Nat.one_mul, Nat.add_comm 1 n,
        Nat.add_le_add_iff_right]
      exact Nat.mul_pos n.succ_pos n.succ.factorial_pos
    | succ (succ n) => contradiction

theorem add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) : i + n ! ≤ (i + n)! := by
  rcases n1 with - | @h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h

theorem factorial_mul_pow_sub_le_factorial {n m : ℕ} (hnm : n ≤ m) : n ! * n ^ (m - n) ≤ m ! := by
  calc
    _ ≤ n ! * (n + 1) ^ (m - n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
    _ ≤ _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)

lemma factorial_le_pow : ∀ n, n ! ≤ n ^ n
  | 0 => le_refl _
  | n + 1 =>
    calc
      _ ≤ (n + 1) * n ^ n := Nat.mul_le_mul_left _ n.factorial_le_pow
      _ ≤ (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
      _ = _ := by rw [pow_succ']

end Factorial

/-! ### Ascending and descending factorials -/


section AscFactorial

/-- `n.ascFactorial k = n (n + 1) ⋯ (n + k - 1)`. This is closely related to `ascPochhammer`, but
much less general. -/
def ascFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n + k) * ascFactorial n k

@[simp]
theorem ascFactorial_zero (n : ℕ) : n.ascFactorial 0 = 1 :=
  rfl

theorem ascFactorial_succ {n k : ℕ} : n.ascFactorial k.succ = (n + k) * n.ascFactorial k :=
  rfl

theorem zero_ascFactorial : ∀ (k : ℕ), (0 : ℕ).ascFactorial k.succ = 0
  | 0 => by
    rw [ascFactorial_succ, ascFactorial_zero, Nat.zero_add, Nat.zero_mul]
  | (k + 1) => by
    rw [ascFactorial_succ, zero_ascFactorial k, Nat.mul_zero]

@[simp]
theorem one_ascFactorial : ∀ (k : ℕ), (1 : ℕ).ascFactorial k = k.factorial
  | 0 => ascFactorial_zero 1
  | (k + 1) => by
    rw [ascFactorial_succ, one_ascFactorial k, Nat.add_comm, factorial_succ]

theorem succ_ascFactorial (n : ℕ) :
    ∀ k, n * n.succ.ascFactorial k = (n + k) * n.ascFactorial k
  | 0 => by rw [Nat.add_zero, ascFactorial_zero, ascFactorial_zero]
  | k + 1 => by rw [ascFactorial, Nat.mul_left_comm, succ_ascFactorial n k, ascFactorial, succ_add,
    ← Nat.add_assoc]

/-- `(n + 1).ascFactorial k = (n + k) ! / n !` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. -/
theorem factorial_mul_ascFactorial (n : ℕ) : ∀ k, n ! * (n + 1).ascFactorial k = (n + k)!
  | 0 => by rw [ascFactorial_zero, Nat.add_zero, Nat.mul_one]
  | k + 1 => by
    rw [ascFactorial_succ, ← Nat.add_assoc, factorial_succ, Nat.mul_comm (n + 1 + k),
      ← Nat.mul_assoc, factorial_mul_ascFactorial n k, Nat.mul_comm, Nat.add_right_comm]

/-- `n.ascFactorial k = (n + k - 1)! / (n - 1)!` for `n > 0` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. Consider using
`factorial_mul_ascFactorial` to avoid complications of ℕ-subtraction. -/
theorem factorial_mul_ascFactorial' (n k : ℕ) (h : 0 < n) :
    (n - 1)! * n.ascFactorial k = (n + k - 1)! := by
  rw [Nat.sub_add_comm h, Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one, factorial_mul_ascFactorial]

theorem ascFactorial_mul_ascFactorial (n l k : ℕ) :
    n.ascFactorial l * (n + l).ascFactorial k = n.ascFactorial (l + k) := by
  cases n with
  | zero =>
    cases l
    · simp only [ascFactorial_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
    · simp only [Nat.add_right_comm, zero_ascFactorial, Nat.zero_add, Nat.zero_mul]
  | succ n' =>
    apply Nat.mul_left_cancel (factorial_pos n')
    simp only [Nat.add_assoc, ← Nat.mul_assoc, factorial_mul_ascFactorial]
    rw [Nat.add_comm 1 l, ← Nat.add_assoc, factorial_mul_ascFactorial, Nat.add_assoc]

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial` if you can. ℕ-division isn't worth it. -/
theorem ascFactorial_eq_div (n k : ℕ) : (n + 1).ascFactorial k = (n + k)! / n ! :=
  Nat.eq_div_of_mul_eq_right n.factorial_ne_zero (factorial_mul_ascFactorial _ _)

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial'` if you can. ℕ-division isn't worth it. -/
theorem ascFactorial_eq_div' (n k : ℕ) (h : 0 < n) :
    n.ascFactorial k = (n + k - 1)! / (n - 1)! :=
  Nat.eq_div_of_mul_eq_right (n - 1).factorial_ne_zero (factorial_mul_ascFactorial' _ _ h)

theorem ascFactorial_of_sub {n k : ℕ} :
    (n - k) * (n - k + 1).ascFactorial k = (n - k).ascFactorial (k + 1) := by
  rw [succ_ascFactorial, ascFactorial_succ]

theorem pow_succ_le_ascFactorial (n : ℕ) : ∀ k : ℕ, n ^ k ≤ n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm, ascFactorial_succ, ← succ_ascFactorial]
    exact Nat.mul_le_mul (Nat.le_refl n)
      (Nat.le_trans (Nat.pow_le_pow_left (le_succ n) k) (pow_succ_le_ascFactorial n.succ k))

theorem pow_lt_ascFactorial' (n k : ℕ) : (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2) := by
  rw [Nat.pow_succ, ascFactorial, Nat.mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le' (Nat.lt_add_of_pos_right k.succ_pos)
    (pow_succ_le_ascFactorial n.succ _) (Nat.pow_pos n.succ_pos)

theorem pow_lt_ascFactorial (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1) ^ k < (n + 1).ascFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => pow_lt_ascFactorial' n k

theorem ascFactorial_le_pow_add (n : ℕ) : ∀ k : ℕ, (n + 1).ascFactorial k ≤ (n + k) ^ k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [ascFactorial_succ, Nat.pow_succ, Nat.mul_comm, ← Nat.add_assoc, Nat.add_right_comm n 1 k]
    exact Nat.mul_le_mul_right _
      (Nat.le_trans (ascFactorial_le_pow_add _ k) (Nat.pow_le_pow_left (le_succ _) _))

theorem ascFactorial_lt_pow_add (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1).ascFactorial k < (n + k) ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [Nat.pow_succ, Nat.mul_comm, ascFactorial_succ, succ_add_eq_add_succ n (k + 1)]
    exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) (Nat.lt_of_le_of_lt (ascFactorial_le_pow_add n _)
      (Nat.pow_lt_pow_left (Nat.lt_succ_self _) k.succ_ne_zero)) (succ_pos _)

theorem ascFactorial_pos (n k : ℕ) : 0 < (n + 1).ascFactorial k :=
  Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)

end AscFactorial

section DescFactorial

/-- `n.descFactorial k = n! / (n - k)!` (as seen in `Nat.descFactorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. This is closely
related to `descPochhammer`, but much less general. -/
def descFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k

@[simp]
theorem descFactorial_zero (n : ℕ) : n.descFactorial 0 = 1 :=
  rfl

@[simp]
theorem descFactorial_succ (n k : ℕ) : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
  rfl

theorem zero_descFactorial_succ (k : ℕ) : (0 : ℕ).descFactorial (k + 1) = 0 := by
  rw [descFactorial_succ, Nat.zero_sub, Nat.zero_mul]

theorem descFactorial_one (n : ℕ) : n.descFactorial 1 = n := by simp

theorem succ_descFactorial_succ (n : ℕ) :
    ∀ k : ℕ, (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
  | 0 => by rw [descFactorial_zero, descFactorial_one, Nat.mul_one]
  | succ k => by
    rw [descFactorial_succ, succ_descFactorial_succ _ k, descFactorial_succ, succ_sub_succ,
      Nat.mul_left_comm]

theorem succ_descFactorial (n : ℕ) :
    ∀ k, (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFactorial k
  | 0 => by rw [Nat.sub_zero, descFactorial_zero, descFactorial_zero]
  | k + 1 => by
    rw [descFactorial, succ_descFactorial _ k, descFactorial_succ, succ_sub_succ, Nat.mul_left_comm]

theorem descFactorial_self : ∀ n : ℕ, n.descFactorial n = n !
  | 0 => by rw [descFactorial_zero, factorial_zero]
  | succ n => by rw [succ_descFactorial_succ, descFactorial_self n, factorial_succ]

@[simp]
theorem descFactorial_eq_zero_iff_lt {n : ℕ} : ∀ {k : ℕ}, n.descFactorial k = 0 ↔ n < k
  | 0 => by simp only [descFactorial_zero, Nat.one_ne_zero, Nat.not_lt_zero]
  | succ k => by
    rw [descFactorial_succ, mul_eq_zero, descFactorial_eq_zero_iff_lt, Nat.lt_succ_iff,
      Nat.sub_eq_zero_iff_le, Nat.lt_iff_le_and_ne, or_iff_left_iff_imp, and_imp]
    exact fun h _ => h

@[simp]
lemma descFactorial_pos {n k : ℕ} : 0 < n.descFactorial k ↔ k ≤ n := by simp [Nat.pos_iff_ne_zero]

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt

theorem add_descFactorial_eq_ascFactorial (n : ℕ) : ∀ k : ℕ,
    (n + k).descFactorial k = (n + 1).ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [Nat.add_succ, succ_descFactorial_succ, ascFactorial_succ,
      add_descFactorial_eq_ascFactorial _ k, Nat.add_right_comm]

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
  | n, 0 => fun _ => by rw [descFactorial_zero, Nat.mul_one, Nat.sub_zero]
  | 0, succ k => fun h => by
    exfalso
    exact not_succ_le_zero k h
  | succ n, succ k => fun h => by
    rw [succ_descFactorial_succ, succ_sub_succ, ← Nat.mul_assoc, Nat.mul_comm (n - k)!,
      Nat.mul_assoc, factorial_mul_descFactorial (Nat.succ_le_succ_iff.1 h), factorial_succ]

theorem descFactorial_mul_descFactorial {k m n : ℕ} (hkm : k ≤ m) :
    (n - k).descFactorial (m - k) * n.descFactorial k = n.descFactorial m := by
  by_cases hmn : m ≤ n
  · apply Nat.mul_left_cancel (n - m).factorial_pos
    rw [factorial_mul_descFactorial hmn, show n - m = (n - k) - (m - k) by omega, ← Nat.mul_assoc,
      factorial_mul_descFactorial (show m - k ≤ n - k by omega),
      factorial_mul_descFactorial (le_trans hkm hmn)]
  · rw [descFactorial_eq_zero_iff_lt.mpr (show n < m by omega)]
    by_cases hkn : k ≤ n
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n - k < m - k by omega), Nat.zero_mul]
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n < k by omega), Nat.mul_zero]

/-- Avoid in favor of `Nat.factorial_mul_descFactorial` if you can. ℕ-division isn't worth it. -/
theorem descFactorial_eq_div {n k : ℕ} (h : k ≤ n) : n.descFactorial k = n ! / (n - k)! := by
  apply Nat.mul_left_cancel (n - k).factorial_pos
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm

theorem descFactorial_le (n : ℕ) {k m : ℕ} (h : k ≤ m) :
    k.descFactorial n ≤ m.descFactorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [descFactorial_succ, descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h n) ih

theorem pow_sub_le_descFactorial (n : ℕ) : ∀ k : ℕ, (n + 1 - k) ^ k ≤ n.descFactorial k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, Nat.pow_succ, succ_sub_succ, Nat.mul_comm]
    apply Nat.mul_le_mul_left
    exact (le_trans (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) k)
      (pow_sub_le_descFactorial n k))

theorem pow_sub_lt_descFactorial' {n : ℕ} :
    ∀ {k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
  | 0, h => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.pow_one, descFactorial_one]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.sub_pos_of_lt h)
  | k + 1, h => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.sub_pos_of_lt h)
    refine Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) _) ?_
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' (Nat.le_trans (le_succ _) h)

theorem pow_sub_lt_descFactorial {n : ℕ} :
    ∀ {k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k) ^ k < n.descFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ h => by
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' h

theorem descFactorial_le_pow (n : ℕ) : ∀ k : ℕ, n.descFactorial k ≤ n ^ k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.mul_comm _ n]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (descFactorial_le_pow _ k)

theorem descFactorial_lt_pow {n : ℕ} (hn : n ≠ 0) : ∀ {k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [descFactorial_succ, pow_succ', Nat.mul_comm, Nat.mul_comm n]
    exact Nat.mul_lt_mul_of_le_of_lt (descFactorial_le_pow _ _) (by omega) (Nat.pow_pos <| by omega)

end DescFactorial

lemma factorial_two_mul_le (n : ℕ) : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [Nat.two_mul, ← factorial_mul_ascFactorial, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (ascFactorial_le_pow_add _ _)

lemma two_pow_mul_factorial_le_factorial_two_mul (n : ℕ) : 2 ^ n * n ! ≤ (2 * n)! := by
  obtain _ | n := n
  · simp
  rw [Nat.mul_comm, Nat.two_mul]
  calc
    _ ≤ (n + 1)! * (n + 2) ^ (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_add_left _ _) _)
    _ ≤ _ := Nat.factorial_mul_pow_le_factorial


/-!
# Factorial via binary splitting.

We prove this is equal to the standard factorial and mark it `@[csimp]`.

We could proceed further, with either Legendre or Luschny methods.
-/

/-!
This is the highest factorial I can `#eval` using the naive implementation without a stack overflow:
```
/-- info: 114716 -/
#guard_msgs in
#eval 9718 ! |>.log2
```

We could implement a tail-recursive version (or just use `Nat.fold`),
but instead let's jump straight to binary splitting.
-/

/-- Factorial implemented using binary splitting.

While this still performs the same number of multiplications,
the big-integer operands to each are much smaller. -/
def factorialBinarySplitting (n : Nat) : Nat :=
  if _ : n = 0 then 1 else prodRange 1 (n + 1)
where
  /--
  `prodRange lo hi` is the product of the range `lo` to `hi` (exclusive),
  computed by binary splitting.
  -/
  prodRange (lo hi : Nat) (h : lo < hi := by grind) : Nat :=
    if _ : hi = lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      prodRange lo mid * prodRange mid hi

theorem factorialBinarySplitting.factorial_mul_prodRange (lo hi : Nat) (h : lo < hi) :
    lo ! * prodRange (lo + 1) (hi + 1) = hi ! := by
  rw [prodRange]
  split
  · grind [factorial_succ]
  · dsimp only
    rw [← Nat.mul_assoc]
    simp_rw [show (lo + 1 + (hi + 1)) / 2 = (lo + hi) / 2 + 1 by grind]
    rw [factorial_mul_prodRange, factorial_mul_prodRange]
    all_goals grind

@[csimp]
theorem factorialBinarySplitting_eq_factorial : @factorial = @factorialBinarySplitting := by
  ext n
  by_cases h : n = 0
  · simp [h, factorialBinarySplitting]
  · rw [factorialBinarySplitting, ← factorialBinarySplitting.factorial_mul_prodRange 0 n (by grind)]
    simp [h]

/-!
We are now limited by time, not stack space,
and this is much faster than even the tail-recursive version.

```
#time -- Less than 1s. (Tail-recursive version takes longer for `(10^5) !`.)
#eval (10^6) ! |>.log2
```
-/


end Nat
