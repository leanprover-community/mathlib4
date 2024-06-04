/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Kyle Miller, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

#align_import data.nat.fib from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Fibonacci Numbers

This file defines the fibonacci series, proves results about it and introduces
methods to compute it quickly.
-/

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `Nat.fib` returns the stream of Fibonacci numbers.

## Main Statements

- `Nat.fib_add_two`: shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `Nat.fib_gcd`: `fib n` is a strong divisibility sequence.
- `Nat.fib_succ_eq_sum_choose`: `fib` is given by the sum of `Nat.choose` along an antidiagonal.
- `Nat.fib_succ_eq_succ_sum`: shows that `F₀ + F₁ + ⋯ + Fₙ = Fₙ₊₂ - 1`.
- `Nat.fib_two_mul` and `Nat.fib_two_mul_add_one` are the basis for an efficient algorithm to
  compute `fib` (see `Nat.fastFib`). There are `bit0`/`bit1` variants of these can be used to
  simplify `fib` expressions: `simp only [Nat.fib_bit0, Nat.fib_bit1, Nat.fib_bit0_succ,
  Nat.fib_bit1_succ, Nat.fib_one, Nat.fib_two]`.

## Implementation Notes

For efficiency purposes, the sequence is defined using `Stream.iterate`.

## Tags

fib, fibonacci
-/

namespace Nat



/-- Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/

-- Porting note: Lean cannot find pp_nodot at the time of this port.
-- @[pp_nodot]
def fib (n : ℕ) : ℕ :=
  ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst
#align nat.fib Nat.fib

@[simp]
theorem fib_zero : fib 0 = 0 :=
  rfl
#align nat.fib_zero Nat.fib_zero

@[simp]
theorem fib_one : fib 1 = 1 :=
  rfl
#align nat.fib_one Nat.fib_one

@[simp]
theorem fib_two : fib 2 = 1 :=
  rfl
#align nat.fib_two Nat.fib_two

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
theorem fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  simp [fib, Function.iterate_succ_apply']
#align nat.fib_add_two Nat.fib_add_two

lemma fib_add_one : ∀ {n}, n ≠ 0 → fib (n + 1) = fib (n - 1) + fib n
  | _n + 1, _ => fib_add_two

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by cases n <;> simp [fib_add_two]
#align nat.fib_le_fib_succ Nat.fib_le_fib_succ

@[mono]
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ fun _ => fib_le_fib_succ
#align nat.fib_mono Nat.fib_mono

@[simp] lemma fib_eq_zero : ∀ {n}, fib n = 0 ↔ n = 0
| 0 => Iff.rfl
| 1 => Iff.rfl
| n + 2 => by simp [fib_add_two, fib_eq_zero]

@[simp] lemma fib_pos {n : ℕ} : 0 < fib n ↔ 0 < n := by simp [pos_iff_ne_zero]
#align nat.fib_pos Nat.fib_pos

theorem fib_add_two_sub_fib_add_one {n : ℕ} : fib (n + 2) - fib (n + 1) = fib n := by
  rw [fib_add_two, add_tsub_cancel_right]
#align nat.fib_add_two_sub_fib_add_one Nat.fib_add_two_sub_fib_add_one

theorem fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) := by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  rw [← tsub_pos_iff_lt, add_comm 2, add_right_comm, fib_add_two, add_tsub_cancel_right, fib_pos]
  exact succ_pos n
#align nat.fib_lt_fib_succ Nat.fib_lt_fib_succ

/-- `fib (n + 2)` is strictly monotone. -/
theorem fib_add_two_strictMono : StrictMono fun n => fib (n + 2) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [add_right_comm]
  exact fib_lt_fib_succ (self_le_add_left _ _)
#align nat.fib_add_two_strict_mono Nat.fib_add_two_strictMono

lemma fib_strictMonoOn : StrictMonoOn fib (Set.Ici 2)
  | _m + 2, _, _n + 2, _, hmn => fib_add_two_strictMono <| lt_of_add_lt_add_right hmn

lemma fib_lt_fib {m : ℕ} (hm : 2 ≤ m) : ∀ {n}, fib m < fib n ↔ m < n
  | 0 => by simp [hm]
  | 1 => by simp [hm]
  | n + 2 => fib_strictMonoOn.lt_iff_lt hm <| by simp

theorem le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n := by
  induction' five_le_n with n five_le_n IH
  ·-- 5 ≤ fib 5
    rfl
  · -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc
      n ≤ fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)
#align nat.le_fib_self Nat.le_fib_self

lemma le_fib_add_one : ∀ n, n ≤ fib n + 1
  | 0 => zero_le_one
  | 1 => one_le_two
  | 2 => le_rfl
  | 3 => le_rfl
  | 4 => le_rfl
  | _n + 5 => (le_fib_self le_add_self).trans <| le_succ _

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction' n with n ih
  · simp
  · rw [fib_add_two]
    simp only [coprime_add_self_right]
    simp [Coprime, ih.symm]
#align nat.fib_coprime_fib_succ Nat.fib_coprime_fib_succ

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction' n with n ih generalizing m
  · simp
  · specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, succ_eq_add_one, ih]
    ring
#align nat.fib_add Nat.fib_add

theorem fib_two_mul (n : ℕ) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) := by
  cases n
  · simp
  · rw [two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    simp only [← add_assoc, add_tsub_cancel_right]
    ring
#align nat.fib_two_mul Nat.fib_two_mul

theorem fib_two_mul_add_one (n : ℕ) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [two_mul, fib_add]
  ring
#align nat.fib_two_mul_add_one Nat.fib_two_mul_add_one

theorem fib_two_mul_add_two (n : ℕ) :
    fib (2 * n + 2) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [fib_add_two, fib_two_mul, fib_two_mul_add_one]
  -- Porting note: A bunch of issues similar to [this zulip thread](https://github.com/leanprover-community/mathlib4/pull/1576) with `zify`
  have : fib n ≤ 2 * fib (n + 1) :=
    le_trans fib_le_fib_succ (mul_comm 2 _ ▸ Nat.le_mul_of_pos_right _ two_pos)
  zify [this]
  ring

section deprecated

set_option linter.deprecated false

theorem fib_bit0 (n : ℕ) : fib (bit0 n) = fib n * (2 * fib (n + 1) - fib n) := by
  rw [bit0_eq_two_mul, fib_two_mul]
#align nat.fib_bit0 Nat.fib_bit0

theorem fib_bit1 (n : ℕ) : fib (bit1 n) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [Nat.bit1_eq_succ_bit0, bit0_eq_two_mul, fib_two_mul_add_one]
#align nat.fib_bit1 Nat.fib_bit1

theorem fib_bit0_succ (n : ℕ) : fib (bit0 n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 :=
  fib_bit1 n
#align nat.fib_bit0_succ Nat.fib_bit0_succ

theorem fib_bit1_succ (n : ℕ) : fib (bit1 n + 1) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [Nat.bit1_eq_succ_bit0, bit0_eq_two_mul, fib_two_mul_add_two]
#align nat.fib_bit1_succ Nat.fib_bit1_succ

end deprecated

/-- Computes `(Nat.fib n, Nat.fib (n + 1))` using the binary representation of `n`.
Supports `Nat.fastFib`. -/
def fastFibAux : ℕ → ℕ × ℕ :=
  Nat.binaryRec (fib 0, fib 1) fun b _ p =>
    if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
    else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)
#align nat.fast_fib_aux Nat.fastFibAux

/-- Computes `Nat.fib n` using the binary representation of `n`.
Proved to be equal to `Nat.fib` in `Nat.fast_fib_eq`. -/
def fastFib (n : ℕ) : ℕ :=
  (fastFibAux n).1
#align nat.fast_fib Nat.fastFib

theorem fast_fib_aux_bit_ff (n : ℕ) :
    fastFibAux (bit false n) =
      let p := fastFibAux n
      (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2) := by
  rw [fastFibAux, binaryRec_eq]
  · rfl
  · simp
#align nat.fast_fib_aux_bit_ff Nat.fast_fib_aux_bit_ff

theorem fast_fib_aux_bit_tt (n : ℕ) :
    fastFibAux (bit true n) =
      let p := fastFibAux n
      (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2)) := by
  rw [fastFibAux, binaryRec_eq]
  · rfl
  · simp
#align nat.fast_fib_aux_bit_tt Nat.fast_fib_aux_bit_tt

theorem fast_fib_aux_eq (n : ℕ) : fastFibAux n = (fib n, fib (n + 1)) := by
  apply Nat.binaryRec _ (fun b n' ih => _) n
  · simp [fastFibAux]
  · intro b
    intro n'
    intro ih
    cases b <;>
          simp only [fast_fib_aux_bit_ff, fast_fib_aux_bit_tt, congr_arg Prod.fst ih,
            congr_arg Prod.snd ih, Prod.mk.inj_iff] <;>
          simp [bit, fib_bit0, fib_bit1, fib_bit0_succ, fib_bit1_succ]
#align nat.fast_fib_aux_eq Nat.fast_fib_aux_eq

theorem fast_fib_eq (n : ℕ) : fastFib n = fib n := by rw [fastFib, fast_fib_aux_eq]
#align nat.fast_fib_eq Nat.fast_fib_eq

theorem gcd_fib_add_self (m n : ℕ) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h]
    simp
  replace h := Nat.succ_pred_eq_of_pos h; rw [← h, succ_eq_add_one]
  calc
    gcd (fib m) (fib (n.pred + 1 + m)) =
        gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
        rw [← fib_add n.pred _]
        ring_nf
    _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
        rw [add_comm, gcd_add_mul_right_right (fib m) _ (fib n.pred)]
    _ = gcd (fib m) (fib (n.pred + 1)) :=
      Coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (Coprime.symm (fib_coprime_fib_succ m))
#align nat.gcd_fib_add_self Nat.gcd_fib_add_self

theorem gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)
  | 0 => by simp
  | k + 1 => by
    rw [← gcd_fib_add_mul_self m n k,
      add_mul,
      ← add_assoc,
      one_mul,
      gcd_fib_add_self _ _]
#align nat.gcd_fib_add_mul_self Nat.gcd_fib_add_mul_self

/-- `fib n` is a strong divisibility sequence,
  see https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
theorem fib_gcd (m n : ℕ) : fib (gcd m n) = gcd (fib m) (fib n) := by
  induction m, n using Nat.gcd.induction with
  | H0 => simp
  | H1 m n _ h' =>
    rw [← gcd_rec m n] at h'
    conv_rhs => rw [← mod_add_div' n m]
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]
#align nat.fib_gcd Nat.fib_gcd

theorem fib_dvd (m n : ℕ) (h : m ∣ n) : fib m ∣ fib n := by
  rwa [gcd_eq_left_iff_dvd, ← fib_gcd, gcd_eq_left_iff_dvd.mp]
#align nat.fib_dvd Nat.fib_dvd

theorem fib_succ_eq_sum_choose :
    ∀ n : ℕ, fib (n + 1) = ∑ p ∈ Finset.antidiagonal n, choose p.1 p.2 :=
  twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two, h1, h2, Finset.Nat.antidiagonal_succ_succ', Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]
#align nat.fib_succ_eq_sum_choose Nat.fib_succ_eq_sum_choose

theorem fib_succ_eq_succ_sum (n : ℕ) : fib (n + 1) = (∑ k ∈ Finset.range n, fib k) + 1 := by
  induction' n with n ih
  · simp
  · calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k ∈ Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k ∈ Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]
#align nat.fib_succ_eq_succ_sum Nat.fib_succ_eq_succ_sum

end Nat
