/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Kyle Miller, Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Bitwise
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Basic
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

open BigOperators

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
  -- 🎉 no goals
#align nat.fib_add_two Nat.fib_add_two

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by cases n <;> simp [fib_add_two]
                                                            -- ⊢ fib zero ≤ fib (zero + 1)
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
#align nat.fib_le_fib_succ Nat.fib_le_fib_succ

@[mono]
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ fun _ => fib_le_fib_succ
#align nat.fib_mono Nat.fib_mono

theorem fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n :=
  calc
    0 < fib 1 := by decide
                    -- 🎉 no goals
    _ ≤ fib n := fib_mono n_pos
#align nat.fib_pos Nat.fib_pos

theorem fib_add_two_sub_fib_add_one {n : ℕ} : fib (n + 2) - fib (n + 1) = fib n := by
  rw [fib_add_two, add_tsub_cancel_right]
  -- 🎉 no goals
#align nat.fib_add_two_sub_fib_add_one Nat.fib_add_two_sub_fib_add_one

theorem fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) := by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  -- ⊢ fib (2 + n) < fib (2 + n + 1)
  rw [← tsub_pos_iff_lt, add_comm 2, fib_add_two_sub_fib_add_one]
  -- ⊢ 0 < fib (n + 1)
  apply fib_pos (succ_pos n)
  -- 🎉 no goals
#align nat.fib_lt_fib_succ Nat.fib_lt_fib_succ

/-- `fib (n + 2)` is strictly monotone. -/
theorem fib_add_two_strictMono : StrictMono fun n => fib (n + 2) := by
  refine' strictMono_nat_of_lt_succ fun n => _
  -- ⊢ fib (n + 2) < fib (n + 1 + 2)
  rw [add_right_comm]
  -- ⊢ fib (n + 2) < fib (n + 2 + 1)
  exact fib_lt_fib_succ (self_le_add_left _ _)
  -- 🎉 no goals
#align nat.fib_add_two_strict_mono Nat.fib_add_two_strictMono

theorem le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n := by
  induction' five_le_n with n five_le_n IH
  -- ⊢ 5 ≤ fib 5
  ·-- 5 ≤ fib 5
    rfl
    -- 🎉 no goals
  · -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    -- ⊢ n < fib (succ n)
    calc
      n ≤ fib n := IH
      _ < fib (n + 1) := fib_lt_fib_succ (le_trans (by decide) five_le_n)
#align nat.le_fib_self Nat.le_fib_self

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : Nat.coprime (fib n) (fib (n + 1)) := by
  induction' n with n ih
  -- ⊢ coprime (fib zero) (fib (zero + 1))
  · simp
    -- 🎉 no goals
  · rw [fib_add_two]
    -- ⊢ coprime (fib (succ n)) (fib n + fib (n + 1))
    simp only [coprime_add_self_right]
    -- ⊢ coprime (fib (succ n)) (fib n)
    simp [coprime, ih.symm]
    -- 🎉 no goals
#align nat.fib_coprime_fib_succ Nat.fib_coprime_fib_succ

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction' n with n ih generalizing m
  -- ⊢ fib (m + zero + 1) = fib m * fib zero + fib (m + 1) * fib (zero + 1)
  · simp
    -- 🎉 no goals
  · intros
    -- ⊢ fib (m + succ n + 1) = fib m * fib (succ n) + fib (m + 1) * fib (succ n + 1)
    specialize ih (m + 1)
    -- ⊢ fib (m + succ n + 1) = fib m * fib (succ n) + fib (m + 1) * fib (succ n + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    -- ⊢ fib (m + succ n + 1) = fib m * fib (succ n) + fib (m + 1) * fib (succ n + 1)
    simp only [fib_add_two, ih]
    -- ⊢ fib (m + 1) * fib n + (fib m + fib (m + 1)) * fib (n + 1) = fib m * fib (suc …
    ring
    -- 🎉 no goals
#align nat.fib_add Nat.fib_add

theorem fib_two_mul (n : ℕ) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) := by
  cases n
  -- ⊢ fib (2 * zero) = fib zero * (2 * fib (zero + 1) - fib zero)
  · simp
    -- 🎉 no goals
  · rw [Nat.succ_eq_add_one, two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    -- ⊢ fib (n✝ + 1) * fib n✝ + (fib n✝ + fib (n✝ + 1)) * fib (n✝ + 1) = fib (n✝ + 1 …
    simp only [← add_assoc, add_tsub_cancel_right]
    -- ⊢ fib (n✝ + 1) * fib n✝ + (fib n✝ + fib (n✝ + 1)) * fib (n✝ + 1) = fib (n✝ + 1 …
    ring
    -- 🎉 no goals
#align nat.fib_two_mul Nat.fib_two_mul

theorem fib_two_mul_add_one (n : ℕ) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [two_mul, fib_add]
  -- ⊢ fib n * fib n + fib (n + 1) * fib (n + 1) = fib (n + 1) ^ 2 + fib n ^ 2
  ring
  -- 🎉 no goals
#align nat.fib_two_mul_add_one Nat.fib_two_mul_add_one

theorem fib_two_mul_add_two (n : ℕ) :
    fib (2 * n + 2) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [fib_add_two, fib_two_mul, fib_two_mul_add_one]
  -- ⊢ fib n * (2 * fib (n + 1) - fib n) + (fib (n + 1) ^ 2 + fib n ^ 2) = fib (n + …
  -- porting note: A bunch of issues similar to [this zulip thread](https://github.com/leanprover-community/mathlib4/pull/1576) with `zify`
  have : fib n ≤ 2 * fib (n + 1) :=
    le_trans (fib_le_fib_succ) (mul_comm 2 _ ▸ le_mul_of_pos_right two_pos)
  zify [this]
  -- ⊢ ↑(fib n) * (2 * ↑(fib (n + 1)) - ↑(fib n)) + (↑(fib (n + 1)) ^ 2 + ↑(fib n)  …
  ring
  -- 🎉 no goals

section deprecated

set_option linter.deprecated false

theorem fib_bit0 (n : ℕ) : fib (bit0 n) = fib n * (2 * fib (n + 1) - fib n) := by
  rw [bit0_eq_two_mul, fib_two_mul]
  -- 🎉 no goals
#align nat.fib_bit0 Nat.fib_bit0

theorem fib_bit1 (n : ℕ) : fib (bit1 n) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [Nat.bit1_eq_succ_bit0, bit0_eq_two_mul, fib_two_mul_add_one]
  -- 🎉 no goals
#align nat.fib_bit1 Nat.fib_bit1

theorem fib_bit0_succ (n : ℕ) : fib (bit0 n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 :=
  fib_bit1 n
#align nat.fib_bit0_succ Nat.fib_bit0_succ

theorem fib_bit1_succ (n : ℕ) : fib (bit1 n + 1) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [Nat.bit1_eq_succ_bit0, bit0_eq_two_mul, fib_two_mul_add_two]
  -- 🎉 no goals
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
  -- ⊢ (if false = true then ((binaryRec (fib 0, fib 1) (fun b x p => if b = true t …
  · rfl
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align nat.fast_fib_aux_bit_ff Nat.fast_fib_aux_bit_ff

theorem fast_fib_aux_bit_tt (n : ℕ) :
    fastFibAux (bit true n) =
      let p := fastFibAux n
      (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2)) := by
  rw [fastFibAux, binaryRec_eq]
  -- ⊢ (if true = true then ((binaryRec (fib 0, fib 1) (fun b x p => if b = true th …
  · rfl
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align nat.fast_fib_aux_bit_tt Nat.fast_fib_aux_bit_tt

theorem fast_fib_aux_eq (n : ℕ) : fastFibAux n = (fib n, fib (n + 1)) := by
  apply Nat.binaryRec _ (fun b n' ih => _) n
  -- ⊢ fastFibAux 0 = (fib 0, fib (0 + 1))
  · simp [fastFibAux]
    -- 🎉 no goals
  · intro b
    -- ⊢ ∀ (n' : ℕ), fastFibAux n' = (fib n', fib (n' + 1)) → fastFibAux (bit b n') = …
    intro n'
    -- ⊢ fastFibAux n' = (fib n', fib (n' + 1)) → fastFibAux (bit b n') = (fib (bit b …
    intro ih
    -- ⊢ fastFibAux (bit b n') = (fib (bit b n'), fib (bit b n' + 1))
    cases b <;>
    -- ⊢ fastFibAux (bit false n') = (fib (bit false n'), fib (bit false n' + 1))
          simp only [fast_fib_aux_bit_ff, fast_fib_aux_bit_tt, congr_arg Prod.fst ih,
            congr_arg Prod.snd ih, Prod.mk.inj_iff] <;>
          simp [bit, fib_bit0, fib_bit1, fib_bit0_succ, fib_bit1_succ]
          -- 🎉 no goals
          -- 🎉 no goals
#align nat.fast_fib_aux_eq Nat.fast_fib_aux_eq

theorem fast_fib_eq (n : ℕ) : fastFib n = fib n := by rw [fastFib, fast_fib_aux_eq]
                                                      -- 🎉 no goals
#align nat.fast_fib_eq Nat.fast_fib_eq

theorem gcd_fib_add_self (m n : ℕ) : gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n) := by
  cases' Nat.eq_zero_or_pos n with h h
  -- ⊢ gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)
  · rw [h]
    -- ⊢ gcd (fib m) (fib (0 + m)) = gcd (fib m) (fib 0)
    simp
    -- 🎉 no goals
  replace h := Nat.succ_pred_eq_of_pos h; rw [← h, succ_eq_add_one]
  -- ⊢ gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)
                                          -- ⊢ gcd (fib m) (fib (pred n + 1 + m)) = gcd (fib m) (fib (pred n + 1))
  calc
    gcd (fib m) (fib (n.pred + 1 + m)) =
        gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
        rw [← fib_add n.pred _]
        ring_nf
    _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
        rw [add_comm, gcd_add_mul_right_right (fib m) _ (fib n.pred)]
    _ = gcd (fib m) (fib (n.pred + 1)) :=
      coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (coprime.symm (fib_coprime_fib_succ m))
#align nat.gcd_fib_add_self Nat.gcd_fib_add_self

theorem gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)
  | 0 => by simp
            -- 🎉 no goals
  | k + 1 => by
    rw [←gcd_fib_add_mul_self m n k,
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
  -- 🎉 no goals
#align nat.fib_dvd Nat.fib_dvd

theorem fib_succ_eq_sum_choose :
    ∀ n : ℕ, fib (n + 1) = ∑ p in Finset.Nat.antidiagonal n, choose p.1 p.2 :=
  twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two, h1, h2, Finset.Nat.antidiagonal_succ_succ', Finset.Nat.antidiagonal_succ']
    -- ⊢ ∑ p in Finset.Nat.antidiagonal n, choose p.fst p.snd + ∑ p in Finset.cons (n …
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]
    -- 🎉 no goals
#align nat.fib_succ_eq_sum_choose Nat.fib_succ_eq_sum_choose

theorem fib_succ_eq_succ_sum (n : ℕ) : fib (n + 1) = (∑ k in Finset.range n, fib k) + 1 := by
  induction' n with n ih
  -- ⊢ fib (zero + 1) = ∑ k in Finset.range zero, fib k + 1
  · simp
    -- 🎉 no goals
  · calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k in Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k in Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]
#align nat.fib_succ_eq_succ_sum Nat.fib_succ_eq_succ_sum

end Nat
