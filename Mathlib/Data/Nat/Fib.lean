/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann, Kyle Miller, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.fib
! leanprover-community/mathlib commit 92ca63f0fb391a9ca5f22d2409a6080e786d99f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Bitwise
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

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
  (((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n]) (0, 1)).fst
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

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by cases n <;> simp [fib_add_two]
#align nat.fib_le_fib_succ Nat.fib_le_fib_succ

@[mono]
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ fun _ => fib_le_fib_succ
#align nat.fib_mono Nat.fib_mono

theorem fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n :=
  calc
    0 < fib 1 := by decide
    _ ≤ fib n := fib_mono n_pos
#align nat.fib_pos Nat.fib_pos

theorem fib_add_two_sub_fib_add_one {n : ℕ} : fib (n + 2) - fib (n + 1) = fib n := by
  rw [fib_add_two, add_tsub_cancel_right]
#align nat.fib_add_two_sub_fib_add_one Nat.fib_add_two_sub_fib_add_one

theorem fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) := by
  rcases exists_add_of_le hn with ⟨n, rfl⟩
  rw [← tsub_pos_iff_lt, add_comm 2, fib_add_two_sub_fib_add_one]
  apply fib_pos (succ_pos n)
#align nat.fib_lt_fib_succ Nat.fib_lt_fib_succ

/-- `fib (n + 2)` is strictly monotone. -/
theorem fib_add_two_strictMono : StrictMono fun n => fib (n + 2) := by
  refine' strictMono_nat_of_lt_succ fun n => _
  rw [add_right_comm]
  exact fib_lt_fib_succ (self_le_add_left _ _)
#align nat.fib_add_two_strict_mono Nat.fib_add_two_strictMono

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

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : Nat.coprime (fib n) (fib (n + 1)) := by
  induction' n with n ih
  · simp
  · rw [fib_add_two]
    simp only [coprime_add_self_right]
    simp [coprime, ih.symm]
#align nat.fib_coprime_fib_succ Nat.fib_coprime_fib_succ

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction' n with n ih generalizing m
  · simp
  · intros
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring
#align nat.fib_add Nat.fib_add

theorem fib_two_mul (n : ℕ) : fib (2 * n) = fib n * (2 * fib (n + 1) - fib n) := by
  cases n
  · simp
  · rw [Nat.succ_eq_add_one, two_mul, ← add_assoc, fib_add, fib_add_two, two_mul]
    simp only [← add_assoc, add_tsub_cancel_right]
    ring
#align nat.fib_two_mul Nat.fib_two_mul

theorem fib_two_mul_add_one (n : ℕ) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by
  rw [two_mul, fib_add]
  ring
#align nat.fib_two_mul_add_one Nat.fib_two_mul_add_one

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

-- porting note: A bunch of issues similar to [this zulip thread](https://github.com/leanprover-community/mathlib4/pull/1576) with `zify`
theorem fib_bit1_succ (n : ℕ) : fib (bit1 n + 1) = fib (n + 1) * (2 * fib n + fib (n + 1)) := by
  rw [Nat.bit1_eq_succ_bit0, fib_add_two, fib_bit0, fib_bit0_succ]
  have : fib n ≤ 2 * fib (n + 1) :=
    le_trans (fib_le_fib_succ) (mul_comm 2 _ ▸ le_mul_of_pos_right two_pos)
  zify [this]
  ring
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
  cases' Nat.eq_zero_or_pos n with h h
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
      coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (coprime.symm (fib_coprime_fib_succ m))
#align nat.gcd_fib_add_self Nat.gcd_fib_add_self

theorem gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcd (fib m) (fib (n + k * m)) = gcd (fib m) (fib n)
  | 0 => by simp
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
#align nat.fib_dvd Nat.fib_dvd

theorem fib_succ_eq_sum_choose :
    ∀ n : ℕ, fib (n + 1) = ∑ p in Finset.Nat.antidiagonal n, choose p.1 p.2 :=
  two_step_induction rfl rfl fun n h1 h2 => by
    rw [fib_add_two, h1, h2, Finset.Nat.antidiagonal_succ_succ', Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_comm]
#align nat.fib_succ_eq_sum_choose Nat.fib_succ_eq_sum_choose

theorem fib_succ_eq_succ_sum (n : ℕ) : fib (n + 1) = (∑ k in Finset.range n, fib k) + 1 := by
  induction' n with n ih
  · simp
  · calc
      fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      _ = (fib n + ∑ k in Finset.range n, fib k) + 1 := by rw [ih, add_assoc]
      _ = (∑ k in Finset.range (n + 1), fib k) + 1 := by simp [Finset.range_add_one]
#align nat.fib_succ_eq_succ_sum Nat.fib_succ_eq_succ_sum

end Nat

namespace NormNum

open Tactic Nat

/-! ### `norm_num` plugin for `fib`

The `norm_num` plugin uses a strategy parallel to that of `Nat.fastFib`, but it instead
produces proofs of what `Nat.fib` evaluates to.
-/
/-
expected ')'
-/

section deprecated

set_option linter.deprecated false

/-- Auxiliary definition for `prove_fib` plugin. -/
def IsFibAux (n a b : ℕ) :=
  fib n = a ∧ fib (n + 1) = b
#align norm_num.is_fib_aux NormNum.IsFibAux

theorem is_fib_aux_one : IsFibAux 1 1 1 :=
  ⟨fib_one, fib_two⟩
#align norm_num.is_fib_aux_one NormNum.is_fib_aux_one

theorem is_fib_aux_bit0 {n a b c a2 b2 a' b' : ℕ} (H : IsFibAux n a b) (h1 : a + c = bit0 b)
    (h2 : a * c = a') (h3 : a * a = a2) (h4 : b * b = b2) (h5 : a2 + b2 = b') :
    IsFibAux (bit0 n) a' b' :=
  ⟨by
    rw [fib_bit0, H.1, H.2, ← bit0_eq_two_mul,
      show bit0 b - a = c by rw [← h1, Nat.add_sub_cancel_left], h2],
    by rw [fib_bit0_succ, H.1, H.2, pow_two, pow_two, h3, h4, add_comm, h5]⟩
#align norm_num.is_fib_aux_bit0 NormNum.is_fib_aux_bit0

theorem is_fib_aux_bit1 {n a b c a2 b2 a' b' : ℕ} (H : IsFibAux n a b) (h1 : a * a = a2)
    (h2 : b * b = b2) (h3 : a2 + b2 = a') (h4 : bit0 a + b = c) (h5 : b * c = b') :
    IsFibAux (bit1 n) a' b' :=
  ⟨by rw [fib_bit1, H.1, H.2, pow_two, pow_two, h1, h2, add_comm, h3], by
    rw [fib_bit1_succ, H.1, H.2, ← bit0_eq_two_mul, h4, h5]⟩
#align norm_num.is_fib_aux_bit1 NormNum.is_fib_aux_bit1

theorem is_fib_aux_bit0_done {n a b c a' : ℕ} (H : IsFibAux n a b) (h1 : a + c = bit0 b)
    (h2 : a * c = a') : fib (bit0 n) = a' :=
  (is_fib_aux_bit0 H h1 h2 rfl rfl rfl).1
#align norm_num.is_fib_aux_bit0_done NormNum.is_fib_aux_bit0_done

theorem is_fib_aux_bit1_done {n a b a2 b2 a' : ℕ} (H : IsFibAux n a b) (h1 : a * a = a2)
    (h2 : b * b = b2) (h3 : a2 + b2 = a') : fib (bit1 n) = a' :=
  (is_fib_aux_bit1 H h1 h2 h3 rfl rfl).1
#align norm_num.is_fib_aux_bit1_done NormNum.is_fib_aux_bit1_done

end deprecated
-- Porting note: This part of the file is tactic related
/-
/-- `prove_fib_aux ic n` returns `(ic', a, b, ⊢ is_fib_aux n a b)`, where `n` is a numeral. -/
unsafe def prove_fib_aux (ic : instance_cache) : expr → tactic (instance_cache × expr × expr × expr)
  | e =>
    match match_numeral e with
    | match_numeral_result.one => pure (ic, q((1 : ℕ)), q((1 : ℕ)), q(is_fib_aux_one))
    | match_numeral_result.bit0 e => do
      let (ic, a, b, H) ← prove_fib_aux e
      let na ← a.toNat
      let nb ← b.toNat
      let (ic, c) ← ic.ofNat (2 * nb - na)
      let (ic, h1) ← prove_add_nat ic a c (q((bit0 : ℕ → ℕ)).mk_app [b])
      let (ic, a', h2) ← prove_mul_nat ic a c
      let (ic, a2, h3) ← prove_mul_nat ic a a
      let (ic, b2, h4) ← prove_mul_nat ic b b
      let (ic, b', h5) ← prove_add_nat' ic a2 b2
      pure
          (ic, a', b',
            q(@is_fib_aux_bit0).mk_app [e, a, b, c, a2, b2, a', b', H, h1, h2, h3, h4, h5])
    | match_numeral_result.bit1 e => do
      let (ic, a, b, H) ← prove_fib_aux e
      let na ← a.toNat
      let nb ← b.toNat
      let (ic, c) ← ic.ofNat (2 * na + nb)
      let (ic, a2, h1) ← prove_mul_nat ic a a
      let (ic, b2, h2) ← prove_mul_nat ic b b
      let (ic, a', h3) ← prove_add_nat' ic a2 b2
      let (ic, h4) ← prove_add_nat ic (q((bit0 : ℕ → ℕ)).mk_app [a]) b c
      let (ic, b', h5) ← prove_mul_nat ic b c
      pure
          (ic, a', b',
            q(@is_fib_aux_bit1).mk_app [e, a, b, c, a2, b2, a', b', H, h1, h2, h3, h4, h5])
    | _ => failed
#align norm_num.prove_fib_aux NormNum.prove_fib_aux

/-- A `norm_num` plugin for `fib n` when `n` is a numeral.
Uses the binary representation of `n` like `Nat.fastFib`. -/
unsafe def prove_fib (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
  match match_numeral e with
  | match_numeral_result.zero => pure (ic, q((0 : ℕ)), q(fib_zero))
  | match_numeral_result.one => pure (ic, q((1 : ℕ)), q(fib_one))
  | match_numeral_result.bit0 e => do
    let (ic, a, b, H) ← prove_fib_aux ic e
    let na ← a.toNat
    let nb ← b.toNat
    let (ic, c) ← ic.ofNat (2 * nb - na)
    let (ic, h1) ← prove_add_nat ic a c (q((bit0 : ℕ → ℕ)).mk_app [b])
    let (ic, a', h2) ← prove_mul_nat ic a c
    pure (ic, a', q(@is_fib_aux_bit0_done).mk_app [e, a, b, c, a', H, h1, h2])
  | match_numeral_result.bit1 e => do
    let (ic, a, b, H) ← prove_fib_aux ic e
    let (ic, a2, h1) ← prove_mul_nat ic a a
    let (ic, b2, h2) ← prove_mul_nat ic b b
    let (ic, a', h3) ← prove_add_nat' ic a2 b2
    pure (ic, a', q(@is_fib_aux_bit1_done).mk_app [e, a, b, a2, b2, a', H, h1, h2, h3])
  | _ => failed
#align norm_num.prove_fib NormNum.prove_fib

/-- A `norm_num` plugin for `fib n` when `n` is a numeral.
/-
unknown identifier ''
-/
Uses the binary representation of `n` like `Nat.fastFib`. -/
@[norm_num]
unsafe def eval_fib : expr → tactic (expr × expr)
  | (fib $(en)) => do
    let n ← en.toNat
    match n with
      | 0 => pure (q((0 : ℕ)), q(fib_zero))
      | 1 => pure (q((1 : ℕ)), q(fib_one))
      | 2 => pure (q((1 : ℕ)), q(fib_two))
      | _ => do
        let c ← mk_instance_cache q(ℕ)
        Prod.snd <$> prove_fib c en
  | _ => failed
#align norm_num.eval_fib NormNum.eval_fib
-/
end NormNum
