/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Order.WithZero
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Tactic.Common

/-!
# The maximal power of one natural number dividing another

Here we introduce `p.maxPowDiv n` which returns the maximal `k : ℕ` for
which `p ^ k ∣ n` with the convention that `maxPowDiv 1 n = 0` for all `n`.

We prove enough about `maxPowDiv` in this file to show equality with `Nat.padicValNat` in
`padicValNat.padicValNat_eq_maxPowDiv`.

The implementation of `maxPowDiv` improves on the speed of `padicValNat`.
-/

namespace Nat

open Nat

/--
Tail recursive function which returns the largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`.
`padicValNat_eq_maxPowDiv` allows the code generator to use this definition for `padicValNat`
-/
def maxPowDiv (p n : ℕ) : ℕ :=
  go 0 p n
where go (k p n : ℕ) : ℕ :=
  if h : 1 < p ∧ 0 < n ∧ n % p = 0 then
    have : n / p < n := by apply Nat.div_lt_self <;> aesop
    go (k+1) p (n / p)
  else
    k

attribute [inherit_doc maxPowDiv] maxPowDiv.go

end Nat

namespace Nat.maxPowDiv

theorem go_eq {k p n : ℕ} :
    go k p n = if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k+1) p (n / p) else k := by
  dsimp [go, go._unary]
  rw [WellFounded.fix_eq]
  simp

theorem go_succ {k p n : ℕ} : go (k+1) p n = go k p n + 1 := by
  rw [go_eq]
  conv_rhs => rw [go_eq]
  by_cases h : (1 < p ∧ 0 < n ∧ n % p = 0); swap
  · simp only [if_neg h]
  · have : n / p < n := by apply Nat.div_lt_self <;> aesop
    simp only [if_pos h]
    apply go_succ

@[simp]
theorem zero_base {n : ℕ} : maxPowDiv 0 n = 0 := by
  dsimp [maxPowDiv]
  rw [maxPowDiv.go_eq]
  simp

@[simp]
theorem zero {p : ℕ} : maxPowDiv p 0 = 0 := by
  dsimp [maxPowDiv]
  rw [maxPowDiv.go_eq]
  simp

theorem base_mul_eq_succ {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv (p*n) = p.maxPowDiv n + 1 := by
  have : 0 < p := lt_trans (b := 1) (by simp) hp
  dsimp [maxPowDiv]
  rw [maxPowDiv.go_eq, if_pos, mul_div_right _ this]
  · apply go_succ
  · refine ⟨hp, ?_, by simp⟩
    apply Nat.mul_pos this hn

theorem base_pow_mul {p n exp : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv (p ^ exp * n) = p.maxPowDiv n + exp := by
  match exp with
  | 0 => simp
  | e + 1 =>
    rw [pow_succ, mul_assoc, mul_comm, mul_assoc, base_mul_eq_succ hp, mul_comm, base_pow_mul hp hn]
    · ac_rfl
    · apply Nat.mul_pos hn <| pow_pos (pos_of_gt hp) e

theorem pow_dvd (p n : ℕ) : p ^ (p.maxPowDiv n) ∣ n := by
  dsimp [maxPowDiv]
  rw [go_eq]
  by_cases h : (1 < p ∧ 0 < n ∧ n % p = 0)
  · have : n / p < n := by apply Nat.div_lt_self <;> aesop
    rw [if_pos h]
    have ⟨c,hc⟩ := pow_dvd p (n / p)
    rw [go_succ, pow_succ]
    nth_rw 2 [← mod_add_div' n p]
    rw [h.right.right, zero_add]
    exact ⟨c,by nth_rw 1 [hc]; ac_rfl⟩
  · rw [if_neg h]
    simp

theorem le_of_dvd {p n pow : ℕ} (hp : 1 < p) (hn : 0 < n) (h : p ^ pow ∣ n) :
    pow ≤ p.maxPowDiv n := by
  have ⟨c, hc⟩ := h
  have : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro h'
    rw [h',mul_zero] at hc
    exact not_eq_zero_of_lt hn hc
  simp [hc, base_pow_mul hp this]
