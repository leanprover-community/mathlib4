/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import Mathlib.Data.Nat.Pow

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
                           -- ⊢ 0 < n
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
    go (k+1) p (n / p)
  else
    k

attribute [inherit_doc maxPowDiv] maxPowDiv.go

end Nat

namespace Nat.maxPowDiv

theorem go_eq {k p n : ℕ} :
    go k p n = if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k+1) p (n / p) else k := by
  dsimp [go, go._unary]
  -- ⊢ WellFounded.fix go._unary.proof_1 (fun _x a => if h : 1 < _x.snd.fst ∧ 0 < _ …
  rw [WellFounded.fix_eq]
  -- ⊢ (if h : 1 < { fst := k, snd := { fst := p, snd := n } }.snd.fst ∧ 0 < { fst  …
  simp
  -- 🎉 no goals

theorem go_succ {k p n : ℕ} : go (k+1) p n = go k p n + 1 := by
  rw [go_eq]
  -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = go …
  conv_rhs => rw [go_eq]
  -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = (i …
  by_cases (1 < p ∧ 0 < n ∧ n % p = 0); swap
  -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = (i …
  -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = (i …
                                        -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = (i …
  · simp only [if_neg h]
    -- 🎉 no goals
  · have : n / p < n := by apply Nat.div_lt_self <;> aesop
    -- ⊢ (if 1 < p ∧ 0 < n ∧ n % p = 0 then go (k + 1 + 1) p (n / p) else k + 1) = (i …
    simp only [if_pos h]
    -- ⊢ go (k + 1 + 1) p (n / p) = go (k + 1) p (n / p) + 1
    apply go_succ
    -- 🎉 no goals

@[simp]
theorem zero_base {n : ℕ} : maxPowDiv 0 n = 0 := by
  dsimp [maxPowDiv]
  -- ⊢ go 0 0 n = 0
  rw [maxPowDiv.go_eq]
  -- ⊢ (if 1 < 0 ∧ 0 < n ∧ n % 0 = 0 then go (0 + 1) 0 (n / 0) else 0) = 0
  simp
  -- 🎉 no goals

@[simp]
theorem zero {p : ℕ} : maxPowDiv p 0 = 0 := by
  dsimp [maxPowDiv]
  -- ⊢ go 0 p 0 = 0
  rw [maxPowDiv.go_eq]
  -- ⊢ (if 1 < p ∧ 0 < 0 ∧ 0 % p = 0 then go (0 + 1) p (0 / p) else 0) = 0
  simp
  -- 🎉 no goals

theorem base_mul_eq_succ {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDiv (p*n) = p.maxPowDiv n + 1 := by
  have : 0 < p := lt_trans (b := 1) (by simp) hp
  -- ⊢ maxPowDiv p (p * n) = maxPowDiv p n + 1
  dsimp [maxPowDiv]
  -- ⊢ go 0 p (p * n) = go 0 p n + 1
  rw [maxPowDiv.go_eq, if_pos, mul_div_right _ this]
  -- ⊢ go (0 + 1) p n = go 0 p n + 1
  · apply go_succ
    -- 🎉 no goals
  · refine ⟨hp, ?_, by simp⟩
    -- ⊢ 0 < p * n
    apply Nat.mul_pos this hn
    -- 🎉 no goals

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
  -- ⊢ p ^ go 0 p n ∣ n
  rw [go_eq]
  -- ⊢ (p ^ if 1 < p ∧ 0 < n ∧ n % p = 0 then go (0 + 1) p (n / p) else 0) ∣ n
  by_cases (1 < p ∧ 0 < n ∧ n % p = 0)
  -- ⊢ (p ^ if 1 < p ∧ 0 < n ∧ n % p = 0 then go (0 + 1) p (n / p) else 0) ∣ n
  -- ⊢ (p ^ if 1 < p ∧ 0 < n ∧ n % p = 0 then go (0 + 1) p (n / p) else 0) ∣ n
  · have : n / p < n := by apply Nat.div_lt_self <;> aesop
    -- ⊢ (p ^ if 1 < p ∧ 0 < n ∧ n % p = 0 then go (0 + 1) p (n / p) else 0) ∣ n
    rw [if_pos h]
    -- ⊢ p ^ go (0 + 1) p (n / p) ∣ n
    have ⟨c,hc⟩ := pow_dvd p (n / p)
    -- ⊢ p ^ go (0 + 1) p (n / p) ∣ n
    rw [go_succ, pow_succ]
    -- ⊢ p ^ go 0 p (n / p) * p ∣ n
    nth_rw 2 [←mod_add_div' n p]
    -- ⊢ p ^ go 0 p (n / p) * p ∣ n % p + n / p * p
    rw [h.right.right, zero_add]
    -- ⊢ p ^ go 0 p (n / p) * p ∣ n / p * p
    exact ⟨c,by nth_rw 1 [hc]; ac_rfl⟩
    -- 🎉 no goals
  · rw [if_neg h]
    -- ⊢ p ^ 0 ∣ n
    simp
    -- 🎉 no goals

theorem le_of_dvd {p n pow : ℕ} (hp : 1 < p) (hn : 0 < n) (h : p ^ pow ∣ n) :
    pow ≤ p.maxPowDiv n := by
  have ⟨c, hc⟩ := h
  -- ⊢ pow ≤ maxPowDiv p n
  have : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro h'
    rw [h',mul_zero] at hc
    exact not_eq_zero_of_lt hn hc
  simp [hc, base_pow_mul hp this]
  -- 🎉 no goals

