/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Common

/-!
# The maximal power of one natural number dividing another

Here we introduce `p.maxPowDvd n` which returns the maximal `k : ℕ` for
which `p ^ k ∣ n` with the convention that `maxPowDvd 1 n = 0` for all `n`.

We prove enough about `maxPowDvd` in this file to show equality with `Nat.padicValNat` in
`padicValNat.padicValNat_eq_maxPowDvd`.

The implementation of `maxPowDvd` improves on the speed of `padicValNat`.
-/

namespace Nat

/--
Find largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`, as well as the ratio `n / p ^ k`.

This function is written using "fuel recursion" so that it is 
-/
def maxPowDvdDiv (p n : ℕ) : ℕ × ℕ :=
  if 1 < p ∧ 0 < n then
    go p 0 n n
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go
  | _, res, n, 0 => (res, n)
  | p, res, n, fuel + 1 =>
    if n % p = 0 then
      go p (res + 1) (n / p) fuel
    else
      (res, n)

/--
Tail recursive function which returns the largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`.
`padicValNat_eq_maxPowDvd` allows the code generator to use this definition for `padicValNat`
-/
def maxPowDvd (p n : ℕ) : ℕ := (maxPowDvdDiv p n).1

@[deprecated (since := "2025-09-27")]
alias maxPowDiv := maxPowDvd

namespace maxPowDvdDiv

theorem go_spec {p res n fuel : ℕ} (hp : 1 < p) (hn : 0 < n) (hfuel : n ≤ fuel) :
    p ^ (go p res n fuel).1 * (go p res n fuel).2 = p ^ res * n ∧ ¬p ∣ (go p res n fuel).2 := by
  induction fuel generalizing res n with
  | zero => exact absurd hn hfuel.not_gt
  | succ fuel ih =>
    by_cases hnp : n % p = 0
    case pos =>
      rw [← Nat.dvd_iff_mod_eq_zero] at hnp
      rcases hnp with ⟨m, rfl⟩
      specialize @ih (res + 1) m (by grind) ?_
      · rw [← Nat.lt_add_one_iff]
        refine lt_of_lt_of_le ?_ hfuel
        rwa [Nat.lt_mul_iff_one_lt_left (by grind)]
      · simp [go, one_pos.trans hp, ih, pow_succ, mul_assoc]
    case neg =>
      simp [go, hnp, Nat.dvd_iff_mod_eq_zero]

theorem go_unique {p k l n fuel : ℕ} (hp : 0 < p) (hdvd : ¬p ∣ n) (hfuel : l ≤ fuel) :
    go p k (p ^ l * n) fuel = (k + l, n) := by
  induction fuel generalizing k l with
  | zero => simp_all [go]
  | succ fuel ih =>
    cases l with
    | zero => simp [go, ← Nat.dvd_iff_mod_eq_zero, hdvd]
    | succ l => simp_all [go, pow_succ, mul_right_comm _ p, add_assoc, add_comm 1 l]

@[simp]
theorem pow_mul_eq (p n : ℕ) : p ^ (maxPowDvdDiv p n).1 * (maxPowDvdDiv p n).2 = n := by
  unfold maxPowDvdDiv
  split_ifs with h
  · simp [go_spec, h]
  · simp
    
theorem not_dvd_snd {p n : ℕ} (hp : 1 < p) (hn : 0 < n) : ¬p ∣ (maxPowDvdDiv p n).2 := by
  simp [maxPowDvdDiv, go_spec, *]

theorem of_base_le_one {p : ℕ} (hp : p ≤ 1) (n : ℕ) : maxPowDvdDiv p n = (0, n) := by
  simp [maxPowDvdDiv, hp.not_gt]

@[simp] theorem zero_left (n : ℕ) : maxPowDvdDiv 0 n = (0, n) := of_base_le_one (Nat.zero_le _) _
@[simp] theorem one_left (n : ℕ) : maxPowDvdDiv 1 n = (0, n) := of_base_le_one le_rfl _

@[simp]
theorem zero_right (p : ℕ) : maxPowDvdDiv p 0 = (0, 0) := by simp [maxPowDvdDiv]

theorem of_not_dvd {p n : ℕ} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, go]

@[simp]
theorem one_right (p : ℕ) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [of_not_dvd, *]

theorem base_mul {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDvdDiv (p * n) = ((p.maxPowDvdDiv n).1 + 1, (p.maxPowDvdDiv n).2) := by
  rw [maxPowDvdDiv, if_pos (by simp [*, hp.pos])]
  conv in p * n => rw [← pow_mul_eq p n, ← mul_assoc, ← pow_add_one']
  rw [go_unique hp.pos (not_dvd_snd hp hn), zero_add]
  rw [add_one_le_iff]
  calc
    (p.maxPowDvdDiv n).1 < p ^ (p.maxPowDvdDiv n).1 := Nat.lt_pow_self hp
    _ ≤ p ^ (p.maxPowDvdDiv n).1 * (p.maxPowDvdDiv n).2 := by
      apply le_mul_of_le_of_one_le (by simp)
    _ < p * n := by
      rw [pow_mul_eq]

theorem base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (k : ℕ) :
    p.maxPowDvdDiv (p ^ k * n) = ((p.maxPowDvdDiv n).1 + k, (p.maxPowDvdDiv n).2) := by
  induction k <;>
    simp [*, pow_succ', mul_assoc, base_mul hp (Nat.mul_pos (Nat.pow_pos hp.pos) _), add_assoc]

@[simp]
theorem base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : p.maxPowDvdDiv (p ^ k) = (k, 1) := by
  simpa using base_pow_mul hp one_pos k

@[simp]
theorem base {p : ℕ} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1) := by
  simpa using base_pow hp 1

end maxPowDvdDiv

namespace maxPowDvd

@[simp] theorem zero_left {n : ℕ} : maxPowDvd 0 n = 0 := by simp [maxPowDvd]
@[simp] theorem one_left {n : ℕ} : maxPowDvd 1 n = 0 := by simp [maxPowDvd]
@[simp] theorem zero_right {p : ℕ} : maxPowDvd p 0 = 0 := by simp [maxPowDvd]

theorem base_pow_mul {p n k : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDvd (p ^ k * n) = p.maxPowDvd n + k := by
  simp [maxPowDvd, maxPowDvdDiv.base_pow_mul hp hn]

theorem base_mul_eq_succ {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDvd (p * n) = p.maxPowDvd n + 1 := by
  simp [← base_pow_mul hp hn]

theorem pow_dvd {p n : ℕ} : p ^ p.maxPowDvd n ∣ n := by
  conv_rhs => rw [← maxPowDvdDiv.pow_mul_eq p n]
  apply dvd_mul_right

theorem le_of_dvd {p n k : ℕ} (hp : 1 < p) (hn : 0 < n) (h : p ^ k ∣ n) :
    k ≤ p.maxPowDvd n := by
  by_contra! hlt
  rw [← maxPowDvdDiv.pow_mul_eq p n] at h
  rcases Nat.exists_eq_add_of_lt hlt with ⟨l, rfl⟩
  rw [add_assoc, pow_add, maxPowDvd, Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos), pow_succ] at h
  exact maxPowDvdDiv.not_dvd_snd hp hn <| dvd_trans (Nat.dvd_mul_left ..) h

theorem pow_dvd_iff_le {p n k : ℕ} (hp : 1 < p) (hn : 0 < n) : p ^ k ∣ n ↔ k ≤ p.maxPowDvd n :=
  ⟨le_of_dvd hp hn, fun hle ↦ dvd_trans (Nat.pow_dvd_pow _ hle) pow_dvd⟩

end maxPowDvd

end Nat
