/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
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
Tail recursive function which returns the largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`,
as well as the ratio `n / p ^ k`.
-/
def maxPowDvdDiv (p n : ℕ) : ℕ × ℕ :=
  go 0 p n
  where go (k p n : ℕ) : ℕ × ℕ :=
    if 1 < p ∧ 0 < n ∧ n % p = 0 then
      go (k + 1) p (n / p)
    else
      (k, n)
    termination_by n
    decreasing_by apply Nat.div_lt_self <;> tauto

attribute [inherit_doc maxPowDvdDiv] maxPowDvdDiv.go

/--
Tail recursive function which returns the largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`.
`padicValNat_eq_maxPowDvd` allows the code generator to use this definition for `padicValNat`
-/
def maxPowDvd (p n : ℕ) : ℕ := (maxPowDvdDiv p n).1

@[deprecated (since := "2025-04-22")]
alias maxPowDiv := maxPowDvd

namespace maxPowDvdDiv

theorem go_spec (k p n : ℕ) :
    p ^ (go k p n).1 * (go k p n).2 = p ^ k * n ∧
      (1 < p → 0 < n → ¬p ∣ (go k p n).2) := by
  fun_induction go with
  | case1 k n h ih =>
    unfold go
    rw [if_pos h, ih.1, pow_succ, mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.2.2)]
    refine ⟨rfl, fun hp hn ↦ ih.2 hp ?_⟩
    apply_rules [Nat.div_pos, zero_le_one.trans_lt hp, Nat.le_of_dvd, Nat.dvd_of_mod_eq_zero h.2.2]
  | case2 k n h =>
    unfold go
    rw [if_neg h]
    simp only [not_and, ← Nat.dvd_iff_mod_eq_zero] at h
    exact ⟨rfl, h⟩

theorem go_succ (k p n : ℕ) : go (k + 1) p n = ((go k p n).1 + 1, (go k p n).2) := by
  fun_induction go with
  | case1 _ _ h ih =>
    unfold go
    simp only [if_pos h, ih]
  | case2 _ _ h =>
    unfold go
    simp only [if_neg h]

@[simp]
theorem pow_mul_eq (p n : ℕ) : p ^ (maxPowDvdDiv p n).1 * (maxPowDvdDiv p n).2 = n := by
  simpa [maxPowDvdDiv] using (go_spec 0 p n).1

theorem not_dvd_snd {p n : ℕ} (hp : 1 < p) (hn : 0 < n) : ¬p ∣ (maxPowDvdDiv p n).2 := by
  simpa [maxPowDvdDiv] using (go_spec 0 p n).2 hp hn

theorem of_base_le_one {p : ℕ} (hp : p ≤ 1) (n : ℕ) : maxPowDvdDiv p n = (0, n) := by
  simp [maxPowDvdDiv, go, hp.not_lt]

@[simp] theorem zero_left (n : ℕ) : maxPowDvdDiv 0 n = (0, n) := of_base_le_one (Nat.zero_le _) _
@[simp] theorem one_left (n : ℕ) : maxPowDvdDiv 1 n = (0, n) := of_base_le_one le_rfl _

@[simp]
theorem zero_right (p : ℕ) : maxPowDvdDiv p 0 = (0, 0) := by
  simp [maxPowDvdDiv, go]

theorem of_not_dvd {p n : ℕ} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  rw [maxPowDvdDiv, go]
  simp [Nat.dvd_iff_mod_eq_zero.not.mp h]

@[simp]
theorem one_right (p : ℕ) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [of_not_dvd, *]

theorem base_mul {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDvdDiv (p * n) = ((p.maxPowDvdDiv n).1 + 1, (p.maxPowDvdDiv n).2) := by
  unfold maxPowDvdDiv
  rw [go, if_pos (by simp [*, hp.pos]), go_succ, Nat.mul_div_cancel_left _ hp.pos]

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
