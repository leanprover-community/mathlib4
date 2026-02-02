/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Notation

/-!
# The maximal power of one natural number dividing another

Here we introduce `p.maxPowDvd n` which returns the maximal `k : ℕ` for
which `p ^ k ∣ n` with the convention that `maxPowDvd 1 n = 0` for all `n`.

We prove enough about `maxPowDvd` in this file to show equality with `Nat.padicValNat` in
`padicValNat.padicValNat_eq_maxPowDvd`.

The implementation of `maxPowDvd` improves on the speed of `padicValNat`.
-/

@[expose] public section

namespace Nat

/--
Find largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`, as well as the ratio `n / p ^ k`.

TODO: implementation notes.
-/
def maxPowDvdDiv (p n : ℕ) : ℕ × ℕ :=
  if 1 < p ∧ n ≠ 0 then
    go p n
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (0, n)
  | p, fuel + 1 =>
    if n % p = 0 then
      let (e, q) := go (p * p) fuel
      if q % p = 0 then (2 * e + 1, q / p) else (2 * e, q)
    else
      (0, n)

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`. -/
def _root_.padicValNat (p n : ℕ) : ℕ := (maxPowDvdDiv p n).fst

/-- Divide `n` by the maximal power of `p` that divides `n`. -/
def divMaxPow (n p : ℕ) : ℕ := (maxPowDvdDiv p n).snd

theorem maxPowDvdDiv.go_spec {n p fuel : ℕ} (hp : 1 < p) (hn : n ≠ 0) (hfuel : n < p ^ fuel) :
    (go n p fuel).2 * p ^ (go n p fuel).1 = n ∧ ¬p ∣ (go n p fuel).2 := by
  induction fuel generalizing p with
  | zero => simp_all
  | succ fuel ih =>
    by_cases hnp : n % p = 0
    · obtain ⟨ih₁, ih₂⟩ := by
        refine @ih (p * p) (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hp hp) ?_
        cases fuel with
        | zero =>
          refine absurd hfuel <| Nat.not_lt_of_le <| Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ?_
          simpa [dvd_iff_mod_eq_zero]
        | succ fuel =>
          rw [← Nat.pow_two, ← Nat.pow_mul]
          refine Nat.lt_of_lt_of_le hfuel <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (by lia)
      simp only [go, if_pos hnp]
      split <;> simp_all [← dvd_iff_mod_eq_zero, @Nat.pow_add_one' _ (2 * _), ← Nat.mul_assoc,
        Nat.div_mul_cancel, ← Nat.pow_two, ← Nat.pow_mul]
    · simp_all [go, dvd_iff_mod_eq_zero]

theorem maxPowDvdDiv_of_base_le_one {p : ℕ} (hp : p ≤ 1) (n : ℕ) : maxPowDvdDiv p n = (0, n) := by
  simp [maxPowDvdDiv, Nat.not_lt_of_ge hp]

@[simp]
theorem maxPowDvdDiv_zero_left (n : ℕ) : maxPowDvdDiv 0 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.zero_le _) _

@[simp]
theorem _root_.padicValNat_zero_left (n : ℕ) : padicValNat 0 n = 0 := by simp [padicValNat]

@[simp]
theorem divMaxPow_zero_right (n : ℕ) : divMaxPow n 0 = n := by simp [divMaxPow]

@[simp]
theorem maxPowDvdDiv_one_left (n : ℕ) : maxPowDvdDiv 1 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.le_refl _) _

@[simp]
theorem _root_.padicValNat_one_left (n : ℕ) : padicValNat 1 n = 0 := by simp [padicValNat]

@[simp]
theorem divMaxPow_one_right (n : ℕ) : divMaxPow n 1 = n := by simp [divMaxPow]

@[simp]
theorem maxPowDvdDiv_zero_right (p : ℕ) : maxPowDvdDiv p 0 = (0, 0) := by simp [maxPowDvdDiv]

@[simp]
theorem _root_.padicValNat_zero_right (p : ℕ) : padicValNat p 0 = 0 := by simp [padicValNat]

@[simp]
theorem divMaxPow_zero_left (p : ℕ) : divMaxPow 0 p = 0 := by simp [divMaxPow]

theorem maxPowDvdDiv_of_not_dvd {p n : ℕ} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]
theorem maxPowDvdDiv_one_right (p : ℕ) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[simp]
theorem _root_.padicValNat_one (p : ℕ) : padicValNat p 1 = 0 := by simp [padicValNat]

@[simp]
theorem divMaxPow_one_left (p : ℕ) : divMaxPow 1 p = 1 := by simp [divMaxPow]

open maxPowDvdDiv in
@[simp]
theorem divMaxPow_mul_pow_padicValNat (p n : ℕ) : divMaxPow n p * p ^ padicValNat p n = n := by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
  | case1 h => exact go_spec h.1 h.2 (Nat.lt_pow_self h.1) |>.1
  | case2 h => simp

@[simp]
theorem pow_padicValNat_mul_divMaxPow (p n : ℕ) : p ^ padicValNat p n * divMaxPow n p = n := by
  rw [Nat.mul_comm, divMaxPow_mul_pow_padicValNat]

theorem not_dvd_divMaxPow {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) : ¬p ∣ divMaxPow n p := by
  simp [divMaxPow, maxPowDvdDiv, Nat.lt_pow_self, maxPowDvdDiv.go_spec, *]

private theorem pow_dvd_iff_le_of_spec {p k n a b : ℕ} (hp : 1 < p) (hn : n ≠ 0)
    (hab : p ^ a * b = n) (hb : ¬p ∣ b) : p ^ k ∣ n ↔ k ≤ a := by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd ↦ ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, Nat.pow_add,
      Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
    exact hb <| Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_right_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

/-- If `p > 1`, `n > 0`, then the first component of `maxPowDvdDiv` is the maximal power of `p`
that divides `n`. -/
theorem pow_dvd_iff_le_padicValNat {p k n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n := by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)

theorem maxPowDvdDiv_of_pow_mul_eq {p n k l : ℕ} (hn : n ≠ 0) (h : p ^ k * l = n)
    (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l) := by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, ← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of_spec hp hn h hl]
          apply Nat.le_refl
        · rw [← pow_dvd_iff_le_of_spec hp hn h hl, pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn]
          apply Nat.le_refl
    rw [← pow_padicValNat_mul_divMaxPow p n, hk, padicValNat, Nat.mul_left_cancel_iff] at h
    · exact Prod.ext hk.symm h.symm
    · exact Nat.pow_pos <| Nat.zero_lt_of_lt hp

@[simp]
theorem maxPowDvdDiv_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    p.maxPowDvdDiv (p ^ k * n) = (padicValNat p n + k, divMaxPow n p) := by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]
theorem _root_.padicValNat_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    padicValNat p (p ^ k * n) = padicValNat p n + k := by
  simp [padicValNat, *]

@[simp]
theorem divMaxPow_base_pow_mul {p : ℕ} (hp : p ≠ 0) (n k : ℕ) :
    (p ^ k * n).divMaxPow p = n.divMaxPow p := by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]
theorem maxPowDvdDiv_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    p.maxPowDvdDiv (p * n) = (padicValNat p n + 1, divMaxPow n p) := by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]
theorem _root_.padicValNat_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    padicValNat p (p * n) = padicValNat p n + 1 := by
  simp [padicValNat, *]

@[simp]
theorem divMaxPow_base_mul {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    (p * n).divMaxPow p = n.divMaxPow p := by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]
theorem maxPowDvdDiv_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : p.maxPowDvdDiv (p ^ k) = (k, 1) := by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]
theorem _root_.padicValNat_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : padicValNat p (p ^ k) = k := by
  simp [padicValNat, hp]

@[simp]
theorem divMaxPow_base_pow {p : ℕ} (hp : p ≠ 0) (k : ℕ) : (p ^ k).divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]
theorem maxPowDvdDiv_self {p : ℕ} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1) := by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]
theorem _root_.padicValNat_base {p : ℕ} (hp : 1 < p) : padicValNat p p = 1 := by
  simpa using padicValNat_base_pow hp 1

@[simp]
theorem divMaxPow_self {p : ℕ} (hp : p ≠ 0) : p.divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow hp 1

@[simp]
theorem fst_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).1 = padicValNat p n := rfl

@[simp]
theorem snd_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).2 = n.divMaxPow p := rfl

end Nat
