/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Common

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
  if 1 < p ∧ 0 < n then
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

namespace maxPowDvdDiv

theorem go_spec {n p fuel : ℕ} (hp : 1 < p) (hn : 0 < n) (hfuel : n < p ^ fuel) :
    (go n p fuel).2 * p ^ (go n p fuel).1 = n ∧ ¬p ∣ (go n p fuel).2 := by
  induction fuel generalizing p with
  | zero => simp_all
  | succ fuel ih =>
    by_cases hnp : n % p = 0
    · obtain ⟨ih₁, ih₂⟩ := by
        refine @ih (p * p) (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hp hp) ?_
        cases fuel with
        | zero =>
          refine absurd hfuel <| Nat.not_lt_of_le <| Nat.le_of_dvd hn ?_
          simpa [dvd_iff_mod_eq_zero]
        | succ fuel =>
          rw [← Nat.pow_two, ← Nat.pow_mul]
          refine Nat.lt_of_lt_of_le hfuel <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (by cutsat)
      simp only [go, if_pos hnp]
      split <;> simp_all [← dvd_iff_mod_eq_zero, @Nat.pow_add_one' _ (2 * _), ← Nat.mul_assoc,
        Nat.div_mul_cancel, ← Nat.pow_two, ← Nat.pow_mul]
    · simp_all [go, dvd_iff_mod_eq_zero]

@[simp]
theorem mul_pow_eq (p n : ℕ) : (maxPowDvdDiv p n).2 * p ^ (maxPowDvdDiv p n).1 = n := by
  fun_cases maxPowDvdDiv with
  | case1 h => exact go_spec h.1 h.2 (Nat.lt_pow_self h.1) |>.1
  | case2 h => simp

theorem not_dvd_snd {p n : ℕ} (hp : 1 < p) (hn : 0 < n) : ¬p ∣ (maxPowDvdDiv p n).2 := by
  simp [maxPowDvdDiv, Nat.lt_pow_self, go_spec, *]

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

/-- If `p > 1`, `n > 0`, then the first component of `maxPowDvdDiv` is the maximal power of `p`
that divides `n`. -/
theorem pow_dvd_iff_le_fst {p k n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p ^ k ∣ n ↔ k ≤ (p.maxPowDvdDiv n).1 := by
  have H := go_spec hp hn (Nat.lt_pow_self hp)
  conv_lhs => rw [← H.1]
  rw [maxPowDvdDiv, if_pos ⟨hp, hn⟩]
  cases Nat.lt_or_ge (go n p n).1 k with
  | inl hlt =>
    refine iff_of_false (fun hdvd ↦ ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, Nat.pow_add',
      Nat.mul_dvd_mul_iff_right (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
    exact H.2 <| Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_left_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

theorem base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (k : ℕ) :
    p.maxPowDvdDiv (p ^ k * n) = ((p.maxPowDvdDiv n).1 + k, (p.maxPowDvdDiv n).2) := by
  have H₁ : (p.maxPowDvdDiv (p ^ k * n)).1 = (p.maxPowDvdDiv n).1 + k := by
    refine eq_of_forall_le_iff fun c ↦ ?_
    rw [← pow_dvd_iff_le_fst hp, ← Nat.sub_le_iff_le_add, ← pow_dvd_iff_le_fst hp hn]


theorem base_mul {p n : ℕ} (hp : 1 < p) (hn : 0 < n) :
    p.maxPowDvdDiv (p * n) = ((p.maxPowDvdDiv n).1 + 1, (p.maxPowDvdDiv n).2) := by
  have hp₀ := Nat.zero_lt_of_lt hp
  have H₁ : (p.maxPowDvdDiv (p * n)).1 = (p.maxPowDvdDiv n).1 + 1 := by
    refine eq_of_forall_le_iff fun c ↦ ?_
    rw [← pow_dvd_iff_le_fst hp (Nat.mul_pos hp₀ hn), ← Nat.sub_le_iff_le_add,
      ← pow_dvd_iff_le_fst hp hn]


  conv in p * n => rw [← pow_mul_eq p n, ← mul_assoc, ← pow_add_one']
  rw [go_unique hp.pos (not_dvd_snd hp hn), zero_add]
  rw [add_one_le_iff]
  calc
    (p.maxPowDvdDiv n).1 < p ^ (p.maxPowDvdDiv n).1 := Nat.lt_pow_self hp
    _ ≤ p ^ (p.maxPowDvdDiv n).1 * (p.maxPowDvdDiv n).2 := by
      apply le_mul_of_le_of_one_le (by simp)
    _ < p * n := by
      rw [pow_mul_eq]

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
