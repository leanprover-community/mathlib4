/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, David Renshaw
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.ModEq

/-!
# IMO 1985 Q2

Fix a natural number $n ≥ 3$ and define $N=\{1, 2, 3, \dots, n-1\}$. Fix another natural number
$j ∈ N$ coprime to $n$. Each number in $N$ is now colored with one of two colors, say red or black,
so that:

1. $i$ and $n-i$ always receive the same color, and
2. $i$ and $|j-i|$ receive the same color for all $i ∈ N, i ≠ j$.

Prove that all numbers in $N$ must receive the same color.

# Solution

Let $a \sim b$ denote that $a$ and $b$ have the same color.
Because $j$ is coprime to $n$, every number in $N$ is of the form $kj\bmod n$ for a unique
$1 ≤ k < n$, so it suffices to show that $kj\bmod n \sim (k-1)j\bmod n$ for $1 < k < n$.
In this range of $k$, $kj\bmod n ≠ j$, so

* if $kj\bmod n > j$, $kj\bmod n \sim kj\bmod n - j = (k-1)j\bmod n$ using rule 2;
* if $kj\bmod n < j$, $kj\bmod n \sim j - kj\bmod n \sim n - j + kj\bmod n = (k-1)j\bmod n$
  using rule 2 then rule 1.
-/

namespace Imo1985Q2

open Nat

/-- The conditions on the problem's coloring `C`.
Although its domain is all of `ℕ`, we only care about its values in `Set.Ico 1 n`. -/
def Condition (n j : ℕ) (C : ℕ → Fin 2) : Prop :=
  (∀ i ∈ Set.Ico 1 n, C i = C (n - i)) ∧ (∀ i ∈ Set.Ico 1 n, i ≠ j → C i = C (j - i : ℤ).natAbs)

/-- For `1 ≤ k < n`, `k * j % n` has the same color as `j`. -/
lemma C_mul_mod {n j : ℕ} (hn : 3 ≤ n) (hj : j ∈ Set.Ico 1 n) (cpj : Nat.Coprime n j)
    {C : ℕ → Fin 2} (hC : Condition n j C) {k : ℕ} (hk : k ∈ Set.Ico 1 n) :
    C (k * j % n) = C j := by
  induction k, hk.1 using Nat.le_induction with
  | base => rw [one_mul, Nat.mod_eq_of_lt hj.2]
  | succ k hk₁ ih =>
    have nej : (k + 1) * j % n ≠ j := by
      by_contra! h; nth_rw 2 [← Nat.mod_eq_of_lt hj.2, ← one_mul j] at h
      replace h : (k + 1) % n = 1 % n := Nat.ModEq.cancel_right_of_coprime cpj h
      rw [Nat.mod_eq_of_lt hk.2, Nat.mod_eq_of_lt (by omega)] at h
      omega
    have b₁ : (k + 1) * j % n ∈ Set.Ico 1 n := by
      refine ⟨?_, Nat.mod_lt _ (by omega)⟩
      by_contra! h; rw [Nat.lt_one_iff, ← Nat.dvd_iff_mod_eq_zero] at h
      have ek := Nat.eq_zero_of_dvd_of_lt (cpj.dvd_of_dvd_mul_right h) hk.2
      omega
    rw [← ih ⟨hk₁, Nat.lt_of_succ_lt hk.2⟩, hC.2 _ b₁ nej]
    rcases nej.lt_or_gt with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h.le]
      have b₂ : j - (k + 1) * j % n ∈ Set.Ico 1 n :=
        ⟨Nat.sub_pos_iff_lt.mpr h, (Nat.sub_le ..).trans_lt hj.2⟩
      have q : n - (j - (k + 1) * j % n) = (k + 1) * j % n + (n - j) % n := by
        rw [tsub_tsub_eq_add_tsub_of_le h.le, add_comm, Nat.add_sub_assoc hj.2.le,
          Nat.mod_eq_of_lt (show n - j < n by omega)]
      rw [hC.1 _ b₂, q, ← Nat.add_mod_of_add_mod_lt (by omega), ← Nat.add_sub_assoc hj.2.le,
        add_comm, Nat.add_sub_assoc (Nat.le_mul_of_pos_left _ hk.1), ← tsub_one_mul,
        Nat.add_mod_left, add_tsub_cancel_right]
    · rw [Int.natAbs_natCast_sub_natCast_of_le h.le, Nat.mod_sub_of_le h.le]
      rw [add_mul, one_mul, add_tsub_cancel_right]

theorem result {n j : ℕ} (hn : 3 ≤ n) (hj : j ∈ Set.Ico 1 n) (cpj : Coprime n j)
    {C : ℕ → Fin 2} (hC : Condition n j C) {i : ℕ} (hi : i ∈ Set.Ico 1 n) :
    C i = C j := by
  obtain ⟨v, hv⟩ := exists_mul_emod_eq_one_of_coprime cpj.symm (by omega)
  have hvi : i = (v * i % n) * j % n := by
    rw [mod_mul_mod, ← mul_rotate, ← mod_mul_mod, hv, one_mul, mod_eq_of_lt hi.2]
  have vib : v * i % n ∈ Set.Ico 1 n := by
    refine ⟨(?_ : 0 < _), mod_lt _ (by omega)⟩
    by_contra! h; rw [le_zero, ← dvd_iff_mod_eq_zero] at h
    rw [mul_comm, ← mod_eq_of_lt (show 1 < n by omega)] at hv
    have i0 := eq_zero_of_dvd_of_lt
      ((coprime_of_mul_modEq_one _ hv).symm.dvd_of_dvd_mul_left h) hi.2
    subst i; simp at hi
  rw [hvi, C_mul_mod hn hj cpj hC vib]

end Imo1985Q2
