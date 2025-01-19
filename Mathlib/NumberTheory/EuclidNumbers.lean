/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Euclid Numbers

This file introduces the Euclid numbers as defined in [knuth1989concrete].
This is sequence [A129871](https://oeis.org/A129871) in [oeis]

## Implementation notes

The reference [knuth1989concrete] names the sequence $(e_n)_{n\ge 1}$ as
*Euclid numbers*, while [oeis] names it
$(e_n)_{n\ge 0}$ as *Sylvester's sequence*. We chose to follow
the notation from [knuth1989concrete].

## Main results

- Recurrence with a product of Euclid numbers.
- Co-primality of Euclid numbers.

## References

* [Concrete Mathematics][knuth1989concrete]
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

namespace Euclid

/--
The sequence of Euclid numbers $(e_n)_{n\ge 0}$.

Definition by a simple recurrence. The more explicit recurrence is proved in
Theorem `euclid_prod_finset_add_one`.
-/
def euclid : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 1 => (euclid n) ^ 2 - (euclid n) + 1

-- The definition conforms to the standard one for the first few examples
@[simp]
theorem euclid_zero : euclid 0 = 1 := by rfl

@[simp]
theorem euclid_one : euclid 1 = 2 := by rfl

@[simp]
theorem euclid_two : euclid 2 = 3 := by rfl

@[simp]
theorem euclid_three : euclid 3 = 7 := by rfl

/--
The Euclid numbers satisfy the recurrence:
$$
e_{n+1} = \prod_{i=1}^n e_i + 1.
$$
-/
theorem euclid_prod_finset_add_one {n : ℕ} :
    euclid (n + 1) = ∏ x ∈ Finset.Icc 1 n, euclid x + 1 := by
  induction' n with n ih
  · simp
  · rw[euclid]
    · simp [Nat.pow_two, Finset.prod_Icc_succ_top]
      rw [← Nat.sub_one_mul]
      congr
      simp [ih]
    · simp

/--
Another expression of `euclid_prod_finset_add_one` for easier application when $n\ge 1$:
$$
e_n = \prod_{i=1}^{n-1} e_i + 1.
$$
-/
theorem euclid_prod_finset_add_one_of_pos {n : ℕ} (h : n ≥ 1) :
    euclid n = ∏ x∈Finset.Icc 1 (n - 1), euclid x + 1 := by
  have c : n = (n - 1) + 1 := by omega
  rw [c, euclid_prod_finset_add_one]
  simp

/--
Euclid numbers are positive.
-/
theorem euclid_gt_zero {n : ℕ} : 0 < euclid n := by
  unfold euclid
  split <;> linarith

theorem euclid_ne_zero {n : ℕ} : NeZero (euclid n) := NeZero.of_pos euclid_gt_zero

/--
Euclid numbers are $\ge 1$.
-/
theorem euclid_ge_one {n : ℕ} : 1 ≤ euclid n := by
  simp [Nat.one_le_iff_ne_zero]
  linarith [@euclid_gt_zero n]

/--
Only $e_0 = 1$.
-/
theorem euclid_gt_one_of_pos {n : ℕ} (h : n ≥ 1) : 1 < euclid n := by
  cases n
  · contradiction
  · simp [euclid_prod_finset_add_one, euclid_gt_zero]

/--
$e_n \equiv 1\ (\mathrm{mod}~e_m)$, when $0 < m < n$.
-/
theorem euclid_mod_eq_one {m n : ℕ} (h1 : m < n) (h2 : 0 < m) :
    euclid n % euclid m = 1 := by
  rw [euclid_prod_finset_add_one_of_pos]
  · have d : (euclid m) ∣  ∏ x ∈ Finset.Icc 1 (n-1), euclid x := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_Icc.mpr (by omega)
    rw [Nat.add_mod]
    simp [Nat.dvd_iff_mod_eq_zero.mp d]
    exact Nat.mod_eq_of_lt <| euclid_gt_one_of_pos <| by linarith
  · linarith

private lemma euclid_coprime_of_lt {m n : ℕ} (h : m < n) :
    Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m = 0
  · simp [c]
  · simp [Nat.Coprime]
    rw [Nat.gcd_rec, euclid_mod_eq_one] <;> first | simp | omega

/--
The Euclid numbers are co-prime: $\gcd(e_n, e_m) = 1$, for $n\neq m$.
-/
theorem euclid_coprime {m n : ℕ} (h : m ≠ n) : Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m < n
  · exact euclid_coprime_of_lt c
  · exact Nat.coprime_comm.mp <| euclid_coprime_of_lt <| by omega

end Euclid
