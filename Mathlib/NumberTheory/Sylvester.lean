/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Init.Data.List.Nat.Pairwise
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Sylvester sequence

This file introduces the Sylvester's sequence.
This is sequence [A000058](https://oeis.org/A000058) in [oeis].

## Implementation notes

We follow the presentantion from [Wikipedia](https://en.wikipedia.org/wiki/Sylvester%27s_sequence).

## Main results

- Basic facts.
- Recurrence formula.
- Sylvester sequence is strictly monotonic.
- Pairwise co-primality.

## References

* <https://en.wikipedia.org/wiki/Sylvester%27s_sequence>
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

open Nat

/--
Sylvester sequence: https://oeis.org/A000058.
-/
def sylvester : ℕ -> ℕ
  | 0 => 2
  | n + 1 => (sylvester n) * (sylvester n - 1) + 1

@[simp]
theorem sylvester_zero : sylvester 0 = 2 := by rfl

@[simp]
theorem sylvester_one : sylvester 1 = 3 := by rfl

@[simp]
theorem sylvester_two : sylvester 2 = 7 := by rfl

@[simp]
theorem sylvester_three : sylvester 3 = 43 := by rfl

theorem sylvester_ge_two (n : ℕ) : 2 ≤ sylvester n := by
  induction' n with n ih
  · simp
  · simp only [sylvester, reduceLeDiff]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

/--
This recurrence motivates the alternative name of **Euclid numbers**:
$$
\mathrm{sylvester}~n = 1 + \prod_{i=0}^{n-1} \mathrm{sylvester}~i,
$$
assuming the product over the empty set to be 1.
-/
theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvester n = ∏ i ∈ Finset.range n, sylvester i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvester n - 1)]
  · exact (Nat.sub_one_add_one (by linarith [sylvester_ge_two n])).symm
  · norm_num
  · simp [sylvester, mul_comm]

theorem sylvester_strictMono : StrictMono sylvester := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sylvester]
  calc
    sylvester n * (sylvester n - 1) + 1 > sylvester n * (sylvester n - 1) := by linarith
    _ ≥ sylvester n := Nat.le_mul_of_pos_right _ <| le_sub_one_of_lt <| sylvester_ge_two n

-- Coprimality

theorem sylvester_mod_eq_one {m n : ℕ} (h : m < n) :
    sylvester n % sylvester m = 1 := by
  rw [sylvester_prod_finset_add_one, Nat.add_mod]
  simp only [add_mod_mod, mod_add_mod, Nat.dvd_iff_mod_eq_zero.mp
    (Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr ((by omega) : m < n))]
  exact Nat.mod_eq_of_lt <| sylvester_ge_two _

private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvester m) (sylvester n) := by
  rw [Coprime, Nat.gcd_rec, sylvester_mod_eq_one]
  · simp only [gcd_one_left]
  · trivial

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) : Coprime (sylvester m) (sylvester n) := by
  by_cases c : m < n
  · exact sylvester_coprime_of_lt c
  · exact coprime_comm.mp <| sylvester_coprime_of_lt <| by omega
