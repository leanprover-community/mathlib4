/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Sylvester's sequence

This file introduces the Sylvester's sequence.
This is sequence [A000058](https://oeis.org/A000058) in [oeis].

## Implementation notes

We follow the presentantion from [Wikipedia](https://en.wikipedia.org/wiki/Sylvester%27s_sequence).

## Main results

- Basic facts: the first terms of the sequence are 2, 3, 7, 43.
- `sylvester_prod_finset_add_one`: each term of the sequence is one plus the product of its
  predecessors.
- `sylvester_strictMono`: the sequence is strictly monotonic.
- `sylvester_coprime`: Pairwise co-primality.

## References

* <https://en.wikipedia.org/wiki/Sylvester%27s_sequence>
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

open Nat

/-- Sylvester's sequence: https://oeis.org/A000058. -/
def sylvesterSequence : ℕ → ℕ
  | 0 => 2
  | n + 1 => (sylvesterSequence n) * (sylvesterSequence n - 1) + 1

@[simp]
theorem sylvester_zero : sylvesterSequence 0 = 2 := rfl

@[simp]
theorem sylvester_one : sylvesterSequence 1 = 3 := rfl

@[simp]
theorem sylvester_two : sylvesterSequence 2 = 7 := rfl

@[simp]
theorem sylvester_three : sylvesterSequence 3 = 43 := rfl

theorem two_le_sylvester (n : ℕ) : 2 ≤ sylvesterSequence n := by
  induction' n with n ih
  · simp
  · simp only [sylvesterSequence, reduceLeDiff]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

/--
This recurrence motivates the alternative name of **Euclid numbers**:
$$
\mathrm{sylvester}~n = 1 + \prod_{i=0}^{n-1} \mathrm{sylvester}~i,
$$
assuming the product over the empty set to be 1.
-/
theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvesterSequence n = ∏ i ∈ Finset.range n, sylvesterSequence i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvesterSequence n - 1)]
  · exact (Nat.sub_one_add_one (by linarith [two_le_sylvester n])).symm
  · norm_num
  · simp [sylvesterSequence, mul_comm]

theorem sylvester_strictMono : StrictMono sylvesterSequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sylvesterSequence]
  calc
    sylvesterSequence n * (sylvesterSequence n - 1) + 1 >
      sylvesterSequence n * (sylvesterSequence n - 1) := by linarith
    _ ≥ sylvesterSequence n := Nat.le_mul_of_pos_right _ <| le_sub_one_of_lt <| two_le_sylvester n

/-!
### Coprimality
-/

theorem sylvester_mod_eq_one {m n : ℕ} (h : m < n) :
    sylvesterSequence n % sylvesterSequence m = 1 := by
  rw [sylvester_prod_finset_add_one, ← mod_add_mod,
    dvd_iff_mod_eq_zero.mp (Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr h)]
  exact Nat.mod_eq_of_lt <| two_le_sylvester _

private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvesterSequence m) (sylvesterSequence n) := by
  rw [Coprime, Nat.gcd_rec, sylvester_mod_eq_one h, gcd_one_left]

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) :
    Coprime (sylvesterSequence m) (sylvesterSequence n) := by
  rcases h.lt_or_lt with c | c
  · exact sylvester_coprime_of_lt c
  · exact (sylvester_coprime_of_lt c).symm
