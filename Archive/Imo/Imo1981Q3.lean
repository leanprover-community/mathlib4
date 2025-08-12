/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# IMO 1981 Q3

Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.

The trick to this problem is that `m` and `n` have to be consecutive Fibonacci numbers,
because you can reduce any solution to a smaller one using the Fibonacci recurrence.
-/


/-
First, define the problem in terms of finding the maximum of a set.

We first generalize the problem to `{1, 2, ..., N}` and specialize to `N = 1981` at the very end.
-/
open Int Nat Set

namespace Imo1981Q3

variable (N : ℕ)

-- N = 1981
@[mk_iff]
structure ProblemPredicate (m n : ℤ) : Prop where
  m_range : m ∈ Ioc 0 (N : ℤ)
  n_range : n ∈ Ioc 0 (N : ℤ)
  eq_one : (n ^ 2 - m * n - m ^ 2) ^ 2 = 1

def specifiedSet : Set ℤ :=
  {k : ℤ | ∃ m : ℤ, ∃ n : ℤ, k = m ^ 2 + n ^ 2 ∧ ProblemPredicate N m n}

/-
We want to reduce every solution to a smaller solution. Specifically,
we show that when `(m, n)` is a solution, `(n - m, m)` is also a solution,
except for the base case of `(1, 1)`.
-/
namespace ProblemPredicate

variable {N}

theorem m_le_n {m n : ℤ} (h1 : ProblemPredicate N m n) : m ≤ n := by
  by_contra h2
  have h3 : 1 = (n * (n - m) - m ^ 2) ^ 2 := by linear_combination - h1.eq_one
  have h4 : n * (n - m) - m ^ 2 < -1 := by nlinarith [h1.n_range.left]
  have h5 : 1 < (n * (n - m) - m ^ 2) ^ 2 := by nlinarith
  exact h5.ne h3

theorem eq_imp_1 {n : ℤ} (h1 : ProblemPredicate N n n) : n = 1 :=
  have : n * (n * (n * n)) = 1 := by linear_combination h1.eq_one
  eq_one_of_mul_eq_one_right h1.m_range.left.le this

theorem reduction {m n : ℤ} (h1 : ProblemPredicate N m n) (h2 : 1 < n) :
    ProblemPredicate N (n - m) m := by
  obtain (rfl : m = n) | (h3 : m < n) := h1.m_le_n.eq_or_lt
  · have h4 : m = 1 := h1.eq_imp_1
    exact absurd h4.symm h2.ne
  exact
    { n_range := h1.m_range
      m_range := by
        have h5 : 0 < n - m := sub_pos.mpr h3
        have h6 : n - m < N := by
          calc
            _ < n := sub_lt_self n h1.m_range.left
            _ ≤ N := h1.n_range.right
        exact ⟨h5, h6.le⟩
      eq_one := by linear_combination h1.eq_one }

end ProblemPredicate

/-
It will be convenient to have the lemmas above in their natural number form.
Most of these can be proved with the `norm_cast` family of tactics.
-/
def NatPredicate (m n : ℕ) : Prop :=
  ProblemPredicate N ↑m ↑n

namespace NatPredicate

variable {N}

nonrec theorem m_le_n {m n : ℕ} (h1 : NatPredicate N m n) : m ≤ n := mod_cast h1.m_le_n

nonrec theorem eq_imp_1 {n : ℕ} (h1 : NatPredicate N n n) : n = 1 := mod_cast h1.eq_imp_1

nonrec theorem reduction {m n : ℕ} (h1 : NatPredicate N m n) (h2 : 1 < n) :
    NatPredicate N (n - m) m := by
  have : m ≤ n := h1.m_le_n
  exact mod_cast h1.reduction (mod_cast h2)

theorem n_pos {m n : ℕ} (h1 : NatPredicate N m n) : 0 < n := mod_cast h1.n_range.left

theorem m_pos {m n : ℕ} (h1 : NatPredicate N m n) : 0 < m := mod_cast h1.m_range.left

theorem n_le_N {m n : ℕ} (h1 : NatPredicate N m n) : n ≤ N := mod_cast h1.n_range.right

/-
Now we can use induction to show that solutions must be Fibonacci numbers.
-/
theorem imp_fib {n : ℕ} : ∀ m : ℕ, NatPredicate N m n → ∃ k : ℕ, m = fib k ∧ n = fib (k + 1) := by
  refine Nat.strong_induction_on n ?_
  intro n h1 m h2
  have h3 : m ≤ n := h2.m_le_n
  obtain (rfl : 1 = n) | (h4 : 1 < n) := (succ_le_iff.mpr h2.n_pos).eq_or_lt
  · use 1
    have h5 : 1 ≤ m := succ_le_iff.mpr h2.m_pos
    simpa using h3.antisymm h5
  · obtain (rfl : m = n) | (h6 : m < n) := h3.eq_or_lt
    · exact absurd h2.eq_imp_1 (Nat.ne_of_gt h4)
    · have h7 : NatPredicate N (n - m) m := h2.reduction h4
      obtain ⟨k : ℕ, hnm : n - m = fib k, rfl : m = fib (k + 1)⟩ := h1 m h6 (n - m) h7
      use k + 1, rfl
      rw [fib_add_two, ← hnm, tsub_add_cancel_of_le h3]

end NatPredicate

/-
Next, we prove that if `N < fib K + fib (K+1)`, then the largest `m` and `n`
satisfying `NatPredicate m n N` are `fib K` and `fib (K+1)`, respectively.
-/
variable {K : ℕ} (HK : N < fib K + fib (K + 1)) {N}

include HK in
theorem m_n_bounds {m n : ℕ} (h1 : NatPredicate N m n) : m ≤ fib K ∧ n ≤ fib (K + 1) := by
  obtain ⟨k : ℕ, hm : m = fib k, hn : n = fib (k + 1)⟩ := h1.imp_fib m
  by_cases h2 : k < K + 1
  · have h3 : k ≤ K := Nat.lt_succ_iff.mp h2
    constructor
    · calc
        m = fib k := hm
        _ ≤ fib K := fib_mono h3
    · have h6 : k + 1 ≤ K + 1 := succ_le_succ h3
      calc
        n = fib (k + 1) := hn
        _ ≤ fib (K + 1) := fib_mono h6
  · have h7 : N < n := by
      have h8 : K + 2 ≤ k + 1 := succ_le_succ (not_lt.mp h2)
      rw [← fib_add_two] at HK
      calc
        N < fib (K + 2) := HK
        _ ≤ fib (k + 1) := fib_mono h8
        _ = n := hn.symm
    have h9 : n ≤ N := h1.n_le_N
    exact absurd h7 h9.not_gt

/-
We spell out the consequences of this result for `specifiedSet N` here.
-/
variable {M : ℕ} (HM : M = fib K ^ 2 + fib (K + 1) ^ 2)
include HK HM

theorem k_bound {m n : ℤ} (h1 : ProblemPredicate N m n) : m ^ 2 + n ^ 2 ≤ M := by
  have h2 : 0 ≤ m := h1.m_range.left.le
  have h3 : 0 ≤ n := h1.n_range.left.le
  rw [← natAbs_of_nonneg h2, ← natAbs_of_nonneg h3] at h1; clear h2 h3
  obtain ⟨h4 : m.natAbs ≤ fib K, h5 : n.natAbs ≤ fib (K + 1)⟩ := m_n_bounds HK h1
  have h6 : m ^ 2 ≤ (fib K : ℤ) ^ 2 := Int.natAbs_le_iff_sq_le.mp h4
  have h7 : n ^ 2 ≤ (fib (K + 1) : ℤ) ^ 2 := Int.natAbs_le_iff_sq_le.mp h5
  linarith

theorem solution_bound : ∀ {k : ℤ}, k ∈ specifiedSet N → k ≤ M
  | _, ⟨_, _, rfl, h⟩ => k_bound HK HM h

theorem solution_greatest (H : ProblemPredicate N (fib K) (fib (K + 1))) :
    IsGreatest (specifiedSet N) M :=
  ⟨⟨fib K, fib (K + 1), by simp [HM], H⟩, fun k h => solution_bound HK HM h⟩

end Imo1981Q3

open Imo1981Q3

/-
Now we just have to demonstrate that 987 and 1597 are in fact the largest Fibonacci
numbers in this range, and thus provide the maximum of `specifiedSet`.
-/
theorem imo1981_q3 : IsGreatest (specifiedSet 1981) 3524578 := by
  have := fun h => @solution_greatest 1981 16 h 3524578
  simp +decide at this
  apply this
  simp +decide [problemPredicate_iff]
