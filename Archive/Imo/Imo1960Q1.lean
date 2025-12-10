/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# IMO 1960 Q1

Determine all three-digit numbers $N$ having the property that $N$ is divisible by 11, and
$\dfrac{N}{11}$ is equal to the sum of the squares of the digits of $N$.

Since Lean doesn't have a way to directly express problem statements of the form
"Determine all X satisfying Y", we express two predicates where proving that one implies the
other is equivalent to solving the problem. A human solver also has to discover the
second predicate.

The strategy here is roughly brute force, checking the possible multiples of 11.
-/


open Nat

namespace Imo1960Q1

def sumOfSquares (L : List ℕ) : ℕ :=
  (L.map fun x => x * x).sum

def ProblemPredicate (n : ℕ) : Prop :=
  (Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧ n / 11 = sumOfSquares (Nat.digits 10 n)

def SolutionPredicate (n : ℕ) : Prop :=
  n = 550 ∨ n = 803

/-
Proving that three digit numbers are the ones in [100, 1000).
-/
theorem not_zero {n : ℕ} (h1 : ProblemPredicate n) : n ≠ 0 :=
  have h2 : Nat.digits 10 n ≠ List.nil := List.ne_nil_of_length_eq_add_one h1.left
  digits_ne_nil_iff_ne_zero.mp h2

theorem ge_100 {n : ℕ} (h1 : ProblemPredicate n) : 100 ≤ n := by
  have h2 : 10 ^ 3 ≤ 10 * n := by
    rw [← h1.left]
    refine Nat.base_pow_length_digits_le 10 n ?_ (not_zero h1)
    simp
  omega

theorem lt_1000 {n : ℕ} (h1 : ProblemPredicate n) : n < 1000 := by
  have h2 : n < 10 ^ 3 := by
    rw [← h1.left]
    refine Nat.lt_base_pow_length_digits ?_
    simp
  omega

/-
We do an exhaustive search to show that all results are covered by `SolutionPredicate`.
-/
def SearchUpTo (c n : ℕ) : Prop :=
  n = c * 11 ∧ ∀ m : ℕ, m < n → ProblemPredicate m → SolutionPredicate m

theorem searchUpTo_start : SearchUpTo 9 99 :=
  ⟨rfl, fun n h p => by linarith [ge_100 p]⟩

theorem searchUpTo_step {c n} (H : SearchUpTo c n) {c' n'} (ec : c + 1 = c') (en : n + 11 = n') {l}
    (el : Nat.digits 10 n = l) (H' : c = sumOfSquares l → c = 50 ∨ c = 73) : SearchUpTo c' n' := by
  subst ec; subst en; subst el
  obtain ⟨rfl, H⟩ := H
  refine ⟨by ring, fun m l p => ?_⟩
  obtain ⟨h₁, ⟨m, rfl⟩, h₂⟩ := id p
  by_cases h : 11 * m < c * 11; · exact H _ h p
  obtain rfl : m = c := by omega
  rw [Nat.mul_div_cancel_left _ (by simp : 11 > 0), mul_comm] at h₂
  refine (H' h₂).imp ?_ ?_ <;> · rintro rfl; norm_num

theorem searchUpTo_end {c} (H : SearchUpTo c 1001) {n : ℕ} (ppn : ProblemPredicate n) :
    SolutionPredicate n :=
  H.2 _ (by linarith [lt_1000 ppn]) ppn

theorem right_direction {n : ℕ} : ProblemPredicate n → SolutionPredicate n := by
  have := searchUpTo_start
  iterate 82
    replace :=
      searchUpTo_step this (by norm_num1; rfl) (by norm_num1; rfl) rfl
        (by simp +decide)
  exact searchUpTo_end this

/-
Now we just need to prove the equivalence, for the precise problem statement.
-/
theorem left_direction (n : ℕ) (spn : SolutionPredicate n) : ProblemPredicate n := by
  rcases spn with (rfl | rfl) <;> refine ⟨?_, by decide, ?_⟩ <;> norm_num <;> rfl

end Imo1960Q1

open Imo1960Q1

theorem imo1960_q1 (n : ℕ) : ProblemPredicate n ↔ SolutionPredicate n :=
  ⟨right_direction, left_direction n⟩
