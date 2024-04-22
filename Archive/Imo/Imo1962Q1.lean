/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Mathlib.Data.Nat.Digits

#align_import imo.imo1962_q1 from "leanprover-community/mathlib"@"2d6f88c296da8df484d7f5b9ee1d10910ab473a2"

/-!
# IMO 1962 Q1

Find the smallest natural number $n$ which has the following properties:

(a) Its decimal representation has 6 as the last digit.

(b) If the last digit 6 is erased and placed in front of the remaining digits,
the resulting number is four times as large as the original number $n$.

Since Lean does not explicitly express problems of the form "find the smallest number satisfying X",
we define the problem as a predicate, and then prove a particular number is the smallest member
of a set satisfying it.
-/


namespace Imo1962Q1

open Nat

def ProblemPredicate (n : ℕ) : Prop :=
  (digits 10 n).headI = 6 ∧ ofDigits 10 ((digits 10 n).tail.concat 6) = 4 * n
#align imo1962_q1.problem_predicate Imo1962Q1.ProblemPredicate

/-!
First, it's inconvenient to work with digits, so let's simplify them out of the problem.
-/


abbrev ProblemPredicate' (c n : ℕ) : Prop :=
  n = 10 * c + 6 ∧ 6 * 10 ^ (digits 10 c).length + c = 4 * n
#align imo1962_q1.problem_predicate' Imo1962Q1.ProblemPredicate'

theorem without_digits {n : ℕ} (h1 : ProblemPredicate n) : ∃ c : ℕ, ProblemPredicate' c n := by
  use n / 10
  cases' n with n
  · have h2 : ¬ProblemPredicate 0 := by norm_num [ProblemPredicate]
    contradiction
  · rw [ProblemPredicate, digits_def' (by decide : 2 ≤ 10) n.succ_pos, List.headI, List.tail_cons,
      List.concat_eq_append] at h1
    constructor
    · rw [← h1.left, div_add_mod (n + 1) 10]
    · rw [← h1.right, ofDigits_append, ofDigits_digits, ofDigits_singleton, add_comm, mul_comm]
#align imo1962_q1.without_digits Imo1962Q1.without_digits

/-!
Now we can eliminate possibilities for `(digits 10 c).length` until we get to the one that works.
-/


theorem case_0_digit {c n : ℕ} (h1 : (digits 10 c).length = 0) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 0 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 0 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  linarith
#align imo1962_q1.case_0_digit Imo1962Q1.case_0_digit

theorem case_1_digit {c n : ℕ} (h1 : (digits 10 c).length = 1) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 1 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 1 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  have h6 : c > 0 := by linarith
  linarith
#align imo1962_q1.case_1_digit Imo1962Q1.case_1_digit

theorem case_2_digit {c n : ℕ} (h1 : (digits 10 c).length = 2) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 2 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 2 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  have h5 : c > 14 := by linarith
  linarith
#align imo1962_q1.case_2_digit Imo1962Q1.case_2_digit

theorem case_3_digit {c n : ℕ} (h1 : (digits 10 c).length = 3) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 3 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 3 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  have h5 : c > 153 := by linarith
  linarith
#align imo1962_q1.case_3_digit Imo1962Q1.case_3_digit

theorem case_4_digit {c n : ℕ} (h1 : (digits 10 c).length = 4) : ¬ProblemPredicate' c n := by
  intro h2
  have h3 : 6 * 10 ^ 4 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 4 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  have h5 : c > 1537 := by linarith
  linarith
#align imo1962_q1.case_4_digit Imo1962Q1.case_4_digit

/-- Putting this inline causes a deep recursion error, so we separate it out. -/
theorem helper_5_digit {c : ℤ} (h : 6 * 10 ^ 5 + c = 4 * (10 * c + 6)) : c = 15384 := by linarith
#align imo1962_q1.helper_5_digit Imo1962Q1.helper_5_digit

theorem case_5_digit {c n : ℕ} (h1 : (digits 10 c).length = 5) (h2 : ProblemPredicate' c n) :
    c = 15384 := by
  have h3 : 6 * 10 ^ 5 + c = 6 * 10 ^ (digits 10 c).length + c := by rw [h1]
  have h4 : 6 * 10 ^ 5 + c = 4 * (10 * c + 6) := by rw [h3, h2.right, h2.left]
  zify at *
  exact helper_5_digit h4
#align imo1962_q1.case_5_digit Imo1962Q1.case_5_digit

/-- `linarith` fails on numbers this large, so this lemma spells out some of the arithmetic
that normally would be automated.
-/
theorem case_more_digits {c n : ℕ} (h1 : (digits 10 c).length ≥ 6) (h2 : ProblemPredicate' c n) :
    n ≥ 153846 := by
  have h3 : c ≠ 0 := by
    intro h4
    have h5 : (digits 10 c).length = 0 := by simp [h4]
    exact case_0_digit h5 h2
  calc
    n ≥ 10 * c := le.intro h2.left.symm
    _ ≥ 10 ^ (digits 10 c).length := base_pow_length_digits_le 10 c (by decide) h3
    _ ≥ 10 ^ 6 := pow_le_pow_right (by decide) h1
    _ ≥ 153846 := by norm_num
#align imo1962_q1.case_more_digits Imo1962Q1.case_more_digits

/-!
Now we combine these cases to show that 153846 is the smallest solution.
-/


theorem satisfied_by_153846 : ProblemPredicate 153846 := by
  norm_num [ProblemPredicate]
  decide
#align imo1962_q1.satisfied_by_153846 Imo1962Q1.satisfied_by_153846

theorem no_smaller_solutions (n : ℕ) (h1 : ProblemPredicate n) : n ≥ 153846 := by
  have ⟨c, h2⟩ := without_digits h1
  have h3 : (digits 10 c).length < 6 ∨ (digits 10 c).length ≥ 6 := by apply lt_or_ge
  cases h3 with
  | inr h3 => exact case_more_digits h3 h2
  | inl h3 =>
    interval_cases h : (digits 10 c).length
    · exfalso; exact case_0_digit h h2
    · exfalso; exact case_1_digit h h2
    · exfalso; exact case_2_digit h h2
    · exfalso; exact case_3_digit h h2
    · exfalso; exact case_4_digit h h2
    · have h4 : c = 15384 := case_5_digit h h2
      have h5 : n = 10 * 15384 + 6 := h4 ▸ h2.left
      norm_num at h5
      exact h5.ge
#align imo1962_q1.no_smaller_solutions Imo1962Q1.no_smaller_solutions

end Imo1962Q1

open Imo1962Q1

theorem imo1962_q1 : IsLeast {n | ProblemPredicate n} 153846 :=
  ⟨satisfied_by_153846, no_smaller_solutions⟩
#align imo1962_q1 imo1962_q1
