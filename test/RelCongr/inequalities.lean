/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.RelCongr
import Mathlib.Tactic.SuccessIfFailWithMsg

/-! # Inequality tests for the `rel_congr` tactic -/

open Nat Finset BigOperators

-- We deliberately mock `ℝ` here so that we don't have to import the dependencies
axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.linearOrderedRing : LinearOrderedField ℝ

/-! ## Examples as a finishing tactic -/

example {x : ℤ} (hx : x ≥ 12) : x * x ^ 2 ≥ 12 * x ^ 2 := by rel_congr

example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by rel_congr
example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by rel [hx]

example {x : ℤ} (hx : x > 12) : x * x ^ 2 > 12 * x ^ 2 := by rel_congr

example {x y : ℤ} (hx : x > 12) : y + x * x > y + 12 * x := by rel_congr

-- not solved by `nlinarith` because of the cube
example {n m : ℤ} (hn : n ≥ 10) : n * n ^ 3 - m ≥ 10 * n ^ 3 - m := by rel_congr

example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by rel_congr
example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by rel [hn]

example {x : ℤ} (hx : x ≥ 12) : x ≥ 12 := by rel_congr

example {x y : ℤ} (hx : x ≥ 12) : y + 8 * x ≥ y + 8 * 12 := by rel_congr

example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) : x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]

-- not solved by `nlinarith` because of the cube and the absolute value
example {a b c x  y : ℤ} (hb : b ≥ 4) (hxy : x ≤ y) :
    c + (3 * |a| ^ 3 * b + b * 7 + 14) * x ≤ c + (3 * |a| ^ 3 * b + b * 7 + 14) * y := by
  rel_congr

example {x y : ℤ} (hy : 3 ≤ y) (hx : x ≥ 9) : y + 2 * x ≥ 3 + 2 * 9 := by rel_congr

example {b : ℤ} (h2 : b ≥ 3) : 2 * b + 5 ≥ 2 * 3 + 5 := by rel_congr

example {x : ℝ} (h1 : x ≤ 3) : 4 * x - 3 ≤ 4 * 3 - 3 := by rel_congr

example {x : ℝ} (h : x < 1) : 3 * x ≤ 3 * 1 := by rel_congr

example {x : ℝ} (h1 : x < 3) : 4 * x - 3 < 4 * 3 - 3 := by rel_congr

example {x : ℝ} (h : x < 1) : 3 * x < 3 * 1 := by rel_congr

example {x y : ℝ} (h1 : 1 ≤ y) (h2 : x < 2) : x * y ≤ 2 * y := by rel_congr

-- for this test to pass, need the check to ensure that leading function application is
-- syntactically (not just definitionally) the same on both sides.
example {a b c : ℚ} (h2 : 2 ≤ a + b) : 2 + c ≤ (a + b) + c := by rel_congr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : 4 ≤ b) : (3 + 4) / 2 ≤ (a + b) / 2 := by rel_congr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a : ℚ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by rel_congr

example {a : ℝ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by rel_congr

example {x y : ℝ} (h : 3 ≤ x) (h' : 1 ≤ y) : (3 + 1) / 2 ≤ (x + y) / 2 := by rel_congr

example {x : ℝ} (h : x ≤ 3) : 0.1 * x ≤ 0.1 * 3 := by rel_congr

example {x : ℝ} (h : x ≤ 3) : x / 10 ≤ 3 / 10 := by rel_congr

example {x : ℝ} (h : x ≤ 3) : 1 / 10 * x ≤ 1 / 10 * 3 := by rel_congr

example (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := by rel_congr

-- this tests that the tactic prioritizes applying hypotheses (such as, here, `0 ≤ a ^ 6`) over the
-- greedy application of nonnegativity lemmas
example {a b : ℚ} (h : 0 ≤ a ^ 6) : 0 + b ≤ a ^ 6 + b := by rel_congr

-- another priority test
example {k m n : ℤ}  (H : m ^ 2 ≤ n ^ 2) : k + m ^ 2 ≤ k + n ^ 2 := by rel_congr

example {x : ℤ} (hx : x ≥ 12) (h : Even x) : Even x := by
  success_if_fail_with_msg "rel failed, goal not a relation" (rel [hx])
  exact h

example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 1 ≤ x + 1) : x * a + c ≤ x * b + d := by
  success_if_fail_with_msg
    "rel failed, cannot prove goal by 'substituting' the listed relationships. The steps which could not be automatically justified were: \n0 ≤ x\nc ≤ d"
    (rel [h1])
  have : 0 ≤ x := by linarith
  rel [h1, h2]

/-! ## Non-finishing examples -/

example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel_congr <;> linarith

example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  rel_congr x ^ 2 * ?_ + 5
  linarith

example {x y z : ℝ} (h : 2 ≤ z) : z * |x + y| ≤ z * (|x| + |y|) := by rel_congr; apply abs_add

example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by rel_congr; apply abs_add
example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by rel_congr ?_ + _; apply abs_add
example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by rel_congr ?_ + (A : ℝ); apply abs_add

example {n i : ℕ} (hi : i ∈ range n) : 2 ^ i ≤ 2 ^ n := by
  rel_congr
  · norm_num
  · apply le_of_lt
    simpa using hi

example {n' : ℕ} (hn': 6 ≤ n') : 2 ^ ((n' + 1) * (n' + 1)) ≤ 2 ^ (n' * n' + 4 * n') := by
  rel_congr
  · norm_num
  · linarith

example {F : ℕ → ℕ} (le_sum: ∀ {N : ℕ}, 6 ≤ N → 15 ≤ F N) {n' : ℕ} (hn' : 6 ≤ n') :
    let A := F n';
    A ! * (15 + 1) ^ n' ≤ A ! * (A + 1) ^ n' := by
  intro A
  rel_congr
  exact le_sum hn'

example {a : ℤ} {n : ℕ} (ha : ∀ i < n, 2 ^ i ≤ a) :
    ∏ i in range n, (a - 2 ^ i) ≤ ∏ _i in range n, a := by
  rel_congr with i
  · intro i hi
    simp only [mem_range] at hi
    linarith [ha i hi]
  · have : 0 ≤ 2 ^ i := by positivity
    linarith

-- this tests that the match goes only as deep as is indicated by the template
example {a b c d e : ℝ} (_h1 : 0 ≤ b) (_h2 : 0 ≤ c) (hac : a * b + 1 ≤ c * d + 1) (_hbd : b ≤ d) :
    a * b + e ≤ c * d + e := by
  rel_congr ?_ + _
  guard_target =ₛ a * b ≤ c * d
  linarith

-- this tests templates with binders
example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ^ 2 + 1 ≤ g i ^ 2 + 1) :
    ∑ i in s, f i ^ 2 ≤ ∑ i in s, g i ^ 2 := by
  rel_congr ∑ _i in s, ?_ with i hi
  linarith [h i hi]

-- this tests templates with binders
example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ^ 2 + 1 ≤ g i ^ 2 + 1) :
    ∑ i in s, (3 + f i ^ 2) ≤ ∑ i in s, (3 + g i ^ 2) := by
  rel_congr ∑ _i in s, (3 + ?_) with i hi
  linarith [h i hi]

axiom f : ℕ → ℕ

example {x y : ℕ} (h : f x ≤ f y) : f x ≤ f y := by
  success_if_fail_with_msg
    "rel_congr failed, no @[rel_congr] lemma applies for the template portion f ?a and the relation LE.le"
    (rel_congr f ?a)
  exact h

example {x y : ℕ} (h : f x ≤ f y) : f x ^ 2 ≤ f y ^ 2 := by
  success_if_fail_with_msg
    "rel_congr failed, no @[rel_congr] lemma applies for the template portion f ?a and the relation LE.le"
    (rel_congr (f ?a) ^ 2)
  rel_congr

example (s : Finset ℕ) (h : ∀ i ∈ s, f i ≤ f (2 * i)) : ∑ i in s, f i ≤ ∑ i in s, f (2 * i) := by
  rel_congr
  apply h
  assumption
