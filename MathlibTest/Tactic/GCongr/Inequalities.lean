/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Tactic.NormNum.OfScientific

namespace GCongrTests

private axiom test_sorry : ∀ {α}, α
/-! # Inequality tests for the `gcongr` tactic -/

open Nat Finset

-- We deliberately mock `ℝ` here so that we don't have to import the dependencies
axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.field : Field ℝ
@[instance] axiom Real.linearOrder : LinearOrder ℝ
@[instance] axiom Real.isStrictOrderedRing : IsStrictOrderedRing ℝ

/-! ## Examples as a finishing tactic -/

example {x : ℤ} (hx : x ≥ 12) : x * x ^ 2 ≥ 12 * x ^ 2 := by gcongr

example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by gcongr
example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by rel [hx]

example {x : ℤ} (hx : x > 12) : x * x ^ 2 > 12 * x ^ 2 := by gcongr

example {x y : ℤ} (hx : x > 12) : y + x * x > y + 12 * x := by gcongr

-- not solved by `nlinarith` because of the cube
example {n m : ℤ} (hn : n ≥ 10) : n * n ^ 3 - m ≥ 10 * n ^ 3 - m := by gcongr

example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by gcongr
example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by rel [hn]

example {x : ℤ} (hx : x ≥ 12) : x ≥ 12 := by gcongr

example {x y : ℤ} (hx : x ≥ 12) : y + 8 * x ≥ y + 8 * 12 := by gcongr

example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) : x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]

-- not solved by `nlinarith` because of the cube and the absolute value
example {a b c x y : ℤ} (hb : b ≥ 4) (hxy : x ≤ y) :
    c + (3 * |a| ^ 3 * b + b * 7 + 14) * x ≤ c + (3 * |a| ^ 3 * b + b * 7 + 14) * y := by
  gcongr

example {x y : ℤ} (hy : 3 ≤ y) (hx : x ≥ 9) : y + 2 * x ≥ 3 + 2 * 9 := by gcongr

example {b : ℤ} (h2 : b ≥ 3) : 2 * b + 5 ≥ 2 * 3 + 5 := by gcongr

example {x : ℝ} (h1 : x ≤ 3) : 4 * x - 3 ≤ 4 * 3 - 3 := by gcongr

example {x : ℝ} (h : x < 1) : 3 * x ≤ 3 * 1 := by gcongr

example {x : ℝ} (h1 : x < 3) : 4 * x - 3 < 4 * 3 - 3 := by gcongr

example {x : ℝ} (h : x < 1) : 3 * x < 3 * 1 := by gcongr

example {x y : ℝ} (h1 : 1 ≤ y) (h2 : x < 2) : x * y ≤ 2 * y := by gcongr

-- for this test to pass, need the check to ensure that leading function application is
-- syntactically (not just definitionally) the same on both sides.
example {a b c : ℚ} (h2 : 2 ≤ a + b) : 2 + c ≤ (a + b) + c := by gcongr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : 4 ≤ b) : (3 + 4) / 2 ≤ (a + b) / 2 := by gcongr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a : ℚ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by gcongr

example {a : ℝ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by gcongr

example {x y : ℝ} (h : 3 ≤ x) (h' : 1 ≤ y) : (3 + 1) / 2 ≤ (x + y) / 2 := by gcongr

example {x : ℝ} (h : x ≤ 3) : 0.1 * x ≤ 0.1 * 3 := by gcongr

example {x : ℝ} (h : x ≤ 3) : x / 10 ≤ 3 / 10 := by gcongr

example {x : ℝ} (h : x ≤ 3) : 1 / 10 * x ≤ 1 / 10 * 3 := by gcongr

example (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := by gcongr

-- this tests that the tactic prioritizes applying hypotheses (such as, here, `0 ≤ a ^ 6`) over the
-- greedy application of nonnegativity lemmas
example {a b : ℚ} (h : 0 ≤ a ^ 6) : 0 + b ≤ a ^ 6 + b := by gcongr

example {a b : ℚ} (h₁ : a ≤ b) (c : ℝ) : (a + c : ℝ) ≤ b + c := by gcongr

example {a b : ℚ} (h₁ : a < b) (c : ℝ) : (a + c : ℝ) < b + c := by gcongr

-- another priority test
example {k m n : ℤ} (H : m ^ 2 ≤ n ^ 2) : k + m ^ 2 ≤ k + n ^ 2 := by gcongr

-- test of behaviour when no lemmas are applicable
example (n k : ℕ) (H : n % k + 1 ≤ k % n + 1) : n % k ≤ k % n := by
  success_if_fail_with_msg
    "gcongr did not make progress"
    (gcongr)
  linarith

set_option linter.unusedVariables false in
example {x : ℤ} (hx : x ≥ 12) (h : Even x) : Even x := by
  success_if_fail_with_msg "rel failed, goal not a relation" (rel [hx])
  exact h

example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 1 ≤ x + 1) : x * a + c ≤ x * b + d := by
  success_if_fail_with_msg
    "rel failed, cannot prove goal by 'substituting' the listed relationships. \
     The steps which could not be automatically justified were:\n0 ≤ x\nc ≤ d"
    (rel [h1])
  have : 0 ≤ x := by linarith
  rel [h1, h2]

-- test for a missing `withContext`
example {x y : ℚ} {n : ℕ} (hx : 0 ≤ x) (hn : 0 < n) : y ≤ x := by
  have h : x < y := test_sorry
  have _this : x ^ n < y ^ n := by
    rel [h] -- before bugfix: complained "unknown identifier 'h'"
  exact test_sorry

/-! ## Non-finishing examples -/

example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr <;> linarith

example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith

example {x y z : ℝ} (h : 2 ≤ z) : z * |x + y| ≤ z * (|x| + |y|) := by gcongr; apply abs_add_le

example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by gcongr; apply abs_add_le
example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by gcongr ?_ + _; apply abs_add_le
example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by gcongr ?_ + (C : ℝ); apply abs_add_le

example {n i : ℕ} (hi : i ∈ range n) : 2 ^ i ≤ 2 ^ n := by
  gcongr
  · norm_num
  · apply le_of_lt
    simpa using hi

example {n' : ℕ} (hn' : 6 ≤ n') : 2 ^ ((n' + 1) * (n' + 1)) ≤ 2 ^ (n' * n' + 4 * n') := by
  gcongr
  · norm_num
  · linarith

example {F : ℕ → ℕ} (le_sum : ∀ {N : ℕ}, 6 ≤ N → 15 ≤ F N) {n' : ℕ} (hn' : 6 ≤ n') :
    let A := F n'
    ;A ! * (15 + 1) ^ n' ≤ A ! * (A + 1) ^ n' := by
  intro A
  gcongr
  exact le_sum hn'

example {a : ℤ} {n : ℕ} (ha : ∀ i < n, 2 ^ i ≤ a) :
    ∏ i ∈ range n, (a - 2 ^ i) ≤ ∏ _i ∈ range n, a := by
  gcongr with i
  · intro i hi
    simp only [mem_range] at hi
    linarith [ha i hi]
  · have : 0 ≤ 2 ^ i := by positivity
    linarith

-- this tests that the match goes only as deep as is indicated by the template
example {a b c d e : ℝ} (_h1 : 0 ≤ b) (_h2 : 0 ≤ c) (hac : a * b + 1 ≤ c * d + 1) (_hbd : b ≤ d) :
    a * b + e ≤ c * d + e := by
  gcongr ?_ + _
  guard_target =ₛ a * b ≤ c * d
  linarith

-- test big operators
example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, (3 + f i ^ 2) ≤ ∑ i ∈ s, (3 + g i ^ 2) := by
  gcongr with i hi
  exact h i hi

-- this tests templates with binders
example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ^ 2 + 1 ≤ g i ^ 2 + 1) :
    ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, g i ^ 2 := by
  gcongr ∑ _i ∈ s, ?_ with i hi
  linarith [h i hi]

-- this tests templates with binders
example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ^ 2 + 1 ≤ g i ^ 2 + 1) :
    ∑ i ∈ s, (3 + f i ^ 2) ≤ ∑ i ∈ s, (3 + g i ^ 2) := by
  gcongr ∑ _i ∈ s, (3 + ?_) with i hi
  linarith [h i hi]

example (f g : ℕ → ℕ) (s : Finset ℕ) (h : ∀ i ∈ s, f i ^ 2 + 1 ≤ g i ^ 2 + 1) :
    ∑ i ∈ s, (f i ^ 2 / 5) ≤ ∑ i ∈ s, (g i ^ 2 / 5) := by
  gcongr 2 with i hi
  linarith [h i hi]

axiom f : ℕ → ℕ

example {x y : ℕ} (h : f x ≤ f y) : f x ≤ f y := by
  success_if_fail_with_msg
    "Tactic `gcongr` failed: there is no `@[gcongr]` lemma for relation 'LE.le' and constant 'GCongrTests.f'.

x y : ℕ
h : GCongrTests.f x ≤ GCongrTests.f y
⊢ GCongrTests.f x ≤ GCongrTests.f y"
    (gcongr f ?a)
  exact h

example {x y : ℕ} (h : f x ≤ f y) : f x ^ 2 ≤ f y ^ 2 := by
  success_if_fail_with_msg
    "Tactic `gcongr` failed: there is no `@[gcongr]` lemma for relation 'LE.le' and constant 'GCongrTests.f'.

case hab
x y : ℕ
h : GCongrTests.f x ≤ GCongrTests.f y
⊢ GCongrTests.f x ≤ GCongrTests.f y"
    (gcongr (f ?a) ^ 2)
  gcongr

example (s : Finset ℕ) (h : ∀ i ∈ s, f i ≤ f (2 * i)) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, f (2 * i) := by
  gcongr
  apply h
  assumption

def dontUnfoldMe : Nat → List Bool → Nat
  | 0, _ => 0
  | n + 1, l => dontUnfoldMe n (true::l) + dontUnfoldMe n (false::l)

-- times out if a certain reducibility setting in `gcongr`'s implementation is not correct
example {x y : ℕ} (h : x ≤ y) (l) : dontUnfoldMe 14 l + x ≤ 0 + y := by
  gcongr
  guard_target = dontUnfoldMe 14 l ≤ 0
  apply test_sorry

/-! Test that `gcongr` works well with proof arguments -/

example {α β : Type*} [SemilatticeSup α] (f : β → α)
    {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) :
    s₁.sup' h₁ f ≤ s₂.sup' (h₁.mono h) f := by
  gcongr

example {α β : Type*} [SemilatticeSup α] (f : β → α)
    {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    s₁.sup' h₁ f ≤ s₂.sup' h₂ f := by
  gcongr

/-! Test that `gcongr` can solve side goals of the form `∀ i, f i` when `f i` is in scope for
`positivity` -/

example {ι : Type*} [Fintype ι] {f g : ι → ℝ} : ∏ i, f i ^ 2 ≤ ∏ i, g i ^ 2 := by
  gcongr with i _ i _
  · guard_target = 0 ≤ f i
    exact test_sorry
  · guard_target = f i ≤ g i
    exact test_sorry

/-! Test that `gcongr` can deal with `_ ≤ _ → _ ≤ _` and `_ < _ → _ < _` -/

example {a b : ℕ} (h1 : a ≤ 0) (h2 : 0 ≤ b)  : b ≤ a + 1 → 0 ≤ 0 + 1 := by gcongr
example {a b : ℕ} (h1 : a ≤ 0) (_h2 : 0 ≤ b) : b ≤ a + 1 → b ≤ 0 + 1 := by gcongr
example {a b : ℕ} (_h1 : a ≤ 0) (h2 : 0 ≤ b) : b ≤ a + 1 → 0 ≤ a + 1 := by gcongr

example {a b : ℕ} (h1 : a ≤ 0) (h2 : 0 ≤ b)  : b < a + 1 → 0 < 0 + 1 := by gcongr
example {a b : ℕ} (h1 : a ≤ 0) (_h2 : 0 ≤ b) : b < a + 1 → b < 0 + 1 := by gcongr
example {a b : ℕ} (_h1 : a ≤ 0) (h2 : 0 ≤ b) : b < a + 1 → 0 < a + 1 := by gcongr

/-! Test that `gcongr` with a pattern doesn't complain about type class inference problems. -/

example {a b : ℕ} (h1 : a ≤ 0) (h2 : 0 ≤ b) : b ≤ a + 1 → 0 ≤ 0 + 1 := by gcongr ?_ ≤ ?_ + _

/-! Test that `Monotone` and friends can be tagged with `@[gcongr]` -/

def myCons (_ : Nat) : Nat := 0
theorem myCons_monotone : Monotone myCons := fun _ _ _ => le_rfl
theorem myCons_monotone' : Monotone (myCons ·) := fun _ _ _ => le_rfl
theorem myCons_antitone : Antitone myCons := fun _ _ _ => le_rfl
theorem myCons_monotoneOn : MonotoneOn myCons (Set.Ioi 0) := fun _ _ _ _ _ => le_rfl
theorem myCons_antitoneOn : AntitoneOn myCons (Set.Ioi 0) := fun _ _ _ _ _ => le_rfl

attribute [local gcongr] myCons_monotone in
example : myCons 4 ≤ myCons 5 := by
  gcongr; simp

attribute [local gcongr] myCons_monotone' in
example : myCons 4 ≤ myCons 5 := by
  gcongr; simp

attribute [local gcongr] myCons_antitone in
example : myCons 6 ≤ myCons 5 := by
  gcongr; simp

attribute [local gcongr] myCons_monotoneOn in
example : myCons 4 ≤ myCons 5 := by
  gcongr <;> simp

attribute [local gcongr] myCons_antitoneOn in
example : myCons 6 ≤ myCons 5 := by
  gcongr <;> simp

def myMono (n : Nat) : Nat := n
theorem myMono_strictMono : StrictMono myMono := fun _ _ => id
theorem myMono_strictMonoOn : StrictMonoOn myMono (Set.Ioi 0) := fun _ _ _ _ => id

attribute [local gcongr] myMono_strictMono in
example : myMono 4 < myMono 5 := by
  gcongr; simp

attribute [local gcongr] myMono_strictMonoOn in
example : myMono 4 < myMono 5 := by
  gcongr <;> simp

def myAnti (n : Int) : Int := -n
theorem myAnti_strictAnti : StrictAnti myAnti := fun _ _ => neg_lt_neg
theorem myAnti_strictAntiOn : StrictAntiOn myAnti (Set.Ioi 0) := fun _ _ _ _ => neg_lt_neg

attribute [local gcongr] myAnti_strictAnti in
example : myAnti 6 < myAnti 5 := by
  gcongr; simp

attribute [local gcongr] myAnti_strictAntiOn in
example : myAnti 6 < myAnti 5 := by
  gcongr <;> simp

end GCongrTests
