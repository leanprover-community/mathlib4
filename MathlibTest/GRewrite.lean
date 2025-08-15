/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/- In many examples in this module, we rewrite expressions which do not make it into the final term.

This only happens because we are writing tests where we resolve the goal with a universal axiom, it
would not happen in real proofs, so we disable the resulting linter warnings.
-/
set_option linter.unusedVariables false

private axiom test_sorry : ∀ {α}, α

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (a b c d e : α)

section inequalities

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a + 5 ≤ c + 6 := by
  grw [h₁, h₂]
  guard_target =ₛ c + 5 ≤ c + 6
  grw [show (5 : α) < 6 by norm_num]

example (h₁ : a ≤ b) (h₂ : b ≤ c) : c + 6 > a + 5 := by
  grw [h₁, h₂]
  guard_target =ₛ c + 6 > c + 5
  exact test_sorry

example (h₁ : c ≤ b) : a + 5 ≤ b + 6 := by
  grw [← h₁]
  guard_target =ₛ a + 5 ≤ c + 6
  exact test_sorry

example (h₁ : c ≤ b) (h₂ : a + 5 < c + 6) : a + 5 < b + 6 := by
  grw [← h₁]
  guard_target =ₛ a + 5 < c + 6
  exact h₂

example (h₁ : a + e ≤ b + e) (h₂ : b < c) (h₃ : c ≤ d) : a + e ≤ d + e := by
  grw [h₂, h₃] at h₁
  guard_hyp h₁ :ₛ a + e ≤ d + e
  exact h₁

example (f g : α → α) (h : ∀ x : α, f x ≤ g x) (h₂ : g a + g b ≤ 5) : f a + f b ≤ 5 := by
  grw [h]
  guard_target =ₛ g a + f b ≤ 5
  grw [h]
  guard_target =ₛ g a + g b ≤ 5
  grw [h₂]

example (f g : α → α) (h : ∀ x : α, f x < g x) : f a ≤ g b := by
  grw [h, ← h b]
  guard_target =ₛ g a ≤ f b
  exact test_sorry

example (h₁ : a ≥ b) (h₂ : 0 ≤ c) : a * c ≥ 100 - a := by
  grw [h₁]
  guard_target =ₛ b * c ≥ 100 - b
  exact test_sorry

example {n : ℕ} (bound : n ≤ 5) : n ≤ 10 := by
  have h' : 5 ≤ 10 := by decide
  grw [h'] at bound
  assumption

example (h₁ : a ≤ b) : a + 5 ≤ b + 6 := by grw [h₁, show (5 : α) ≤ 6 by norm_num]

example (h₁ : a ≤ b) : a * 5 ≤ b * 5 := by grw [h₁]

example (h₁ : a ≤ b) (h₂ : c ≥ 0) : a * c ≤ b * c := by grw [h₁]

example (h₁ : a ≤ b) : a * c ≤ b * c := by
  grw [h₁]
  guard_target =ₛ 0 ≤ c
  exact test_sorry

/- This example has behaviour which might be weaker than some users would desire: it would be
mathematically sound to transform the goal here to `2 * y ≤ z`, not `2 * y < z`.

However, the current behavior is easier to implement, and preserves the form of the goal (`?_ < z`),
which is a useful invariant. -/
example {x y z : ℤ} (hx : x < y) : 2 * x < z := by
  grw [hx]
  guard_target =ₛ 2 * y < z
  exact test_sorry

end inequalities

section subsets

variable (X Y Z W : Set α)

example (h₁ : X ⊆ Y) (h₂ : Y ⊆ Z) (h₃ : a ∈ X) : False := by
  grw [h₁] at h₃
  guard_hyp h₃ :ₛ a ∈ Y
  grw [h₂] at h₃
  guard_hyp h₃ :ₛ a ∈ Z
  exact test_sorry

example (h₁ : Y ⊇ W) : X ⊂ (Y ∪ Z) := by
  grw [h₁]
  guard_target =ₛ X ⊂ (W ∪ Z)
  exact test_sorry

example (h₁ : W ⊂ Y) (h₂ : X ⊂ (W ∪ Z)) : X ⊂ (Y ∪ Z) := by
  grw [← h₁]
  guard_target =ₛ X ⊂ (W ∪ Z)
  exact h₂

example {a b : Nat} (h : a < b) (f : Nat → Nat) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ ({x | x ≤ a} : Set Nat), f i ≤ ∑ i ∈ ({x | x ≤ b} : Set Nat), f i := by
  grw [h]

end subsets

section rationals

example (x x' y z w : ℚ) (h0 : x' = x) (h₁ : x < z) (h₂ : w ≤ y + 4) (h₃ : z + 1 < 5 * w) :
    x' + 1 < 5 * (y + 4) := by
  grw [h0, h₁, ← h₂]
  exact h₃

example {x y z : ℚ} (f g : ℚ → ℚ) (h : ∀ t, f t = g t) : 2 * f x * f y * f x ≤ z := by
  grw [h]
  guard_target =ₛ 2 * g x * f y * g x ≤ z
  exact test_sorry

example {x y a b : ℚ} (h : x ≤ y) (h1 : a ≤ 3 * x) : 2 * x ≤ b := by
  grw [h] at h1
  guard_hyp h1 :ₛ a ≤ 3 * y
  exact test_sorry

end rationals

section modeq

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] := by grw [hn]; decide

example {a b : ℤ} (h1 : a ≡ 3 [ZMOD 5]) (h2 : b ≡ a ^ 2 + 1 [ZMOD 5]) :
    a ^ 2 + b ^ 2 ≡ 4 [ZMOD 5] := by
  grw [h1] at h2 ⊢
  guard_hyp h2 :ₛ b ≡ 3 ^ 2 + 1 [ZMOD 5]
  guard_target =ₛ 3 ^ 2 + b ^ 2 ≡ 4 [ZMOD 5]
  grw [h2]
  decide

end modeq

section wildcard

/-! Rewriting at a wildcard `*`, i.e. `grw [h] at *`, will sometimes include a rewrite at `h` itself
and sometimes not, according to whether the generalized rewrite is valid or not; this is the case
approximately (not exactly) when the relation in the type of `h` is an equivalence relation.  See
examples below of it occurring for `≡ [ZMOD 5]` and not occurring for `<`.

Having `grw [h] at *` rewrite at `h` itself is a bit weird, but is consistent with the behaviour of
`rw` (for the equivalence relation `=`).
-/

example {a b : ℤ} (h1 : a ≡ 3 [ZMOD 5]) (h2 : b ≡ a ^ 2 + 1 [ZMOD 5]) :
    a ^ 2 + b ^ 2 ≡ 4 [ZMOD 5] := by
  grw [h1] at *
  guard_hyp h1 :ₛ 3 ≡ 3 [ZMOD 5] -- `grw [h1] at *` rewrites at `h1`
  guard_hyp h2 :ₛ b ≡ 3 ^ 2 + 1 [ZMOD 5]
  guard_target =ₛ 3 ^ 2 + b ^ 2 ≡ 4 [ZMOD 5]
  grw [h2]
  decide

example {x y a b : ℚ} (h : x < y) (h1 : a ≤ 3 * x) : 2 * x ≤ b := by
  grw [h] at *
  guard_hyp h :ₛ x < y -- `grw [h] at *` does not rewrite at `h`
  guard_hyp h1 :ₛ a ≤ 3 * y
  guard_target =ₛ 2 * y ≤ b
  exact test_sorry

end wildcard

section nontransitive_grw_lemmas

example {s s' t : Set ℕ} (h : s' ⊆ s) (h2 : BddAbove (s ∩ t)) : BddAbove (s' ∩ t) := by
  grw [h]; exact h2

example {s s' : Set ℕ} (h : s' ⊆ s) (h2 : BddAbove s) : BddAbove s' := by
  grw [h]; exact h2

example {s s' t : Set α} (h : s ⊆ s') : (s' ∩ t).Nonempty := by
  grw [← h]
  guard_target =ₛ (s ∩ t).Nonempty
  exact test_sorry

end nontransitive_grw_lemmas

section

/-! In the examples in this section, the proposed rewrite is not valid because the constructed
relation does not have its main goals proved by `gcongr` (in the two examples here this is because
the inequality goes in the wrong direction). -/

/--
error: Tactic `grewrite` failed: could not discharge x ≤ y using x ≥ y

case h₁.h
α : Type u_1
inst✝² : CommRing α
inst✝¹ : LinearOrder α
inst✝ : IsStrictOrderedRing α
a b✝ c d e : α
x y b : ℚ
h : x ≥ y
⊢ x ≤ y
-/
#guard_msgs in
example {x y b : ℚ} (h : x ≥ y) : 2 * x ≤ b := by
  grw [h]

example {s s' t : Set α} (h : s' ⊆ s) : (s' ∩ t).Nonempty := by
  fail_if_success grw [h]
  exact test_sorry

end

example {x y a b : ℤ} (h1 : |x| ≤ a) (h2 : |y| ≤ b) :
    |x ^ 2 + 2 * x * y| ≤ a ^ 2 + 2 * a * b := by
  have : 0 ≤ a := by grw [← h1]; positivity
  grw [abs_add, abs_mul, abs_mul, abs_pow, h1, h2, abs_of_nonneg]
  norm_num

example {a b : ℚ} {P : Prop} (hP : P) (h : P → a < b) : False := by
  have : 2 * a ≤ 2 * b := by grw [h]; exact hP
  exact test_sorry

example {a b : ℚ} {P Q : Prop} (hP : P) (hQ : Q) (h : P → Q → a < b) : False := by
  have : 2 * a ≤ 2 * b := by grw [h ?_ hQ]; exact hP
  exact test_sorry

example {a a' : ℕ} {X : Set ℕ} (h₁ : a + 1 ∈ X) (h₂ : a = a') : False := by
  grw [h₂] at h₁
  guard_hyp h₁ :ₛ a' + 1 ∈ X
  exact test_sorry

example {Prime : ℕ → Prop} {a a' : ℕ} (h₁ : Prime (a + 1)) (h₂ : a = a') : False := by
  grw [h₂] at h₁
  guard_hyp h₁ :ₛ Prime (a' + 1)
  exact test_sorry

/--
error: Tactic `grewrite` failed: could not discharge b ≤ a using a ≤ b

case h₁.h
α : Type u_1
inst✝² : CommRing α
inst✝¹ : LinearOrder α
inst✝ : IsStrictOrderedRing α
a b c d e : α
h₁ : a ≤ b
h₂ : 0 ≤ c
⊢ b ≤ a
-/
#guard_msgs in
example (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≥ 100 + a := by
  grw [h₁]

example (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≥ 100 + a + a := by
  nth_grw 2 3 [h₁]
  guard_target =ₛ a * c ≥ 100 + b + b
  exact test_sorry
section apply

variable {p q r s : Prop}

example (n : Nat) (h : p → n=1) (h' : p) : n = 1 := by
  apply_rw [← h]
  exact h'

example (n : Nat) (h : p → n=1) (h' : r → s) : p ∧ r → n = 1 ∧ s := by
  apply_rw [h, h']
  exact id

example (n : Nat) (h : p → n=1) (h' : r → s) : p ∧ r → n = 1 ∧ s := by
  grw [h]
  apply_rw [h']
  gcongr
  intro _
  rfl
  exact test_sorry

example (h : p → q) (h' : q → r) : p → r := by
  apply_rw [← h] at h'
  exact h'

end apply

-- previously, `grw` failed to rewrite in expressions with syntheticOpaque metavariables
example : ∃ n, n < 2 := by
  refine ⟨?_, ?_⟩
  on_goal 2 => grw [← one_lt_two]
  exact 0
  refine zero_lt_one
