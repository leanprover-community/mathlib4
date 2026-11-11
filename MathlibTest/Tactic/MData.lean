module
import Mathlib

/-!
# Tactics should not be confused by `Expr.mdata` or `autoParam`

This file records a common type of bug in tactics that manipulate expressions that occur "in the
wild". The issue is that subexpressions may contain metadata annotations, which are hidden from the
user but get in the way of tactics. One common issue is that `Expr.getAppFnArgs` does not strip
metadata itself, for example.

These annotations get into goals in three ways in this file:
* `ofNat(n)`, which is `no_index (OfNat.ofNat n)`. Many Mathlib lemmas are stated with it, so
  rewriting with such a lemma leaves the annotation behind in the goal.
* `no_index t`, written explicitly, for the cases where the offending subterm is not a numeral.
* In types, as `autoParam`. These can be stripped using `Expr.cleanupAnnotations`.
-/

open Polynomial
open scoped NNReal

set_option linter.unusedVariables false

variable (a b c : ℕ) (x y z : ℝ)

/-! ### `positivity`: even powers -/

example : 0 ≤ x ^ (ofNat(nat_lit 2) : ℕ) := by
  positivity

/-! ### `abel` -/

example : x + ofNat(nat_lit 0) = x := by
  abel1

example : no_index (x + y) + z = z + (y + x) := by
  abel1

/-! ### `basify` -/

example : ∀ (a : ENNReal := 0), a ≤ a + 1 := by
  intro a
  basify
  linarith

/-! ### `linarith`: preprocessing of `ℕ` and `ℝ≥0`

Here the annotation is on the *type*. -/

example (n m : ℕ := 3) (h : n < m) : n ≤ m := by
  linarith

example (u v : ℝ≥0 := 0) (h : u < v) : u ≤ v := by
  linarith

-- the nonnegativity of a cast of a natural number
example (n : ℕ) (h : no_index (n : ℝ) < x) : 0 < x := by
  linarith

/-! ### `fin_cases` -/

example (s : Finset ℕ := {}) (hs : s = {1, 2}) (h : a ∈ s) : True := by
  subst hs
  fin_cases h <;> trivial

/-! ### `reduce_mod_char` -/

example : (4 : no_index (ZMod 3)) = 1 := by
  reduce_mod_char

/-! ### `cancel_denoms` -/

example (h : no_index (x / 2) < y / 2) : x < y := by
  cancel_denoms at h
  exact h

/-! ### `compute_degree` and `monicity` -/

example : (X ^ 2 + no_index (C 1) : ℤ[X]).natDegree = 2 := by
  compute_degree!

example : Monic (no_index (X + 1) : ℤ[X]) := by
  monicity!

/-! ### `apply_fun` -/

example (f : ℕ → ℕ) (h : f a ≠ f b) : ¬ no_index (a = b) := by
  apply_fun f
  exact h

/-! ### `cases_type` -/

example (p q r : Prop) (h : no_index (p ∧ q) ∧ r) : p := by
  cases_type* And
  assumption

/-! ### `move_add` -/

example : no_index (a + b) + c = c + a + b := by
  move_add [← c]
  rfl
