/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Tests for fun_prop with HasFinite{Mul}Support
-/

open Function

example : HasFiniteMulSupport fun _ : ℕ ↦ (1 : ℤ) := by fun_prop

example : HasFiniteSupport (0 : ℕ → ℤ) := by fun_prop

@[to_additive]
lemma HasFiniteMulSupport_foo {K ι M : Type*} [Monoid M] {v : ι → K → ℤ}
    (hv : ∀ x, HasFiniteMulSupport fun i ↦ v i x) (x y : K) :
    HasFiniteMulSupport fun i ↦ max (v i x * v i y) 1 := by
  fun_prop
