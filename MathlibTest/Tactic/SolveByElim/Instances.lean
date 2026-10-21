/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Algebra.Order.Ring.Nat

@[expose] public section

lemma foo (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply_rules [mul_ne_zero]
