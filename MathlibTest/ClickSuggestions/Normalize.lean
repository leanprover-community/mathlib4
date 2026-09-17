/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

import MathlibTest.ClickSuggestions.TestImpl
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.ModuleNF
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Group

/-!
This file tests the normalization suggestions of `#click_suggestions`.
-/
set_option linter.unusedTactic false

#click_suggestions

variable {α R : Type*}

example [Field R] (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  click_test => "ring_nf"
  fail_if_success click_test => "abel_nf"
  fail_if_success click_test => "field_simp"
  fail_if_success click_test => "noncomm_ring"
  fail_if_success click_test => "module_nf"
  click_test "/1" => "conv =>\n enter [2]\n ring_nf"
  ring_nf

example (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  click_test => "ring_nf" "apply Nat.sq_sub_sq"
  apply Nat.sq_sub_sq

example [Ring R] (a b : R) (h : Commute a b) :
    a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  click_test => "noncomm_ring"
  noncomm_ring
  rw [h.eq]
  click_test => "simp" "abel_nf"
  fail_if_success click_test => "module_nf"
  abel_nf

example [Group α] (a b : α) : a * b * b⁻¹ = a := by
  click_test => "simp" "group"
  click_test "/0/1" => "conv =>\n enter [1]\n simp" "group"
  group

example [CommRing R] [AddCommMonoid α] [Module R α] (a b : α) :
    a + (2 : R) • b = b + a + b := by
  -- Here `module_nf` solves the goal and `abel_nf` doesn't.
  click_test => "norm_cast" "abel_nf" "module_nf"
  norm_cast
  -- Here `module_nf` is not suggested because the base is `ℤ`, so `abel_nf` suffices.
  click_test => "abel_nf"
  fail_if_success click_test => "module_nf"
  abel_nf

example {x y : ℚ} (hx : x ≠ 0) : x * y * x⁻¹ = y := by
  click_test "/0/1" => "conv =>\n enter [1]\n field_simp"
  click_test => "field_simp"
  field_simp

example : ((1 : ℕ) + (2 : ℤ) : ℚ) = (1 : NNRat) * (3 : ℚ) := by
  click_test => "dsimp" "simp" "push_cast" "norm_cast" "norm_num1" "ring_nf"
  norm_num1
  rfl
