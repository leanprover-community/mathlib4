/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Expect

example : True ∧ True := by
  expect_goal True ∧ True
  constructor
  expect_failure expect_goal True ∧ True
  expect_goal True
  repeat simp

example (p : P) : P := by
  expect_failure_msg "unknown identifier 'x'" have h := x
  expect_failure expect_failure_msg "unknown identifier 'y'" have h := x
  exact p

example (h : a = b) : a = b ∧ b = a := by
  constructor
  expect_goal a = b
  have _five := 5
  expect_hyp _five : Nat
  expect_failure_msg "expected 'String' but got 'Nat'" expect_hyp _five : String
  expect_failure_msg "unknown identifier 'six'" expect_hyp six : Nat
  expect_hyp h : a = b
  exact h
  expect_goal b = a
  have _six := 6
  expect_hyp _six : Nat
  expect_failure_msg "unknown identifier 'five'" expect_hyp five : Nat
  simp [h]
