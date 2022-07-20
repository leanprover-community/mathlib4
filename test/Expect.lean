/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Expect

example : True ∧ True := by
  expect_goals True ∧ True
  constructor
  expect_goals True, True
  expect_failure_msg "too many expected goals" expect_goals True, True, Foo
  expect_failure expect_goals True ∧ True
  expect_goals True
  repeat simp

example (p : P) : P := by
  expect_failure_msg "unknown identifier 'x'" have h := x
  expect_failure expect_failure_msg "unknown identifier 'y'" have h := x
  exact p

example (h : a = b) : a = b ∧ b = a := by
  constructor
  expect_goals a = b
  have _five := 5
  expect_hyps _five : Nat, h : a = b
  expect_failure_msg "expected 'String' but got 'Nat'" expect_hyps _five : String
  expect_failure_msg "unknown identifier 'six'" expect_hyps six : Nat
  expect_hyps h : a = b
  exact h
  expect_goals b = a
  have _six := 6
  expect_hyps _six : Nat, h : a = b
  expect_failure_msg "unknown identifier 'five'" expect_hyps five : Nat
  simp [h]
