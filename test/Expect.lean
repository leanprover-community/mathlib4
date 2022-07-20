/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Expect

example (p : P) : P := by
  expect_failure_msg "unknown identifier 'x'" have h := x
  expect_failure expect_failure_msg "unknown identifier 'y'" have h := x
  exact p
  expect_failure_msg "no goals to be solved" simp
