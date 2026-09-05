/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.Tactics

/-!
# Tests for `poly_eval` and `poly_dvd`

Kernel evaluation and kernel long-division divisibility for `Polynomial ℤ` — axiom-free.
-/

open Polynomial


-- Evaluation: `(X² + 1)(2) = 5`:
example : Polynomial.eval 2 (X ^ 2 + 1 : Polynomial ℤ) = 5 := by poly_eval

-- A root: `2` is a root of `X² − 4`:
theorem root_demo : Polynomial.eval 2 (X ^ 2 - 4 : Polynomial ℤ) = 0 := by poly_eval
/-- info: 'root_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_demo

-- Divisibility over `ℤ` (kernel reduces `ℤ` literal arithmetic; with a monic divisor the long
-- division is exact). `ℚ` would get stuck — `Rat` doesn't reduce cheaply in the kernel.
example : (X - 1 : Polynomial ℤ) ∣ (X ^ 2 - 1) := by poly_dvd
theorem dvd_demo : (X + 1 : Polynomial ℤ) ∣ (X ^ 3 + 1) := by poly_dvd
/-- info: 'dvd_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_demo
