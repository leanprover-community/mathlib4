/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.Reflect

/-!
# Tests for `poly_decide`

Axiom-free `Polynomial` identities: the `#guard_msgs` check asserts the axiom set is exactly
`[propext, Classical.choice, Quot.sound]` — no `native_decide` / `Lean.ofReduceBool`.
-/

open Polynomial


example : ((X + C 1) ^ 2 : Polynomial ℤ) = X ^ 2 + C 2 * X + C 1 := by poly_decide
example : (X ^ 2 - C 1 : Polynomial ℤ) = (X - C 1) * (X + C 1) := by poly_decide
example : ((X + C 1) ^ 3 : Polynomial ℤ) = X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1 := by poly_decide
example : (X ^ 2 - C 1 - (X - C 1) * (X + C 1) : Polynomial ℤ) = 0 := by poly_decide
-- bare numerals (no `C`) also work, axiom-free:
example : ((X + 1) * (X + 2) : Polynomial ℤ) = X ^ 2 + 3 * X + 2 := by poly_decide

-- The trust check: only the three standard axioms — no `Lean.ofReduceBool`.
theorem sq_expand : ((X + C 1) ^ 2 : Polynomial ℤ) = X ^ 2 + C 2 * X + C 1 := by poly_decide
/-- info: 'sq_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_expand
