/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Antoine Chambert-Loir
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Order.Group.Defs

/-!

# Linear programming

TODO

-/

/-- Typically `P` is `R^m` and `V` is `R^n` -/
structure LinearProgram (R : Type*) (P : Type*) (V : Type*)
    [Ring R] [AddCommGroup P] [Module R P] [AddCommGroup V] [Module R V] where
  /-- Linear map -/
  φ : P →ₗ[R] V
  /-- Right-hand side -/
  v : V
  /-- Objective function -/
  f : P →ₗ[R] R
  /-- Cone defines nonnegative elements -/
  s : AddCommGroup.PositiveCone V

variable {R P V : Type*} [Ring R] [AddCommGroup P] [Module R P] [AddCommGroup V] [Module R V]

/-- Essentially the set `{ x : P | LP.φ x ≤ LP.v }` -/
def LinearProgram.C (LP : LinearProgram R P V) := { x : P | LP.s.nonneg (LP.v - LP.φ x) }
