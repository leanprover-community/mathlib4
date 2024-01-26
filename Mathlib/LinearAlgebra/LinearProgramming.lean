/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Antoine Chambert-Loir
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!

# Linear programming

TODO

-/

structure LinearProgram (R : Type*) (P : Type*) (V : Type*) [LinearOrderedRing R]
    -- Typically `P` is `R^m` and `V` is `R^n`
    [AddCommMonoid P] [Module R P] [AddCommMonoid V] [Module R V] [PartialOrder V] where
  /-- Linear map -/
  φ : P →ₗ[R] V
  /-- Right-hand side -/
  v : V
  /-- Objective function -/
  f : P →ₗ[R] R


variable {R V P : Type*} [LinearOrderedRing R]
  [AddCommMonoid P] [Module R P] [AddCommMonoid V] [Module R V] [PartialOrder V]

def LinearProgram.C (LP : LinearProgram R P V) : Set P := { x : P | (LP.φ x) ≤ LP.v }
