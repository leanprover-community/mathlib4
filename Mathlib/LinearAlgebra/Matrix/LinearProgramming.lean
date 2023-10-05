/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Linear programming

Minimizing a linear function on a region defined by linear inequalities.

## Main definitions

 * `StandardLP` defines a linear program in the standard form (generalization of "A x ≥ b").
 * `StandardLP.feasibles` is the set of all admissible solutions to given standard LP.
 * `StandardLP.MinAt` defines an optimum solution of given standard LP.

-/

/-- Linear program in the standard form. -/
structure StandardLP (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Inequality constraints (given in the form "aᵀx - b ≥ 0") -/
  constraints : List (P →ᵃ[K] K)
  /-- The objective function (affine map) -/
  objective : P →ᵃ[K] K

variable {K V P : Type*} [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- Constructs a linear program in the standard form given a list of equalities,
    a list of inequalities, and an objective function. -/
def standardLP_of_equalities_inequalities_objective
    (equalities inequalities : List (P →ᵃ[K] K)) (objectiv : P →ᵃ[K] K) :
    StandardLP K P where
  constraints := inequalities ++ equalities ++ equalities.map Neg.neg
  objective := objectiv

/-- The set of all admissible solutions to given linear program. -/
def StandardLP.feasibles (lp : StandardLP K P) : Set P :=
  { x : P | ∀ a ∈ lp.constraints, 0 ≤ a x }

/-- Given linear program is minimized at given point. -/
def StandardLP.MinAt (lp : StandardLP K P) (x : P) : Prop :=
  x ∈ lp.feasibles ∧ ∀ y ∈ lp.feasibles, lp.objective x ≤ lp.objective y
