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

 * `LinearProgram` defines a linear program in a form that generalizes "A x ≥ b".
 * `LinearProgram.feasibles` is the set of all admissible solutions to given linear program.
 * `LinearProgram.MinAt` defines an optimum solution of given linear program.

-/

/-- Linear program in the form of inequalities with general variables. -/
structure LinearProgram (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Inequality constraints (given in the form "aᵀx - b ≥ 0") -/
  constraints : List (P →ᵃ[K] K)
  /-- The objective function (affine map) -/
  objective : P →ᵃ[K] K

variable {K V P : Type*} [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- Constructs a linear program given a list of equalities, a list of inequalities,
    and an objective function. -/
def linearProgram_of_equalities_inequalities_objective
    (equalities inequalities : List (P →ᵃ[K] K)) (objectiv : P →ᵃ[K] K) :
    LinearProgram K P where
  constraints := inequalities ++ equalities ++ equalities.map Neg.neg
  objective := objectiv

/-- The set of all admissible solutions to given linear program. -/
def LinearProgram.feasibles (lp : LinearProgram K P) : Set P :=
  { x : P | ∀ a ∈ lp.constraints, 0 ≤ a x }

/-- Given linear program is minimized at given point. -/
def LinearProgram.MinAt (lp : LinearProgram K P) (x : P) : Prop :=
  x ∈ lp.feasibles ∧ ∀ y ∈ lp.feasibles, lp.objective x ≤ lp.objective y
