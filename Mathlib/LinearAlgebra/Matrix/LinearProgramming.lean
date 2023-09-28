/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Linear programming

TODO

## Main definitions

 * `StandardLP` defines a linear program in the standard form.
 * `StandardLP.feasibles` is the set of all admissible solutions to given standard LP.

-/

/-- Linear program in the standard form. -/
structure StandardLP (K : Type*) {V : Type*} (P : Type*)
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P] where
  /-- Inequality constraints -/
  constraints : List (P →ᵃ[K] K)
  /-- The objective function -/
  objective : P →ᵃ[K] K

/-- Constructs a linear program in the standard form given a list of equalities,
    a list of inequalities, and an objective function. -/
def standardLP_of_equalities_inequalities_objective {K V P : Type*}
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]
    (equalities inequalities : List (P →ᵃ[K] K)) (objectiv : P →ᵃ[K] K) :
    StandardLP K P where
  constraints := inequalities ++ equalities ++ equalities.map Neg.neg
  objective := objectiv

/-- The set of all admissible solutions to given linear program. -/
def StandardLP.feasibles {K V P : Type*}
    [LinearOrderedField K] [AddCommGroup V] [Module K V] [AddTorsor V P]
    (lp : StandardLP K P) : Set P :=
  { x : P | ∀ c ∈ lp.constraints, 0 ≤ c x }
