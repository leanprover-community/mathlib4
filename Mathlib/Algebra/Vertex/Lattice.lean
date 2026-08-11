/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Loop
public import Mathlib.Algebra.Vertex.VertexOperator

/-!
# Lattice vertex operators
In this file we introduce vertex operators attached to elements in the double cover of an integer
lattice. They are given by formal power series of operators with rational coefficients, but they
preserve certain integral forms. We introduce a typeclass for a graded module to admit an action by
these operator series.

## Definitions
 * `VertexOperator.Lattice.E-` : The creation operator.
 * `VertexOperator.Lattice.E+` : The annihilation operator.

## Main results

## TODO:

## References
* [R. Borcherds, *Vertex algebras, Kac-Moody algebras, and the monster*]
* [R. McRae, *On integral forms for vertex algebras associated with affine Lie algebras and
  lattices*]
-/

@[expose] public section

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
