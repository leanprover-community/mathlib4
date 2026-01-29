/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Loop
public import Mathlib.Algebra.Vertex.VertexOperator

/-!
# Vertex operators
In this file we introduce lattice vertex operators as linear maps on Heisenberg modules. We put them
together from component parts so that we can add API for the parts.

## Definitions
 * `VertexOperator.Lattice.E-` : The creation operator.
 * `VertexOperator.Lattice.E-` : The annihilation operator.

## Main results

## TODO:

## References
* [G. Mason *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
* H. Li's paper on local systems?
-/

@[expose] public section

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
