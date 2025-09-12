/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivation for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `LeftInvariantDerivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

Note that one can also define a Lie algebra on the space of left-invariant vector fields
(see `instLieAlgebraGroupLieAlgebra`). For finite-dimensional `C^∞` real manifolds, the space of
derivations can be canonically identified with the tangent space, and we recover the same Lie
algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. The left-invariant vector fields should
therefore be favored to construct a theory of Lie groups in suitable generality.
-/


noncomputable section
