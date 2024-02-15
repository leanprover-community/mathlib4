/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Data.Polynomial.Laurent

/-!
# Loop Lie algebras and their central extensions

Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Representations of loop algebras are not particularly interesting - a theorem of Rao (1993) shows
that when `L` is complex semisimple, any irreducible representation is just given by evaluation of
loops at specific points.  However, the theory becomes much richer when one considers projective
representations, i.e., representations of a central extension.

## Main definitions (Todo for now)

* Loop Algebra
* Central extension
* representation with fixed central character
* Positive energy representation

## Tags

lie ring, lie algebra, base change, Laurent polynomial, central extension
-/

suppress_compilation

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace LoopAlgebra

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- A loop algebra is the base change of a Lie algebra by the algebra of Laurent polynomials. -/
abbrev LoopAlgebra := (LaurentPolynomial R ⊗[R] L)

instance instLieRing : LieRing (LoopAlgebra R L) :=
  ExtendScalars.instLieRing R (LaurentPolynomial R) L

instance instLieAlgebra : LieAlgebra (LaurentPolynomial R) (LoopAlgebra R L) :=
  ExtendScalars.instLieAlgebra R (LaurentPolynomial R) L
