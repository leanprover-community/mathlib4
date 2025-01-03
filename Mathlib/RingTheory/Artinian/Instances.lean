/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Divisibility.Prod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] subtype_isMaximal_finite fieldOfSubtypeIsMaximal

instance : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)

instance : DecompositionMonoid (Polynomial R) :=
  MulEquiv.decompositionMonoid <| (Polynomial.mapEquiv <| equivPi R).trans (Polynomial.piEquiv _)

theorem isSemisimpleRing_of_isReduced : IsSemisimpleRing R := (equivPi R).symm.isSemisimpleRing

end IsArtinianRing
