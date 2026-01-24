/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Artinian.Module

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

@[expose] public section

/-- If each `Rⁿ` is a Artinian `R`-module, then `R` satisfies the strong rank condition.
Not an instance for performance reasons. -/
theorem StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R]
    [∀ n, IsArtinian R (Fin n → R)] : StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf ↦
    have e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    not_subsingleton R <| IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] fieldOfSubtypeIsMaximal

instance : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)

instance : DecompositionMonoid (Polynomial R) :=
  MulEquiv.decompositionMonoid <| (Polynomial.mapEquiv <| equivPi R).trans (Polynomial.piEquiv _)

end IsArtinianRing
