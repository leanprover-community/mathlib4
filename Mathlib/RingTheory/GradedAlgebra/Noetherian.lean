/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The 0-th grade of a graded Noetherian ring.

This file proves that for a graded Noetherian ring, its 0-th grade is also
a Noetherian ring.
-/

variable {ι A σ : Type*}
variable [Ring A]
variable [DecidableEq ι] [CanonicallyOrderedAddCommMonoid ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

namespace GradedRing

/--
If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring.
-/
theorem GradeZero.subring_isNoetherianRing_of_isNoetherianRing [IsNoetherianRing A] :
    IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜)
  (GradedRing.projZeroRingHom'_surjective 𝒜)

end GradedRing
