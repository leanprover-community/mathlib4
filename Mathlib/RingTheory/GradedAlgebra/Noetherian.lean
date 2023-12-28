/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!
# The properties of a graded Noetherian ring.

This file proves some properties of a graded Noetherian ring:
1. The 0-th grade of a Noetherian ring is also a Noetherian ring.
2. For a Noetherian ring `A` which is internally graded by `𝒜`,
   `⨁_{i>0} 𝒜ᵢ` is finitely generated as an ideal of `A`.
-/

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [CanonicallyOrderedAddCommMonoid ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

namespace GradedRing

/--
If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring.
-/
theorem GradeZero.subring_isNoetherianRing_of_isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜)
  (GradedRing.projZeroRingHom'_surjective 𝒜)

end GradedRing

/--
If the internally graded ring `A` is Noetherian, then `⨁_{i>0} 𝒜ᵢ`
is finitely generated as an ideal of `A`.
-/
theorem HomogeneousIdeal.irrelevant_toIdeal_fg_of_isNoetherianRing :
    Ideal.FG (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
  (isNoetherianRing_iff_ideal_fg A).1 inferInstance (HomogeneousIdeal.irrelevant 𝒜).toIdeal
