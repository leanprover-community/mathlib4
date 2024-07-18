/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Ring.Hom.Defs

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

Define local ring homomorhpisms.

## Main definitions

* `IsLocalRingHom`: A predicate on semiring homomorphisms, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal.

-/

variable {R S : Type*}

/-- A local ring homomorphism is a homomorphism `f` between local rings such that `a` in the domain
  is a unit if `f a` is a unit for any `a`. See `LocalRing.local_hom_TFAE` for other equivalent
  definitions. -/
class IsLocalRingHom [Semiring R] [Semiring S] (f : R →+* S) : Prop where
  /-- A local ring homomorphism `f : R ⟶ S` will send nonunits of `R` to nonunits of `S`. -/
  map_nonunit : ∀ a, IsUnit (f a) → IsUnit a
#align is_local_ring_hom IsLocalRingHom
