/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Algebra.Order.Hom.Ring

/-! ## Ordered subrings

In this file, we study subrings of ordered rings and their properties.

## Main definitions and results
Let `R` be an ordered ring.
* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
-/

namespace Subring

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
def orderedSubtype {R : Type*} [OrderedRing R] (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

variable {R : Type*} [OrderedRing R]

lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
