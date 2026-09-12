/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `s → R` of a subring `s` as an ordered ring
  homomorphism

A subring of an `IsOrderedRing` or an `IsStrictOrderedRing` is again the respective kind of
ordered ring: this is already provided by the `SubsemiringClass` instances
`SubsemiringClass.toIsOrderedRing` and `SubsemiringClass.toIsStrictOrderedRing`, which apply
since `SubringClass S R` implies `SubsemiringClass S R`.
-/

@[expose] public section

namespace Subring

variable {R : Type*} [Ring R] [PartialOrder R]

/-- The inclusion `s → R` of a subring `s`, as an ordered ring homomorphism. -/
def orderedSubtype (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
