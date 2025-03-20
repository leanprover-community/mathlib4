/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Ring.Subring.Defs

/-!

# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results
* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `OrderedRing`, `OrderedCommRing`, `LinearOrderedRing`,
  `toLinearOrderedCommRing` is again an ordering ring

-/

namespace SubringClass
variable {R S : Type*} [SetLike S R] (s : S)

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of an `OrderedRing` is an `OrderedRing`. -/
instance (priority := 75) toOrderedRing [OrderedRing R] [SubringClass S R] :
    OrderedRing s := fast_instance%
  Subtype.coe_injective.orderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of an `OrderedCommRing` is an `OrderedCommRing`. -/
instance (priority := 75) toOrderedCommRing [OrderedCommRing R] [SubringClass S R] :
    OrderedCommRing s := fast_instance%
  Subtype.coe_injective.orderedCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `LinearOrderedRing` is a `LinearOrderedRing`. -/
instance (priority := 75) toLinearOrderedRing [LinearOrderedRing R] [SubringClass S R] :
    LinearOrderedRing s := fast_instance%
  Subtype.coe_injective.linearOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `LinearOrderedCommRing` is a `LinearOrderedCommRing`. -/
instance (priority := 75) toLinearOrderedCommRing [LinearOrderedCommRing R] [SubringClass S R] :
    LinearOrderedCommRing s := fast_instance%
  Subtype.coe_injective.linearOrderedCommRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end SubringClass

namespace Subring

variable {R : Type*}

/-- A subring of an `OrderedRing` is an `OrderedRing`. -/
instance toOrderedRing [OrderedRing R] (s : Subring R) : OrderedRing s :=
  SubringClass.toOrderedRing s

/-- A subring of an `OrderedCommRing` is an `OrderedCommRing`. -/
instance toOrderedCommRing [OrderedCommRing R] (s : Subring R) : OrderedCommRing s :=
  SubringClass.toOrderedCommRing s

/-- A subring of a `LinearOrderedRing` is a `LinearOrderedRing`. -/
instance toLinearOrderedRing [LinearOrderedRing R] (s : Subring R) : LinearOrderedRing s :=
  SubringClass.toLinearOrderedRing s

/-- A subring of a `LinearOrderedCommRing` is a `LinearOrderedCommRing`. -/
instance toLinearOrderedCommRing [LinearOrderedCommRing R] (s : Subring R) :
    LinearOrderedCommRing s :=
  SubringClass.toLinearOrderedCommRing s

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
def orderedSubtype {R : Type*} [OrderedRing R] (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

variable {R : Type*} [OrderedRing R]

lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
