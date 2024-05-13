/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Order.Hom.Ring

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
    OrderedRing s :=
  Subtype.coe_injective.orderedRing (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ordered_ring SubringClass.toOrderedRing

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of an `OrderedCommRing` is an `OrderedCommRing`. -/
instance (priority := 75) toOrderedCommRing [OrderedCommRing R] [SubringClass S R] :
    OrderedCommRing s :=
  Subtype.coe_injective.orderedCommRing (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ordered_comm_ring SubringClass.toOrderedCommRing

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `LinearOrderedRing` is a `LinearOrderedRing`. -/
instance (priority := 75) toLinearOrderedRing [LinearOrderedRing R] [SubringClass S R] :
    LinearOrderedRing s :=
  Subtype.coe_injective.linearOrderedRing (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring_class.to_linear_ordered_ring SubringClass.toLinearOrderedRing

-- Prefer subclasses of `Ring` over subclasses of `SubringClass`.
/-- A subring of a `LinearOrderedCommRing` is a `LinearOrderedCommRing`. -/
instance (priority := 75) toLinearOrderedCommRing [LinearOrderedCommRing R] [SubringClass S R] :
    LinearOrderedCommRing s :=
  Subtype.coe_injective.linearOrderedCommRing (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring_class.to_linear_ordered_comm_ring SubringClass.toLinearOrderedCommRing

end SubringClass

namespace Subring

variable {R : Type*}

/-- A subring of an `OrderedRing` is an `OrderedRing`. -/
instance toOrderedRing [OrderedRing R] (s : Subring R) : OrderedRing s :=
  SubringClass.toOrderedRing s
#align subring.to_ordered_ring Subring.toOrderedRing

/-- A subring of an `OrderedCommRing` is an `OrderedCommRing`. -/
instance toOrderedCommRing [OrderedCommRing R] (s : Subring R) : OrderedCommRing s :=
  SubringClass.toOrderedCommRing s
#align subring.to_ordered_comm_ring Subring.toOrderedCommRing

/-- A subring of a `LinearOrderedRing` is a `LinearOrderedRing`. -/
instance toLinearOrderedRing [LinearOrderedRing R] (s : Subring R) : LinearOrderedRing s :=
  SubringClass.toLinearOrderedRing s
#align subring.to_linear_ordered_ring Subring.toLinearOrderedRing

/-- A subring of a `LinearOrderedCommRing` is a `LinearOrderedCommRing`. -/
instance toLinearOrderedCommRing [LinearOrderedCommRing R] (s : Subring R) :
    LinearOrderedCommRing s :=
  SubringClass.toLinearOrderedCommRing s
#align subring.to_linear_ordered_comm_ring Subring.toLinearOrderedCommRing

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
def orderedSubtype {R : Type*} [OrderedRing R] (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

variable {R : Type*} [OrderedRing R]

lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
