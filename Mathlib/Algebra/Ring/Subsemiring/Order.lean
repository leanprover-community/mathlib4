/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# `Order`ed instances for `SubsemiringClass` and `Subsemiring`.
-/

namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)

/-- A subsemiring of an `OrderedSemiring` is an `OrderedSemiring`. -/
instance toOrderedSemiring [OrderedSemiring R] [SubsemiringClass S R] :
    OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_ordered_semiring SubsemiringClass.toOrderedSemiring

/-- A subsemiring of a `StrictOrderedSemiring` is a `StrictOrderedSemiring`. -/
instance toStrictOrderedSemiring [StrictOrderedSemiring R]
    [SubsemiringClass S R] : StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_strict_ordered_semiring SubsemiringClass.toStrictOrderedSemiring

/-- A subsemiring of an `OrderedCommSemiring` is an `OrderedCommSemiring`. -/
instance toOrderedCommSemiring [OrderedCommSemiring R] [SubsemiringClass S R] :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_ordered_comm_semiring SubsemiringClass.toOrderedCommSemiring

/-- A subsemiring of a `StrictOrderedCommSemiring` is a `StrictOrderedCommSemiring`. -/
instance toStrictOrderedCommSemiring [StrictOrderedCommSemiring R]
    [SubsemiringClass S R] : StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring_class.to_strict_ordered_comm_semiring SubsemiringClass.toStrictOrderedCommSemiring

/-- A subsemiring of a `LinearOrderedSemiring` is a `LinearOrderedSemiring`. -/
instance toLinearOrderedSemiring [LinearOrderedSemiring R]
    [SubsemiringClass S R] : LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring_class.to_linear_ordered_semiring SubsemiringClass.toLinearOrderedSemiring

/-- A subsemiring of a `LinearOrderedCommSemiring` is a `LinearOrderedCommSemiring`. -/
instance toLinearOrderedCommSemiring [LinearOrderedCommSemiring R]
    [SubsemiringClass S R] : LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring_class.to_linear_ordered_comm_semiring SubsemiringClass.toLinearOrderedCommSemiring

end SubsemiringClass

namespace Subsemiring

variable {R : Type*}

/-- A subsemiring of an `OrderedSemiring` is an `OrderedSemiring`. -/
instance toOrderedSemiring [OrderedSemiring R] (s : Subsemiring R) : OrderedSemiring s :=
  Subtype.coe_injective.orderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_ordered_semiring Subsemiring.toOrderedSemiring

/-- A subsemiring of a `StrictOrderedSemiring` is a `StrictOrderedSemiring`. -/
instance toStrictOrderedSemiring [StrictOrderedSemiring R] (s : Subsemiring R) :
    StrictOrderedSemiring s :=
  Subtype.coe_injective.strictOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_strict_ordered_semiring Subsemiring.toStrictOrderedSemiring

/-- A subsemiring of an `OrderedCommSemiring` is an `OrderedCommSemiring`. -/
instance toOrderedCommSemiring [OrderedCommSemiring R] (s : Subsemiring R) :
    OrderedCommSemiring s :=
  Subtype.coe_injective.orderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_ordered_comm_semiring Subsemiring.toOrderedCommSemiring

/-- A subsemiring of a `StrictOrderedCommSemiring` is a `StrictOrderedCommSemiring`. -/
instance toStrictOrderedCommSemiring [StrictOrderedCommSemiring R] (s : Subsemiring R) :
    StrictOrderedCommSemiring s :=
  Subtype.coe_injective.strictOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
#align subsemiring.to_strict_ordered_comm_semiring Subsemiring.toStrictOrderedCommSemiring

/-- A subsemiring of a `LinearOrderedSemiring` is a `LinearOrderedSemiring`. -/
instance toLinearOrderedSemiring [LinearOrderedSemiring R] (s : Subsemiring R) :
    LinearOrderedSemiring s :=
  Subtype.coe_injective.linearOrderedSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring.to_linear_ordered_semiring Subsemiring.toLinearOrderedSemiring

/-- A subsemiring of a `LinearOrderedCommSemiring` is a `LinearOrderedCommSemiring`. -/
instance toLinearOrderedCommSemiring [LinearOrderedCommSemiring R] (s : Subsemiring R) :
    LinearOrderedCommSemiring s :=
  Subtype.coe_injective.linearOrderedCommSemiring (↑) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subsemiring.to_linear_ordered_comm_semiring Subsemiring.toLinearOrderedCommSemiring

/-- The set of nonnegative elements in an ordered semiring, as a subsemiring. -/
@[simps]
def nonneg (R : Type*) [OrderedSemiring R] : Subsemiring R where
  carrier := Set.Ici 0
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one
  add_mem' := add_nonneg
  zero_mem' := le_rfl

end Subsemiring
