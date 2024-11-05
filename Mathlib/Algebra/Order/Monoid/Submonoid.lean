/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Order.Monoid.Basic

/-!
# Ordered instances on submonoids
-/

assert_not_exists MonoidWithZero

namespace SubmonoidClass
variable {M S : Type*} [SetLike S M]

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an `OrderedCommMonoid` is an `OrderedCommMonoid`. -/
@[to_additive "An `AddSubmonoid` of an `OrderedAddCommMonoid` is an `OrderedAddCommMonoid`."]
instance (priority := 75) toOrderedCommMonoid [OrderedCommMonoid M]
    [SubmonoidClass S M] (s : S) : OrderedCommMonoid s :=
  Subtype.coe_injective.orderedCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `LinearOrderedCommMonoid` is a `LinearOrderedCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`."]
instance (priority := 75) toLinearOrderedCommMonoid [LinearOrderedCommMonoid M]
    [SubmonoidClass S M] (s : S) : LinearOrderedCommMonoid s :=
  Subtype.coe_injective.linearOrderedCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an `OrderedCancelCommMonoid` is an `OrderedCancelCommMonoid`. -/
@[to_additive AddSubmonoidClass.toOrderedCancelAddCommMonoid
      "An `AddSubmonoid` of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`."]
instance (priority := 75) toOrderedCancelCommMonoid [OrderedCancelCommMonoid M]
    [SubmonoidClass S M] (s : S) : OrderedCancelCommMonoid s :=
  Subtype.coe_injective.orderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of a `LinearOrderedCancelCommMonoid` is a `LinearOrderedCancelCommMonoid`.
-/
@[to_additive AddSubmonoidClass.toLinearOrderedCancelAddCommMonoid
      "An `AddSubmonoid` of a `LinearOrderedCancelAddCommMonoid` is
      a `LinearOrderedCancelAddCommMonoid`."]
instance (priority := 75) toLinearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid M]
    [SubmonoidClass S M] (s : S) : LinearOrderedCancelCommMonoid s :=
  Subtype.coe_injective.linearOrderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl


end SubmonoidClass

namespace Submonoid
variable {M : Type*}

/-- A submonoid of an `OrderedCommMonoid` is an `OrderedCommMonoid`. -/
@[to_additive "An `AddSubmonoid` of an `OrderedAddCommMonoid` is an `OrderedAddCommMonoid`."]
instance toOrderedCommMonoid [OrderedCommMonoid M] (S : Submonoid M) : OrderedCommMonoid S :=
  Subtype.coe_injective.orderedCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `LinearOrderedCommMonoid` is a `LinearOrderedCommMonoid`. -/
@[to_additive
      "An `AddSubmonoid` of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`."]
instance toLinearOrderedCommMonoid [LinearOrderedCommMonoid M] (S : Submonoid M) :
    LinearOrderedCommMonoid S :=
  Subtype.coe_injective.linearOrderedCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of an `OrderedCancelCommMonoid` is an `OrderedCancelCommMonoid`. -/
@[to_additive AddSubmonoid.toOrderedCancelAddCommMonoid
      "An `AddSubmonoid` of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`."]
instance toOrderedCancelCommMonoid [OrderedCancelCommMonoid M] (S : Submonoid M) :
    OrderedCancelCommMonoid S :=
  Subtype.coe_injective.orderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submonoid of a `LinearOrderedCancelCommMonoid` is a `LinearOrderedCancelCommMonoid`.
-/
@[to_additive AddSubmonoid.toLinearOrderedCancelAddCommMonoid
      "An `AddSubmonoid` of a `LinearOrderedCancelAddCommMonoid` is
      a `LinearOrderedCancelAddCommMonoid`."]
instance toLinearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid M] (S : Submonoid M) :
    LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.linearOrderedCancelCommMonoid (↑) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

section Preorder
variable (M)
variable [Monoid M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] {a : M}

/-- The submonoid of elements greater than `1`. -/
@[to_additive (attr := simps) nonneg "The submonoid of nonnegative elements."]
def oneLE : Submonoid M where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {M}

@[to_additive (attr := simp) mem_nonneg] lemma mem_oneLE : a ∈ oneLE M ↔ 1 ≤ a := Iff.rfl

end Preorder
end Submonoid
