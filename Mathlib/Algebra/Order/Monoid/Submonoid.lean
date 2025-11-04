/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# Ordered instances on submonoids
-/

assert_not_exists MonoidWithZero

namespace SubmonoidClass
variable {M S : Type*} [SetLike S M]

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an ordered monoid is an ordered monoid. -/
@[to_additive /-- An `AddSubmonoid` of an ordered additive monoid is an ordered additive monoid. -/]
instance (priority := 75) toIsOrderedMonoid [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedMonoid s :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoidClass.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
instance (priority := 75) toIsOrderedCancelMonoid
    [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedCancelMonoid s :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl


end SubmonoidClass

namespace Submonoid
variable {M : Type*}

/-- A submonoid of an ordered monoid is an ordered monoid. -/
@[to_additive /-- An `AddSubmonoid` of an ordered additive monoid is an ordered additive monoid. -/]
instance toIsOrderedMonoid [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    (S : Submonoid M) : IsOrderedMonoid S :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoid.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
instance toIsOrderedCancelMonoid [CommMonoid M] [PartialOrder M] [IsOrderedCancelMonoid M]
    (S : Submonoid M) : IsOrderedCancelMonoid S :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl

section Preorder
variable (M)
variable [Monoid M] [Preorder M] [MulLeftMono M] {a : M}

/-- The submonoid of elements that are at least `1`. -/
@[to_additive (attr := simps) /-- The submonoid of nonnegative elements. -/]
def oneLE : Submonoid M where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {M}

@[to_additive (attr := simp)] lemma mem_oneLE : a ∈ oneLE M ↔ 1 ≤ a := Iff.rfl

end Preorder
end Submonoid
