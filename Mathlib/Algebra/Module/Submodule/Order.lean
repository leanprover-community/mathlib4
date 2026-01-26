import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Ordered instances on submodules
-/

@[expose] public section

namespace Submodule
variable {R M : Type*}

section OrderedMonoid
variable [Semiring R]

/-- A submodule of an ordered additive monoid is an ordered additive monoid. -/
instance toIsOrderedAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] (S : Submodule R M) :
    IsOrderedAddMonoid S :=
  Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submodule of an ordered cancellative additive monoid is an ordered cancellative additive
monoid. -/
instance toIsOrderedCancelAddMonoid [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] [Module R M] (S : Submodule R M) :
    IsOrderedCancelAddMonoid S :=
  Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

end OrderedMonoid

end Submodule
