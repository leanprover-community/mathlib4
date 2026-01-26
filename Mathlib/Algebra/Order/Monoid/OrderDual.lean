
/-! # Ordered monoid structures on the order dual. -/

@[expose] public section

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αᵒᵈ where
  mul_le_mul_left _ _ h c := mul_le_mul_left h c

@[to_additive]
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelMonoid αᵒᵈ where
  le_of_mul_le_mul_left _ _ _ := le_of_mul_le_mul_left'

end OrderDual
