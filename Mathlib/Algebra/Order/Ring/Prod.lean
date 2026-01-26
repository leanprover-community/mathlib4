
/-!
# Products of ordered rings
-/

@[expose] public section

variable {α β : Type*}

instance [Semiring α] [PartialOrder α] [IsOrderedRing α]
    [Semiring β] [PartialOrder β] [IsOrderedRing β] : IsOrderedRing (α × β) where
  zero_le_one := ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩
