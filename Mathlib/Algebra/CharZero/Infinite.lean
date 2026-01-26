import Mathlib.Data.Finite.Defs

/-! # A characteristic-zero semiring is infinite -/

@[expose] public section


open Set

variable (M : Type*) [AddMonoidWithOne M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective Nat.cast Nat.cast_injective
