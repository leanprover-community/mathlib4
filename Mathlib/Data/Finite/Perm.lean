
/-! # Properties of `Equiv.Perm` on `Finite` types

-/

public section

assert_not_exists Field

namespace Nat

theorem card_perm {α : Type*} [Finite α] : Nat.card (Equiv.Perm α) = (Nat.card α)! := by
  classical
  have := Fintype.ofFinite α
  rw [card_eq_fintype_card, card_eq_fintype_card, Fintype.card_perm]

end Nat
