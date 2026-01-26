
/-! Results about the cardinality of a quotient module. -/

public section

namespace Submodule

open LinearMap QuotientAddGroup

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem card_eq_card_quotient_mul_card (S : Submodule R M) :
    Nat.card M = Nat.card S * Nat.card (M ⧸ S) := by
  rw [mul_comm, ← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

end Submodule
