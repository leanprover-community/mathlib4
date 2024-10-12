import Mathlib.LinearAlgebra.QuadraticForm.Basic

variable (R M N : Type*)

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (Q : QuadraticMap R M N)

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (Q : QuadraticMap R M N) : Submodule R M where
  carrier := { a : M | Q a = 0 ∧ }
  add_mem' := by
    intros a b ha hb
    simp only [Set.mem_setOf_eq]
  zero_mem' := map_zero _
  smul_mem' := sorry
