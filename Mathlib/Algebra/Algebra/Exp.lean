import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Nilpotent.Defs

namespace Algebra

section Exp

variable (R : Type*) [Field R] [CharZero R]
variable (A : Type*) [Semiring A] [Algebra R A]

noncomputable def exp (a : A) : A :=
  ∑ n ∈ Finset.range (nilpotencyClass a), (Nat.factorial n : R)⁻¹ • (a ^ n)

theorem well_def {k : ℕ} (a : A) (h : a ^ k = 0) :
    ∑ n ∈ Finset.range k, (Nat.factorial n : R)⁻¹ • (a ^ n) = exp R A a := by
  sorry

-- useful: add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero
-- useful: add_pow (h : Commute x y) (n : ℕ) : ...
-- useful: isNilpotent_add (h_comm : Commute x y) ...
theorem exp_add_mul (a b : A) (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp R A (a + b) = exp R A a * exp R A b := by
  sorry

theorem exp_inv (a : A) (h : IsNilpotent a) : IsUnit (exp R A a) := by
  sorry

end Exp

end Algebra
