import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Faithful actions involving groups with zero
-/

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {α : Type*}

/-- `Monoid.toMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance IsRightCancelMulZero.faithfulSMul [MonoidWithZero α] [IsRightCancelMulZero α] :
    FaithfulSMul α α where
  eq_of_smul_eq_smul h := by
    cases subsingleton_or_nontrivial α
    · exact Subsingleton.elim ..
    · exact mul_left_injective₀ one_ne_zero (h 1)
