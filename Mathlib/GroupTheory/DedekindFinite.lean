import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs

/-!
# Finite monoids are Dedekind-finite
-/

@[expose] public section

instance (M) [Monoid M] [Finite M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm {a b} hab := by
    have ⟨c, hbc⟩ := Finite.surjective_of_injective (isLeftRegular_of_mul_eq_one hab) 1
    rwa [left_inv_eq_right_inv hab hbc]
