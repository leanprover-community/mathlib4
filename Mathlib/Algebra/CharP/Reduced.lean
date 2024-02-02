/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.ExpChar
import Mathlib.RingTheory.Nilpotent

#align_import algebra.char_p.basic from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Results about characteristic p reduced rings
-/


open Finset

open BigOperators

section

variable(R : Type*) [CommRing R] [IsReduced R] (p n : ℕ) [ExpChar R p]

theorem pow_char_pow_inj : (fun r : R ↦ r ^ p ^ n).Injective := fun x y H ↦ by
  rw [← sub_eq_zero] at H ⊢
  rw [← sub_pow_char_pow] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩

theorem frobenius_inj : Function.Injective (frobenius R p) := by
  convert pow_char_pow_inj R p 1; rw [pow_one]; rfl
#align frobenius_inj frobenius_inj

end

/-- If `ringChar R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
theorem isSquare_of_charTwo' {R : Type*} [Finite R] [CommRing R] [IsReduced R] [CharP R 2]
    (a : R) : IsSquare a := by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)
#align is_square_of_char_two' isSquare_of_charTwo'

variable {R : Type*} [CommRing R] [IsReduced R]

@[simp]
theorem ExpChar.pow_prime_pow_mul_eq_one_iff (p k m : ℕ) [ExpChar R p] (x : R) :
    x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 := by
  rw [pow_mul']
  convert (pow_char_pow_inj R p k).eq_iff
  rw [one_pow]
#align char_p.pow_prime_pow_mul_eq_one_iff ExpChar.pow_prime_pow_mul_eq_one_iff

@[deprecated] alias CharP.pow_prime_pow_mul_eq_one_iff := ExpChar.pow_prime_pow_mul_eq_one_iff
