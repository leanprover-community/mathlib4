/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Nilpotent

#align_import algebra.char_p.basic from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!
# Results about characteristic p reduced rings
-/


open Finset

open BigOperators

theorem frobenius_inj (R : Type*) [CommRing R] [IsReduced R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    Function.Injective (frobenius R p) := fun x h H => by
  rw [← sub_eq_zero] at H ⊢
  rw [← frobenius_sub] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩
#align frobenius_inj frobenius_inj

/-- If `ringChar R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
theorem isSquare_of_charTwo' {R : Type*} [Finite R] [CommRing R] [IsReduced R] [CharP R 2]
    (a : R) : IsSquare a := by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)
#align is_square_of_char_two' isSquare_of_charTwo'

namespace CharP

variable {R : Type*} [CommRing R] [IsReduced R]

@[simp]
theorem pow_prime_pow_mul_eq_one_iff (p k m : ℕ) [Fact p.Prime] [CharP R p] (x : R) :
    x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 := by
  induction' k with k hk
  · rw [pow_zero, one_mul]
  · refine' ⟨fun h => _, fun h => _⟩
    · rw [pow_succ, mul_assoc, pow_mul', ← frobenius_def, ← frobenius_one p] at h
      exact hk.1 (frobenius_inj R p h)
    · rw [pow_mul', h, one_pow]
#align char_p.pow_prime_pow_mul_eq_one_iff CharP.pow_prime_pow_mul_eq_one_iff

end CharP
