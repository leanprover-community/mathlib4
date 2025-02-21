/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Int.CharZero
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Further basic results about `Algebra`.

This file could usefully be split further.
-/
namespace Algebra

section Exp

variable (R : Type*) [Field R] [CharZero R]
variable (A : Type*) [Semiring A] [Algebra R A]

noncomputable def exp (a : A) : A :=
  ∑ n ∈ Finset.range (nilpotencyClass a), (Nat.factorial n : R)⁻¹ • (a ^ n)

theorem well_def {k : ℕ} (a : A) (h : a ^ k = 0) :
    ∑ n ∈ Finset.range k, (Nat.factorial n : R)⁻¹ • (a ^ n) = exp R A a := by
  sorry

-- theorem add_pow (h : Commute x y) (n : ℕ) :
theorem exp_add_mul (a b : A) (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp R A (a + b) = exp R A a * exp R A b := by
  sorry

theorem exp_inv (a : A) (h : IsNilpotent a) : IsUnit (exp R A a) := by
  sorry

end Exp

end Algebra
