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

universe u w


namespace Algebra

section Exp

variable {R : Type u} {A : Type w}
variable [Field R] [CharZero R]
variable [Semiring A] [Algebra R A]

noncomputable def exponent (a : A) : ℕ :=
    sInf {k | a ^ k = 0}

noncomputable def exp (a : A) [Field R]: A :=
  ∑ n ∈ Finset.range (exponent a), (Nat.factorial n : R)⁻¹ • (a ^ n)

theorem wellDef {k : ℕ} (a : A) (h : a ^ k = 0) :
    exp (R := R) a  = ∑ n ∈ Finset.range k, (Nat.factorial n : R)⁻¹ • (a ^ n) := by
  sorry

theorem mul_add (a b : A) (h : a * b = b * a) (IsNilpotent a : A) (IsNilpotent b : A) :
    exp (R := R) (a + b) = (exp (R := R) a : A) * (exp (R := R) b) := by
  sorry

end Exp

end Algebra
