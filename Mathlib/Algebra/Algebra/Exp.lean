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

open Function

namespace Algebra

section Exp

variable {R : Type u} {A : Type w}
variable [Field R] [CharZero R]
variable [Semiring A] [Algebra R A]

def exp (a : A) (h : IsNilpotent a) : A :=
  --let k := nilpotency_class a h
  let five_factorial : R := Nat.factorial 5
  let inv_five_factorial : R := five_factorial⁻¹
  ∑ n ∈ Finset.range 11, (Nat.factorial n : R)⁻¹ • a

end Exp


end Algebra

open scoped Algebra
