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

/-!
# Further basic results about `Algebra`.

This file could usefully be split further.
-/

universe u v w u₁ v₁

open Function

namespace Algebra

section Exp

variable {R : Type u} {A : Type w}
variable [Field R] [CharZero R]
variable [Semiring A] [Algebra R A]

noncomputable def exp (a : A) (h : IsNilpotent a) : A :=
  a
  --∑ n in finset.range (nat.find hx + 1), (x^n) / (n! : R)

end Exp


end Algebra

open scoped Algebra
