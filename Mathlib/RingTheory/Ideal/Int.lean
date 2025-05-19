/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing

/-!
# Ideal of `ℤ`

## Main definitions

## Main results

-/

theorem Int.ideal_span_isMaximal_of_prime (p : ℕ) [Fact (Nat.Prime p)] :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField _ (Field.toIsField _)
