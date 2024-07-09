/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Oliver Nash
-/

import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Algebra.Basic

/-!
# Algebra instances for actions by ℕ and theorems specifically about them

-/

section Nat

variable {R : Type*} [Semiring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `Algebra.id` and `algebraNat` are not yet defeq.
-- TODO: fix this by adding an `ofNat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99) algebraNat : Algebra ℕ R where
  commutes' := Nat.cast_commute
  smul_def' _ _ := nsmul_eq_mul _ _
  toRingHom := Nat.castRingHom R
#align algebra_nat algebraNat

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by ext; simp⟩
#align nat_algebra_subsingleton nat_algebra_subsingleton

end Nat

namespace NoZeroSMulDivisors

variable {R : Type*}

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_nat [Semiring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℕ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℕ R).injective_nat
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_nat NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_nat

