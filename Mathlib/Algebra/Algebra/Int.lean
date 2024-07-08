/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Oliver Nash
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Int.CharZero

/-!
# Algebra instances for actions by ℚ and theorems about them

-/

variable (R : Type*) [Ring R]

-- Lower the priority so that `Algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `Algebra.id ℤ` and `algebraInt ℤ` are not yet defeq.
-- TODO: fix this by adding an `ofInt` field to rings.
/-- Ring ⥤ ℤ-Alg -/
instance (priority := 99) algebraInt : Algebra ℤ R where
  commutes' := Int.cast_commute
  smul_def' _ _ := zsmul_eq_mul _ _
  toRingHom := Int.castRingHom R
#align algebra_int algebraInt

theorem intCast_smul {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V] (r : ℤ) (x : V) :
    (r : k) • x = r • x :=
  algebraMap_smul k r x
#align int_cast_smul intCast_smul

/-- A special case of `eq_intCast'` that happens to be true definitionally -/
@[simp]
theorem algebraMap_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl
#align algebra_map_int_eq algebraMap_int_eq

variable {R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => Algebra.algebra_ext P Q <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align int_algebra_subsingleton int_algebra_subsingleton

namespace NoZeroSMulDivisors

variable {R : Type*}

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_int [Ring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℤ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℤ R).injective_int
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_int NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_int


