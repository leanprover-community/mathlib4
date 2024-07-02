/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Oliver Nash
-/

import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Algebra instances for actions by ℕ, ℤ, and ℚ and theorems about them

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

namespace RingHom

variable {R S : Type*}

-- Porting note: changed `[Ring R] [Ring S]` to `[Semiring R] [Semiring S]`
-- otherwise, Lean failed to find a `Subsingleton (ℚ →+* S)` instance
@[simp]
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r
#align ring_hom.map_rat_algebra_map RingHom.map_rat_algebraMap

end RingHom

section Rat

instance algebraRat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α where
  smul := (· • ·)
  smul_def' := Rat.smul_def
  toRingHom := Rat.castHom α
  commutes' := Rat.cast_commute
#align algebra_rat algebraRat

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra NNRat ℚ :=
  NNRat.coeHom.toAlgebra

/-- The two `Algebra ℚ ℚ` instances should coincide. -/
example : algebraRat = Algebra.id ℚ :=
  rfl

@[simp] theorem algebraMap_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ := rfl
#align algebra_map_rat_rat algebraMap_rat_rat

instance algebra_rat_subsingleton {α} [Semiring α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩
#align algebra_rat_subsingleton algebra_rat_subsingleton

end Rat

section Int

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

end Int

namespace NoZeroSMulDivisors

variable {R A : Type*}

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_nat [Semiring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℕ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℕ R).injective_nat
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_nat NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_nat

-- see note [lower instance priority]
instance (priority := 100) CharZero.noZeroSMulDivisors_int [Ring R] [NoZeroDivisors R]
    [CharZero R] : NoZeroSMulDivisors ℤ R :=
  NoZeroSMulDivisors.of_algebraMap_injective <| (algebraMap ℤ R).injective_int
#align no_zero_smul_divisors.char_zero.no_zero_smul_divisors_int NoZeroSMulDivisors.CharZero.noZeroSMulDivisors_int


