/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Commutativity and associativity of action of integers on rings

This file proves that `ℕ` and `ℤ` act commutatively and associatively on (semi)rings.

## TODO

Those instances are in their own file only because they require much less imports than any existing
file they could go to. This is unfortunate and should be fixed by reorganising files.
-/

open scoped Int

variable {R : Type*}

instance NonUnitalNonAssocSemiring.toDistribSMul [NonUnitalNonAssocSemiring R] :
    DistribSMul R R where smul_add := mul_add

/-- Note that `AddCommMonoid.nat_isScalarTower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocSemiring.nat_isScalarTower [NonUnitalNonAssocSemiring R] :
    IsScalarTower ℕ R R where
  smul_assoc n x y := by
    induction n with
    | zero => simp
    | succ n ih => simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]

/-- Note that `AddCommGroup.int_isScalarTower` requires stronger assumptions on `R`. -/
instance NonUnitalNonAssocRing.int_isScalarTower [NonUnitalNonAssocRing R] :
    IsScalarTower ℤ R R where
  smul_assoc n x y :=
    match n with
    | (n : ℕ) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]
