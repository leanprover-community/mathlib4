/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Commutativity and associativity of action of integers on rings

This file proves that `ℕ` and `ℤ` act commutatively and associatively on (semi)rings.

## TODO

Those instances are in their own file only because they require much less imports than any existing
file they could go to. This is unfortunate and should be fixed by reorganising files.
-/

open scoped Int

variable {α : Type*}

/-- Note that `AddMonoid.nat_smulCommClass` requires stronger assumptions on `α`. -/
instance NonUnitalNonAssocSemiring.nat_smulCommClass [NonUnitalNonAssocSemiring α] :
    SMulCommClass ℕ α α where
  smul_comm n x y := by
    induction' n with n ih
    · simp [zero_nsmul]
    · simp_rw [succ_nsmul, smul_eq_mul, mul_add, ← smul_eq_mul, ih]
#align non_unital_non_assoc_semiring.nat_smul_comm_class NonUnitalNonAssocSemiring.nat_smulCommClass

/-- Note that `AddCommMonoid.nat_isScalarTower` requires stronger assumptions on `α`. -/
instance NonUnitalNonAssocSemiring.nat_isScalarTower [NonUnitalNonAssocSemiring α] :
    IsScalarTower ℕ α α where
  smul_assoc n x y := by
    induction' n with n ih
    · simp [zero_nsmul]
    · simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]
#align non_unital_non_assoc_semiring.nat_is_scalar_tower NonUnitalNonAssocSemiring.nat_isScalarTower

/-- Note that `AddMonoid.int_smulCommClass` requires stronger assumptions on `α`. -/
instance NonUnitalNonAssocRing.int_smulCommClass [NonUnitalNonAssocRing α] :
    SMulCommClass ℤ α α where
  smul_comm n x y :=
    match n with
    | (n : ℕ) => by simp_rw [natCast_zsmul, smul_comm]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, mul_neg, mul_smul_comm]
#align non_unital_non_assoc_ring.int_smul_comm_class NonUnitalNonAssocRing.int_smulCommClass

/-- Note that `AddCommGroup.int_isScalarTower` requires stronger assumptions on `α`. -/
instance NonUnitalNonAssocRing.int_isScalarTower [NonUnitalNonAssocRing α] :
    IsScalarTower ℤ α α where
  smul_assoc n x y :=
    match n with
    | (n : ℕ) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]
#align non_unital_non_assoc_ring.int_is_scalar_tower NonUnitalNonAssocRing.int_isScalarTower
