/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

There is also `Data.Int.Cast.Lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `Data.Int.Cast.Defs` is `Algebra.Group.Basic`.
-/


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

/- warning: nat.cast_sub -> Nat.cast_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n m)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) m)))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16 : AddGroupWithOne.{u_1} R] {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (Eq.{succ u_1} R (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) (HSub.hSub.{0 0 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n m)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) n) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.16) m)))
Case conversion may be inaccurate. Consider using '#align nat.cast_sub Nat.cast_subₓ'. -/
@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]
#align nat.cast_sub Nat.cast_subₓ

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, _ => by rw [cast_succ, add_sub_cancel]; rfl
#align nat.cast_pred Nat.cast_pred

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

/- warning: int.cast_neg_succ_of_nat -> Int.cast_negSucc is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Int.negSucc n)) (Neg.neg.{u} R (SubNegMonoid.toHasNeg.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {R : Type.{u_1}} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811 (Int.negSucc n)) (Neg.neg.{u_1} R (AddGroupWithOne.toNeg.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.811) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ'. -/
@[simp, norm_cast]
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n
#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ

/- warning: int.cast_zero -> Int.cast_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R], Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{u} R 0 (OfNat.mk.{u} R 0 (Zero.zero.{u} R (AddZeroClass.toHasZero.{u} R (AddMonoid.toAddZeroClass.{u} R (AddMonoidWithOne.toAddMonoid.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848 (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (AddRightCancelMonoid.toZero.{u_1} R (AddCancelMonoid.toAddRightCancelMonoid.{u_1} R (AddGroup.toAddCancelMonoid.{u_1} R (AddGroupWithOne.toAddGroup.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.848))))))
Case conversion may be inaccurate. Consider using '#align int.cast_zero Int.cast_zeroₓ'. -/
@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero
#align int.cast_zero Int.cast_zeroₓ

/- warning: int.cast_coe_nat -> Int.cast_ofNat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1 1} a b] => self.0) Nat Int (HasLiftT.mk.{1 1} Nat Int (CoeTCₓ.coe.{1 1} Nat Int (CoeTCₓ.mk.{1 1} Nat Int Int.ofNat))) n)) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n)
but is expected to have type
  forall {R : Type.{u_1}} {n : Nat} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772 (Int.ofNat n)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.772) n)
Case conversion may be inaccurate. Consider using '#align int.cast_coe_nat Int.cast_ofNatₓ'. -/
@[simp high, nolint simpNF, norm_cast] -- this lemma competes with `Int.ofNat_eq_cast` to come later
theorem cast_ofNat (n : ℕ) : ((n : ℤ) : R) = n :=
  AddGroupWithOne.intCast_ofNat _
#align int.cast_coe_nat Int.cast_ofNatₓ

/- warning: int.cast_one -> Int.cast_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R], Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (OfNat.ofNat.{u} R 1 (OfNat.mk.{u} R 1 (One.one.{u} R (AddMonoidWithOne.toHasOne.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908 : AddGroupWithOne.{u_1} R], Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908 (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (OfNat.ofNat.{u_1} R 1 (One.toOfNat1.{u_1} R (AddMonoidWithOne.toOne.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Algebra.GroupWithZero.Defs._hyg.908))))
Case conversion may be inaccurate. Consider using '#align int.cast_one Int.cast_oneₓ'. -/
@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 := by
  erw [cast_ofNat, Nat.cast_one]
#align int.cast_one Int.cast_oneₓ

/- warning: int.cast_neg -> Int.cast_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Neg.neg.{0} Int Int.hasNeg n)) (Neg.neg.{u} R (SubNegMonoid.toHasNeg.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 : AddGroupWithOne.{u_1} R] (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 (Neg.neg.{0} Int Int.instNegInt n)) (Neg.neg.{u_1} R (AddGroupWithOne.toNeg.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.97 n))
Case conversion may be inaccurate. Consider using '#align int.cast_neg Int.cast_negₓ'.  -/
@[norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_ofNat, cast_negSucc]
  | -[n+1] => by erw [cast_ofNat, cast_negSucc, neg_neg]
#align int.cast_neg Int.cast_negₓ

/- warning: int.cast_sub_nat_nat -> Int.cast_subNatNat is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Nat) (n : Nat), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (Int.subNatNat m n)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Nat R (HasLiftT.mk.{1 succ u} Nat R (CoeTCₓ.coe.{1 succ u} Nat R (Nat.castCoe.{u} R (AddMonoidWithOne.toHasNatCast.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297 : AddGroupWithOne.{u_1} R] (m : Nat) (n : Nat), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297 (Int.subNatNat m n)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297)) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297) m) (Nat.cast.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.297) n))
Case conversion may be inaccurate. Consider using '#align int.cast_sub_nat_nat Int.cast_subNatNatₓ'. -/
@[simp]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n := by
  unfold subNatNat
  cases e : n - m
  · rw [cast_ofNat]
    simp [e, Nat.le_of_sub_eq_zero e]
  · rw [cast_negSucc, Nat.add_one, ← e, Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e,
      neg_sub]
#align int.cast_sub_nat_nat Int.cast_subNatNatₓ

-- porting note: already exists in `Std`, but still needs `#align`ed
#align int.neg_of_nat_eq Int.negOfNat_eq

@[simp]
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [Int.cast_neg, negOfNat_eq]
#align int.cast_neg_of_nat Int.cast_negOfNat

/- warning: int.cast_add -> Int.cast_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Int) (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (HAdd.hAdd.{0 0 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (HAdd.hAdd.{u u u} R R R (instHAdd.{u} R (AddZeroClass.toHasAdd.{u} R (AddMonoid.toAddZeroClass.{u} R (AddMonoidWithOne.toAddMonoid.{u} R (AddGroupWithOne.toAddMonoidWithOne.{u} R _inst_1))))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 : AddGroupWithOne.{u_1} R] (m : Int) (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 (HAdd.hAdd.{0 0 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (AddZeroClass.toAdd.{u_1} R (AddMonoid.toAddZeroClass.{u_1} R (AddMonoidWithOne.toAddMonoid.{u_1} R (AddGroupWithOne.toAddMonoidWithOne.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392))))) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 m) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.392 n))
Case conversion may be inaccurate. Consider using '#align int.cast_add Int.cast_addₓ'. -/
@[norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.ofNat_add, Nat.cast_add]
  | (m : ℕ), -[n+1] => by erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_iff_eq_add, add_assoc,
      eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] =>
    show (-[m + n + 1+1] : R) = _ by
      rw [cast_negSucc, cast_negSucc, cast_negSucc, ← neg_add_rev, ← Nat.cast_add,
        Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]
#align int.cast_add Int.cast_addₓ

/- warning: int.cast_sub -> Int.cast_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : AddGroupWithOne.{u} R] (m : Int) (n : Int), Eq.{succ u} R ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) (HSub.hSub.{0 0 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (HSub.hSub.{u u u} R R R (instHSub.{u} R (SubNegMonoid.toHasSub.{u} R (AddGroup.toSubNegMonoid.{u} R (AddGroupWithOne.toAddGroup.{u} R _inst_1)))) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) m) ((fun (a : Type) (b : Type.{u}) [self : HasLiftT.{1 succ u} a b] => self.0) Int R (HasLiftT.mk.{1 succ u} Int R (CoeTCₓ.coe.{1 succ u} Int R (Int.castCoe.{u} R (AddGroupWithOne.toHasIntCast.{u} R _inst_1)))) n))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 : AddGroupWithOne.{u_1} R] (m : Int) (n : Int), Eq.{succ u_1} R (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 (HSub.hSub.{0 0 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (HSub.hSub.{u_1 u_1 u_1} R R R (instHSub.{u_1} R (AddGroupWithOne.toSub.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666)) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 m) (Int.cast.{u_1} R inst._@.Mathlib.Data.Int.Cast.Defs._hyg.666 n))
Case conversion may be inaccurate. Consider using '#align int.cast_sub Int.cast_subₓ'. -/
@[norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]
#align int.cast_sub Int.cast_subₓ

section deprecated
set_option linter.deprecated false

@[norm_cast, deprecated]
theorem ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl
#align int.coe_nat_bit0 Int.ofNat_bit0

@[norm_cast, deprecated]
theorem ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl
#align int.coe_nat_bit1 Int.ofNat_bit1

@[norm_cast, deprecated]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 (n : R) :=
  Int.cast_add _ _
#align int.cast_bit0 Int.cast_bit0

@[norm_cast, deprecated]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 (n : R) :=
  by rw [bit1, Int.cast_add, Int.cast_one, cast_bit0]; rfl
#align int.cast_bit1 Int.cast_bit1

end deprecated

theorem cast_two : ((2 : ℤ) : R) = 2 :=
  show (((2 : ℕ) : ℤ) : R) = ((2 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
#align int.cast_two Int.cast_two

theorem cast_three : ((3 : ℤ) : R) = 3 :=
  show (((3 : ℕ) : ℤ) : R) = ((3 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
#align int.cast_three Int.cast_three

theorem cast_four : ((4 : ℤ) : R) = 4 :=
  show (((4 : ℕ) : ℤ) : R) = ((4 : ℕ) : R) by rw [cast_ofNat, Nat.cast_ofNat]
#align int.cast_four Int.cast_four

end Int
