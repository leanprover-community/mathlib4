/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Batteries.Data.Int.Order

open Nat

#align int.neg_succ_of_nat Int.negSucc

-- @[inherit_doc]
notation "ℤ" => Int

namespace Int

#align int.of_nat_zero Int.ofNat_zero
#align int.of_nat_one Int.ofNat_one
#align int.sub_nat_nat_of_sub_eq_zero Int.subNatNat_of_sub_eq_zero
#align int.sub_nat_nat_of_sub_eq_succ Int.subNatNat_of_sub_eq_succ
#align int.of_nat_add Int.ofNat_add
#align int.of_nat_mul Int.ofNat_mul
#align int.of_nat_succ Int.ofNat_succ
#align int.neg_of_nat_of_succ Int.neg_ofNat_succ
#align int.neg_neg_of_nat_succ Int.neg_negSucc

#align int.of_nat_eq_coe Int.ofNat_eq_coe

#align int.neg_succ_of_nat_coe Int.negSucc_coe
#align int.coe_nat_add Int.ofNat_add
#align int.coe_nat_mul Int.ofNat_mul
#align int.coe_nat_zero Int.ofNat_zero
#align int.coe_nat_one Int.ofNat_one
#align int.coe_nat_succ Int.ofNat_succ

protected theorem ofNat_add_out (m n : ℕ) : ↑m + ↑n = (↑(m + n) : ℤ) := rfl
#align int.coe_nat_add_out Int.ofNat_add_out

protected theorem ofNat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl
#align int.coe_nat_mul_out Int.ofNat_mul_out

protected theorem ofNat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl
#align int.coe_nat_add_one_out Int.ofNat_add_one_out

#align int.of_nat_add_of_nat Int.ofNat_add_ofNat

#align int.of_nat_add_neg_succ_of_nat Int.ofNat_add_negSucc
#align int.neg_succ_of_nat_add_of_nat Int.negSucc_add_ofNat
#align int.neg_succ_of_nat_add_neg_succ_of_nat Int.negSucc_add_negSucc
#align int.of_nat_mul_of_nat Int.ofNat_mul_ofNat
#align int.of_nat_mul_neg_succ_of_nat Int.ofNat_mul_negSucc'
#align int.neg_succ_of_nat_of_nat Int.negSucc_mul_ofNat'
#align int.mul_neg_succ_of_nat_neg_succ_of_nat Int.negSucc_mul_negSucc'

#align int.coe_nat_inj Int.ofNat.inj
#align int.of_nat_eq_of_nat_iff Int.ofNat_inj
#align int.coe_nat_eq_coe_nat_iff Int.ofNat_inj
#align int.neg_succ_of_nat_inj_iff Int.negSucc_inj
#align int.neg_succ_of_nat_eq Int.negSucc_eq

protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h
#align int.neg_inj Int.neg_eq_neg

#align int.sub_nat_nat_elim Int.subNatNat_elim
#align int.sub_nat_nat_add_left Int.subNatNat_add_left
#align int.sub_nat_nat_add_right Int.subNatNat_add_right
#align int.sub_nat_nat_add_add Int.subNatNat_add_add
#align int.sub_nat_nat_of_le Int.subNatNat_of_le
#align int.sub_nat_nat_of_lt Int.subNatNat_of_lt
#align int.nat_abs_of_nat Int.natAbs_ofNat

#align int.nat_abs Int.natAbs

#align int.nat_abs_pos_of_ne_zero Int.natAbs_pos
#align int.eq_zero_of_nat_abs_eq_zero Int.natAbs_eq_zero
#align int.nat_abs_zero Int.natAbs_zero
#align int.nat_abs_one Int.natAbs_one
#align int.nat_abs_mul_self Int.natAbs_mul_self
#align int.nat_abs_neg Int.natAbs_neg
#align int.nat_abs_eq Int.natAbs_eq
#align int.eq_coe_or_neg Int.eq_nat_or_neg

#align int.div Int.ediv
#align int.mod Int.emod
#align int.quot Int.div
#align int.rem Int.mod

#align int.sub_nat_nat_sub Int.subNatNat_subₓ -- reordered implicits
#align int.sub_nat_nat_add Int.subNatNat_add
#align int.sub_nat_nat_add_neg_succ_of_nat Int.subNatNat_add_negSucc

#align int.add_assoc_aux1 Int.add_assoc.aux1
#align int.add_assoc_aux2 Int.add_assoc.aux2

#align int.sub_nat_self Int.subNatNat_self

#align int.of_nat_mul_neg_of_nat Int.ofNat_mul_negOfNat
#align int.neg_of_nat_mul_of_nat Int.negOfNat_mul_ofNat
#align int.neg_succ_of_nat_mul_neg_of_nat Int.negSucc_mul_negOfNat
#align int.neg_of_nat_mul_neg_succ_of_nat Int.negOfNat_mul_negSucc
#align int.neg_of_nat_eq_sub_nat_nat_zero Int.negOfNat_eq_subNatNat_zero
#align int.of_nat_mul_sub_nat_nat Int.ofNat_mul_subNatNat
#align int.neg_of_nat_add Int.negOfNat_add
#align int.neg_succ_of_nat_mul_sub_nat_nat Int.negSucc_mul_subNatNat
#align int.distrib_left Int.mul_add
#align int.distrib_right Int.add_mul
#align int.of_nat_sub Int.ofNat_subₓ -- reordered implicits
#align int.neg_succ_of_nat_coe' Int.negSucc_coe'
#align int.coe_nat_sub Int.ofNat_sub
#align int.sub_nat_nat_eq_coe Int.subNatNat_eq_coe
#align int.to_nat_sub Int.toNat_sub

/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
def natMod (m n : ℤ) : ℕ := (m % n).toNat
#align int.nat_mod Int.natMod

#align int.sign_mul_nat_abs Int.sign_mul_natAbs

#align int.to_nat' Int.toNat'
