/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

/-!
# Instances for Euclidean domains
* `int.euclidean_domain`: shows that `ℤ` is a Euclidean domain.
* `field.to_euclidean_domain`: shows that any field is a Euclidean domain.
-/


theorem Int.ofNat_mod_negSucc (m n : Nat) :
  (ofNat m % (Int.negSucc n) : Int) = ofNat (m % n.succ) := rfl
theorem Int.negSucc_mod_ofNat (m n : Nat) :
  (Int.negSucc m % (ofNat n) : Int) = -ofNat (m.succ % n) := rfl
theorem Int.negSucc_mod_negSucc (m n : Nat) :
  (Int.negSucc m % (negSucc n) : Int) = -ofNat (m.succ % n.succ) := rfl

instance Int.euclideanDomain : EuclideanDomain ℤ :=
  { inferInstanceAs (CommRing Int), inferInstanceAs (Nontrivial Int) with
    add := (· + ·), mul := (· * ·), one := 1, zero := 0,
    neg := Neg.neg,
    quotient := (· / ·), quotient_zero := Int.div_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := fun a b => Int.div_add_mod _ _,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
    remainder_lt := fun a b b0 => by
        dsimp only
        cases a <;> cases b
        · simp only [Int.ofNat_mod_ofNat, natAbs_ofNat]
          rw [Int.ofNat_ne_zero, ←Nat.pos_iff_ne_zero] at b0
          apply Nat.mod_lt _ b0
        · rw [Int.ofNat_mod_negSucc, natAbs_ofNat, natAbs_negSucc]
          apply Nat.mod_lt
          apply Nat.succ_pos
        · rw [Int.negSucc_mod_ofNat, natAbs_ofNat, natAbs_neg, natAbs_ofNat]
          rw [Int.ofNat_ne_zero, ←Nat.pos_iff_ne_zero] at b0
          apply Nat.mod_lt _ b0
        · rw [Int.negSucc_mod_negSucc, natAbs_neg, natAbs_ofNat, natAbs_negSucc]
          apply Nat.mod_lt
          apply Nat.succ_pos
    mul_left_not_lt := fun a b b0 =>
      not_lt_of_ge <| by
        rw [← mul_one a.natAbs, Int.natAbs_mul]
        rw [←Int.natAbs_pos] at b0
        exact Nat.mul_le_mul_of_nonneg_left b0  }
