/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.Defs

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

/-!
# Basic instances for the natural numbers

This file contains:
* Algebraic instances on the natural numbers
* Basic lemmas about natural numbers that require more imports than available in
  `Data.Nat.Defs`.
-/

open Multiplicative

namespace Nat

/-! ### Instances -/

instance commSemiring : CommSemiring ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  mul_comm := Nat.mul_comm
  natCast n := n
  natCast_zero := rfl
  natCast_succ n := rfl
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ _ _ := by dsimp only; rw [Nat.add_comm, Nat.right_distrib, Nat.one_mul]
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := Nat.pow_succ'

/-! Extra instances to short-circuit type class resolution and ensure computability -/

instance addCommMonoid : AddCommMonoid ℕ :=
  inferInstance

instance addMonoid : AddMonoid ℕ :=
  inferInstance

instance monoid : Monoid ℕ :=
  inferInstance

instance commMonoid : CommMonoid ℕ :=
  inferInstance

instance commSemigroup : CommSemigroup ℕ :=
  inferInstance

instance semigroup : Semigroup ℕ :=
  inferInstance

instance addCommSemigroup : AddCommSemigroup ℕ :=
  inferInstance

instance addSemigroup : AddSemigroup ℕ :=
  inferInstance

instance distrib : Distrib ℕ :=
  inferInstance

instance semiring : Semiring ℕ :=
  inferInstance

instance cancelCommMonoidWithZero : CancelCommMonoidWithZero ℕ :=
  { (inferInstance : CommMonoidWithZero ℕ) with
    mul_left_cancel_of_ne_zero :=
      fun h1 h2 => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) h2 }
#align nat.cancel_comm_monoid_with_zero Nat.cancelCommMonoidWithZero

/-! ### Extra lemmas -/

protected lemma nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl
#align nat.nsmul_eq_mul Nat.nsmul_eq_mul

section Multiplicative

lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align nat.to_add_pow Nat.toAdd_pow

@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm
#align nat.of_add_mul Nat.ofAdd_mul

end Multiplicative
end Nat
