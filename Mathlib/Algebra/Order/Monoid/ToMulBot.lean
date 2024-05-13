/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Group.Equiv.Basic

#align_import algebra.order.monoid.to_mul_bot from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _
#align with_zero.to_mul_bot WithZero.toMulBot

@[simp]
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl
#align with_zero.to_mul_bot_zero WithZero.toMulBot_zero

@[simp]
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑(Multiplicative.toAdd x) : WithBot α) :=
  rfl
#align with_zero.to_mul_bot_coe WithZero.toMulBot_coe

@[simp]
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl
#align with_zero.to_mul_bot_symm_bot WithZero.toMulBot_symm_bot

@[simp]
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl
#align with_zero.to_mul_bot_coe_of_add WithZero.toMulBot_coe_ofAdd

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id
#align with_zero.to_mul_bot_strict_mono WithZero.toMulBot_strictMono

@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl
#align with_zero.to_mul_bot_le WithZero.toMulBot_le

@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl
#align with_zero.to_mul_bot_lt WithZero.toMulBot_lt

end WithZero
