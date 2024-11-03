/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Order.BoundedOrder

/-!
# Typeclass for `0 ≤ x` and `1 ≤ x`

We introduce `ZeroLEClass` and `OneLEClass` for types whose least element is also their zero or one
element. The purpose of this is to transfer the order lemmas of `⊥` to the otherwise more useful
algebraic forms `0` and `1`.
-/

variable {α : Type*} {x y : α}

/-- A class for types whose bottom element is zero. Declaring this instance makes `0` the preferred
form for `⊥`. -/
class ZeroLEClass (α : Type*) [LE α] [Zero α] where
  zero_le {x : α} : 0 ≤ x

/-- A class for types whose bottom element is one. Declaring this instance makes `1` the preferred
form for `⊥`. -/
@[to_additive ZeroLEClass]
class OneLEClass (α : Type*) [LE α] [One α] where
  one_le {x : α} : 1 ≤ x

@[to_additive (attr := simp) zero_le]
theorem one_le [LE α] [One α] [OneLEClass α] : 1 ≤ x :=
  OneLEClass.one_le

instance (priority := 100) ZeroLEClass.toZeroLEOneClass [LE α] [Zero α] [One α] [ZeroLEClass α] :
    ZeroLEOneClass α :=
  ⟨zero_le⟩

section Preorder

variable [Preorder α] [One α] [OneLEClass α]

@[to_additive (attr := simp) not_lt_zero]
theorem not_lt_one : ¬ x < 1 :=
  not_lt_of_le one_le

@[to_additive]
theorem isBot_one : IsBot (1 : α) :=
  fun _ ↦ one_le

@[to_additive]
theorem isMin_one : IsMin (1 : α) :=
  isBot_one.isMin

end Preorder

section PartialOrder

variable [PartialOrder α] [One α] [OneLEClass α]

@[to_additive (attr := simp)]
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 :=
  isBot_one.eq_bot.symm

@[to_additive (attr := simp) le_zero_iff_eq_zero]
theorem le_one_iff_eq_one : x ≤ 1 ↔ x = 1 :=
  ⟨fun h ↦ h.antisymm one_le, fun h ↦ h ▸ le_rfl⟩

@[to_additive]
theorem one_lt_iff_ne_one : 1 < x ↔ x ≠ 1 :=
  ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne one_le h.symm⟩

alias ⟨_, one_lt_of_ne⟩ := one_lt_iff_ne_one
alias ⟨_, pos_of_ne⟩ := pos_iff_ne_zero

alias Ne.one_lt := one_lt_of_ne
alias Ne.pos := pos_of_ne

@[to_additive]
theorem ne_one_of_lt (h : x < y) : y ≠ 1 :=
  (one_le.trans_lt h).ne'

alias LT.lt.ne_one := ne_one_of_lt
alias LT.lt.ne_zero := ne_zero_of_lt

@[to_additive]
theorem eq_one_or_one_lt (x : α) : x = 1 ∨ 1 < x :=
  one_le.eq_or_lt.imp_left Eq.symm

end PartialOrder

section LinearOrder

variable [LinearOrder α] [One α] [OneLEClass α]

@[to_additive (attr := simp)]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left one_le

@[to_additive (attr := simp)]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right one_le

end LinearOrder

namespace Nat

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le

instance instZeroLEClass : ZeroLEClass ℕ where
  zero_le := Nat.zero_le _

instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩

@[deprecated _root_.bot_eq_zero (since := "2024-11-02")]
protected lemma bot_eq_zero : ⊥ = 0 := rfl

end Nat
