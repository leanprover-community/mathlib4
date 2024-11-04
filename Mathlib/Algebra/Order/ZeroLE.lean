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
class ZeroLEClass (α : Type*) [LE α] [Zero α] : Prop where
  zero_le (x : α) : 0 ≤ x

/-- A class for types whose bottom element is one. Declaring this instance makes `1` the preferred
form for `⊥`. -/
@[to_additive ZeroLEClass]
class OneLEClass (α : Type*) [LE α] [One α] : Prop where
  one_le (x : α) : 1 ≤ x

@[to_additive (attr := simp) zero_le]
theorem one_le [LE α] [One α] [OneLEClass α] : 1 ≤ x :=
  OneLEClass.one_le x

instance (priority := 100) ZeroLEClass.toZeroLEOneClass [LE α] [Zero α] [One α] [ZeroLEClass α] :
    ZeroLEOneClass α :=
  ⟨zero_le _⟩

/-- Defines an `OrderBot` instance using `⊥ = 1`. -/
@[to_additive "Defines an `OrderBot` instance using `⊥ = 0`."]
def OneLEClass.toOrderBot (α : Type*) [LE α] [One α] [OneLEClass α] : OrderBot α := by
  letI : Bot α := ⟨1⟩
  exact ⟨one_le⟩

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

@[to_additive]
theorem one_lt_of_lt (h : x < y) : 1 < y :=
  one_le.trans_lt h

alias LT.lt.one_lt := one_lt_of_lt
alias LT.lt.pos := pos_of_lt

@[to_additive]
theorem ne_one_of_lt (h : x < y) : y ≠ 1 :=
  (one_lt_of_lt h).ne'

alias LT.lt.ne_one := ne_one_of_lt
alias LT.lt.ne_zero := ne_zero_of_lt

end Preorder

section PartialOrder

variable [PartialOrder α] [One α] [OneLEClass α]

@[to_additive (attr := simp)]
theorem bot_eq_one [OrderBot α] : (⊥ : α) = 1 :=
  isBot_one.eq_bot.symm

@[to_additive (attr := simp)]
theorem le_one_iff_eq_one : x ≤ 1 ↔ x = 1 :=
  one_le.le_iff_eq

alias le_zero_iff_eq_zero := nonpos_iff_eq_zero

alias ⟨eq_one_of_le_one, _⟩ := le_one_iff_eq_one
alias ⟨eq_zero_of_le_zero, _⟩ := le_zero_iff_eq_zero

alias LE.le.eq_one := eq_one_of_le_one
alias LE.le.eq_zero := eq_zero_of_le_zero

@[to_additive]
theorem one_lt_iff_ne_one : 1 < x ↔ x ≠ 1 :=
  one_le.gt_iff_ne

alias ⟨_, one_lt_of_ne⟩ := one_lt_iff_ne_one
alias ⟨_, pos_of_ne⟩ := pos_iff_ne_zero

alias Ne.one_lt := one_lt_of_ne
alias Ne.pos := pos_of_ne

@[to_additive]
theorem eq_one_or_one_lt (x : α) : x = 1 ∨ 1 < x :=
  one_le.eq_or_gt

end PartialOrder

namespace NeZero

variable [PartialOrder α] [Zero α] [ZeroLEClass α]

theorem pos (x : α) [NeZero x] : 0 < x :=
  pos_of_ne NeZero.out

theorem of_lt (h : x < y) : NeZero y :=
  ⟨h.ne_zero⟩

end NeZero

section LinearOrder

variable [LinearOrder α] [One α] [OneLEClass α]

@[to_additive (attr := simp)]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left one_le

@[to_additive (attr := simp)]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right one_le

@[to_additive (attr := simp)]
theorem one_max (a : α) : max 1 a = a :=
  max_eq_right one_le

@[to_additive (attr := simp)]
theorem max_one (a : α) : max a 1 = a :=
  max_eq_left one_le

@[to_additive (attr := simp)]
theorem max_eq_one_iff {a b : α} : max a b = 1 ↔ a = 1 ∧ b = 1 := by
  letI := OneLEClass.toOrderBot α
  exact max_eq_bot

end LinearOrder

namespace Nat

instance instZeroLEClass : ZeroLEClass ℕ where
  zero_le := zero_le

instance instOrderBot : OrderBot ℕ :=
  ZeroLEClass.toOrderBot ℕ

instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩

@[deprecated _root_.bot_eq_zero (since := "2024-11-02")]
protected lemma bot_eq_zero : ⊥ = 0 := rfl

end Nat
