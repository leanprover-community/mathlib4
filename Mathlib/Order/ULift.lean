/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Logic.Function.ULift
public import Mathlib.Order.Basic

/-! # Ordered structures on `ULift.{v} α`

Once these basic instances are setup, the instances of more complex typeclasses should live next to
the corresponding `Prod` instances.
-/

@[expose] public section

namespace ULift

open Batteries

universe v u

variable {α : Type u}

instance [LE α] : LE (ULift.{v} α) where le x y := x.down ≤ y.down

@[simp, to_dual self] theorem up_le [LE α] {a b : α} : up a ≤ up b ↔ a ≤ b := Iff.rfl
@[simp, to_dual self] theorem down_le [LE α] {a b : ULift α} : down a ≤ down b ↔ a ≤ b := Iff.rfl

instance [LT α] : LT (ULift.{v} α) where lt x y := x.down < y.down

@[simp, to_dual self] theorem up_lt [LT α] {a b : α} : up a < up b ↔ a < b := Iff.rfl
@[simp, to_dual self] theorem down_lt [LT α] {a b : ULift α} : down a < down b ↔ a < b := Iff.rfl

instance [BEq α] : BEq (ULift.{v} α) where beq x y := x.down == y.down

@[simp] theorem up_beq [BEq α] (a b : α) : (up a == up b) = (a == b) := rfl
@[simp] theorem down_beq [BEq α] (a b : ULift α) : (down a == down b) = (a == b) := rfl

instance [Ord α] : Ord (ULift.{v} α) where compare x y := compare x.down y.down

@[simp] theorem up_compare [Ord α] (a b : α) : compare (up a) (up b) = compare a b := rfl
@[simp] theorem down_compare [Ord α] (a b : ULift α) : compare (down a) (down b) = compare a b :=
  rfl

@[to_dual]
instance [Max α] : Max (ULift.{v} α) where max x y := up <| x.down ⊔ y.down

@[to_dual (attr := simp)]
theorem up_sup [Max α] (a b : α) : up (a ⊔ b) = up a ⊔ up b := rfl

@[to_dual (attr := simp)]
theorem down_sup [Max α] (a b : ULift α) : down (a ⊔ b) = down a ⊔ down b := rfl

instance [SDiff α] : SDiff (ULift.{v} α) where sdiff x y := up <| x.down \ y.down

@[simp] theorem up_sdiff [SDiff α] (a b : α) : up (a \ b) = up a \ up b := rfl
@[simp] theorem down_sdiff [SDiff α] (a b : ULift α) : down (a \ b) = down a \ down b := rfl

instance [Compl α] : Compl (ULift.{v} α) where compl x := up <| x.downᶜ

@[simp] theorem up_compl [Compl α] (a : α) : up (aᶜ) = (up a)ᶜ := rfl
@[simp] theorem down_compl [Compl α] (a : ULift α) : down aᶜ = (down a)ᶜ := rfl

instance [Ord α] [inst : Std.OrientedOrd α] : Std.OrientedOrd (ULift.{v} α) where
  eq_swap := inst.eq_swap

instance [Ord α] [inst : Std.TransOrd α] : Std.TransOrd (ULift.{v} α) where
  isLE_trans := inst.isLE_trans

instance [BEq α] [Ord α] [inst : Std.LawfulBEqOrd α] : Std.LawfulBEqOrd (ULift.{v} α) where
  compare_eq_iff_beq := inst.compare_eq_iff_beq

instance [LT α] [Ord α] [inst : Std.LawfulLTOrd α] : Std.LawfulLTOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt

instance [LE α] [Ord α] [inst : Std.LawfulLEOrd α] : Std.LawfulLEOrd (ULift.{v} α) where
  isLE_iff_le := inst.isLE_iff_le

instance [LE α] [LT α] [BEq α] [Ord α] [inst : Std.LawfulBOrd α] :
    Std.LawfulBOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt
  isLE_iff_le := inst.isLE_iff_le

instance [Preorder α] : Preorder (ULift.{v} α) :=
  Preorder.lift ULift.down

instance [PartialOrder α] : PartialOrder (ULift.{v} α) :=
  PartialOrder.lift ULift.down ULift.down_injective

end ULift
