/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Order.Basic

/-! # Ordered structures on `ULift.{v} α`

Once these basic instances are setup, the instances of more complex typeclasses should live next to
the corresponding `Prod` instances.
-/

namespace ULift

universe v u

variable {α : Type u}

instance [LE α] : LE (ULift.{v} α) where le x y := x.down ≤ y.down

@[simp] theorem up_le [LE α] {a b : α} : up a ≤ up b ↔ a ≤ b := Iff.rfl
@[simp] theorem down_le [LE α] {a b : ULift α} : down a ≤ down b ↔ a ≤ b := Iff.rfl

instance [LT α] : LT (ULift.{v} α) where lt x y := x.down < y.down

@[simp] theorem up_lt [LT α] {a b : α} : up a < up b ↔ a < b := Iff.rfl
@[simp] theorem down_lt [LT α] {a b : ULift α} : down a < down b ↔ a < b := Iff.rfl

instance [Ord α] : Ord (ULift.{v} α) where compare x y := compare x.down y.down

@[simp] theorem up_compare [Ord α] (a b : α) : compare (up a) (up b) = compare a b := rfl
@[simp] theorem down_compare [Ord α] (a b : ULift α) :
  compare (down a) (down b) = compare a b := rfl

instance [Sup α] : Sup (ULift.{v} α) where sup x y := up <| x.down ⊔ y.down

@[simp] theorem up_sup [Sup α] (a b : α) : up (a ⊔ b) = up a ⊔ up b := rfl
@[simp] theorem down_sup [Sup α] (a b : ULift α) : down (a ⊔ b) = down a ⊔ down b := rfl

instance [Inf α] : Inf (ULift.{v} α) where inf x y := up <| x.down ⊓ y.down

@[simp] theorem up_inf [Inf α] (a b : α) : up (a ⊓ b) = up a ⊓ up b := rfl
@[simp] theorem down_inf [Inf α] (a b : ULift α) : down (a ⊓ b) = down a ⊓ down b := rfl

instance [SDiff α] : SDiff (ULift.{v} α) where sdiff x y := up <| x.down \ y.down

@[simp] theorem up_sdiff [SDiff α] (a b : α) : up (a \ b) = up a \ up b := rfl
@[simp] theorem down_sdiff [SDiff α] (a b : ULift α) : down (a \ b) = down a \ down b := rfl

instance [HasCompl α] : HasCompl (ULift.{v} α) where compl x := up <| x.downᶜ

@[simp] theorem up_compl [HasCompl α] (a : α) : up (aᶜ) = (up a)ᶜ := rfl
@[simp] theorem down_compl [HasCompl α] (a : ULift α) : down aᶜ = (down a)ᶜ := rfl

instance [Preorder α] : Preorder (ULift.{v} α) :=
  Preorder.lift ULift.down

instance [PartialOrder α] : PartialOrder (ULift.{v} α) :=
  PartialOrder.lift ULift.down ULift.down_injective

end ULift
