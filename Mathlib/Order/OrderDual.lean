/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Order.Basic

/-!
# Order dual

This file defines `OrderDual α`, a type synonym reversing the meaning of all inequalities,
with notation `αᵒᵈ`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`. Instead, explicit
coercions should be inserted:
* `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
-/

@[expose] public section


variable {α : Type*}

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
def OrderDual (α : Type*) : Type _ :=
  α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type*) [LE α] : LE αᵒᵈ :=
  ⟨fun x y : α ↦ y ≤ x⟩

instance (α : Type*) [LT α] : LT αᵒᵈ :=
  ⟨fun x y : α ↦ y < x⟩

instance instOrd (α : Type*) [Ord α] : Ord αᵒᵈ where
  compare := fun (a b : α) ↦ compare b a

@[to_dual]
instance instSup (α : Type*) [Min α] : Max αᵒᵈ :=
  ⟨((· ⊓ ·) : α → α → α)⟩

instance instIsTransLE [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans := fun _ _ _ hab hbc ↦ T.trans _ _ _ hbc hab

instance instIsTransLT [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans := fun _ _ _ hab hbc ↦ T.trans _ _ _ hbc hab

instance [LT α] [T : @Std.Trichotomous α LT.lt] : @Std.Trichotomous αᵒᵈ LT.lt where
  trichotomous a b := by rw [eq_comm]; exact T.trichotomous b a

instance instPreorder (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl := fun _ ↦ le_refl _
  le_trans := fun _ _ _ hab hbc ↦ hbc.trans hab
  lt_iff_le_not_ge := fun _ _ ↦ lt_iff_le_not_ge

instance instPartialOrder (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  __ := inferInstanceAs (Preorder αᵒᵈ)
  le_antisymm := fun a b hab hba ↦ @le_antisymm α _ a b hba hab

instance (α : Type*) [DecidableEq α] : DecidableEq (αᵒᵈ) := ‹DecidableEq α›

instance (α : Type*) [LT α] [DecidableLT α] : DecidableLT (αᵒᵈ) :=
  inferInstanceAs <| DecidableRel (fun a b : α ↦ b < a)

instance (α : Type*) [LE α] [DecidableLE α] : DecidableLE (αᵒᵈ) :=
  inferInstanceAs <| DecidableRel (fun a b : α ↦ b ≤ a)

instance instLinearOrder (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  __ := inferInstanceAs (Ord αᵒᵈ)
  le_total := fun a b : α ↦ le_total b a
  max := fun a b ↦ (min a b : α)
  min := fun a b ↦ (max a b : α)
  min_def := fun a b ↦ show (max .. : α) = _ by rw [max_comm, max_def]; rfl
  max_def := fun a b ↦ show (min .. : α) = _ by rw [min_comm, min_def]; rfl
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, eq_comm]
    rfl

/-- The opposite linear order to a given linear order -/
def _root_.LinearOrder.swap (α : Type*) (_ : LinearOrder α) : LinearOrder α :=
  inferInstanceAs <| LinearOrder (OrderDual α)

instance : ∀ [Inhabited α], Inhabited αᵒᵈ := fun [x : Inhabited α] => x

theorem Ord.dual_dual (α : Type*) [H : Ord α] : OrderDual.instOrd αᵒᵈ = H :=
  rfl

theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
  rfl

theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
    OrderDual.instPartialOrder αᵒᵈ = H :=
  rfl

theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
    OrderDual.instLinearOrder αᵒᵈ = H :=
  rfl

end OrderDual

/-! ### `DenselyOrdered` for `OrderDual` -/

instance OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha ↦ (@exists_between α _ h _ _ ha).imp fun _ ↦ And.symm⟩

@[simp]
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨by convert @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩
