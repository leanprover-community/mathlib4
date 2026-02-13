/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Order dual

This file defines `OrderDual α`, a type synonym reversing the meaning of all inequalities,
with notation `αᵒᵈ`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

## Implementation notes

`OrderDual` is a one-field structure rather than a type alias, to prevent defeq abuse.
Explicit coercions should be used:
* `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
-/

@[expose] public section


variable {α : Type*}

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
structure OrderDual (α : Type*) where
  /-- Reinterpret a value of `α` in the order dual. -/
  toDual ::
  /-- Extract the value from the order dual. -/
  ofDual : α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

@[ext]
theorem ext {a b : αᵒᵈ} (h : ofDual a = ofDual b) : a = b := by
  cases a; cases b; exact congrArg toDual h

theorem ofDual_toDual (a : α) : ofDual (toDual a) = a := rfl
@[simp] theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a := by cases a; rfl
theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b := by
  constructor
  · intro h; exact congrArg ofDual h
  · intro h; exact congrArg toDual h
@[simp] theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b := by
  constructor
  · exact ext
  · intro h; exact congrArg ofDual h

/-- The equivalence between `αᵒᵈ` and `α`. -/
def equiv (α : Type*) : αᵒᵈ ≃ α where
  toFun := ofDual
  invFun := toDual
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h.map toDual

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  (equiv α).injective.subsingleton

instance (α : Type*) [LE α] : LE αᵒᵈ :=
  ⟨fun x y ↦ ofDual y ≤ ofDual x⟩

instance (α : Type*) [LT α] : LT αᵒᵈ :=
  ⟨fun x y ↦ ofDual y < ofDual x⟩

instance instOrd (α : Type*) [Ord α] : Ord αᵒᵈ where
  compare a b := compare (ofDual b) (ofDual a)

@[to_dual]
instance instSup (α : Type*) [Min α] : Max αᵒᵈ :=
  ⟨fun a b ↦ toDual (ofDual a ⊓ ofDual b)⟩

instance instIsTransLE [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

instance instIsTransLT [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

instance [LT α] [T : @Std.Trichotomous α LT.lt] : @Std.Trichotomous αᵒᵈ LT.lt where
  trichotomous a b h1 h2 := ext (T.trichotomous (ofDual a) (ofDual b) h2 h1)

instance instPreorder (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl x := le_refl (ofDual x)
  le_trans _ _ _ hab hbc := hbc.trans hab
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

instance instPartialOrder (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  __ := inferInstanceAs (Preorder αᵒᵈ)
  le_antisymm _ _ hab hba := ext (le_antisymm hba hab)

instance instDecidableLE [LE α] [inst : DecidableLE α] : DecidableLE αᵒᵈ := fun a b =>
  inst (ofDual b) (ofDual a)

instance instDecidableLT [LT α] [inst : DecidableLT α] : DecidableLT αᵒᵈ := fun a b =>
  inst (ofDual b) (ofDual a)

instance instDecidableEq [inst : DecidableEq α] : DecidableEq αᵒᵈ := fun a b =>
  decidable_of_iff (ofDual a = ofDual b) ofDual_inj

instance instLinearOrder (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  __ := inferInstanceAs (PartialOrder αᵒᵈ)
  __ := inferInstanceAs (Ord αᵒᵈ)
  le_total a b := (le_total (ofDual a) (ofDual b)).symm
  max a b := toDual (min (ofDual a) (ofDual b))
  min a b := toDual (max (ofDual a) (ofDual b))
  min_def a b := by
    change toDual (max (ofDual a) (ofDual b)) = if _ then a else b
    rw [max_comm, max_def, apply_ite toDual, toDual_ofDual, toDual_ofDual]
    exact if_congr Iff.rfl rfl rfl
  max_def a b := by
    change toDual (min (ofDual a) (ofDual b)) = if _ then b else a
    rw [min_comm, min_def, apply_ite toDual, toDual_ofDual, toDual_ofDual]
    exact if_congr Iff.rfl rfl rfl
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    change compare (ofDual b) (ofDual a) = compareOfLessAndEq a b
    simp only [LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, eq_comm]
    exact if_congr Iff.rfl rfl (if_congr ofDual_inj rfl rfl)

instance [Inhabited α] : Inhabited αᵒᵈ := ⟨toDual default⟩

end OrderDual

/-! ### `DenselyOrdered` for `OrderDual` -/

open OrderDual in
instance OrderDual.denselyOrdered (α : Type*) [LT α] [DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun a b (hab : ofDual b < ofDual a) ↦
    let ⟨c, hac, hcb⟩ := exists_between hab
    ⟨toDual c, hcb, hac⟩⟩

open OrderDual in
@[simp]
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨fun _ ↦ ⟨fun a b hab ↦
    let ⟨c, hac, hcb⟩ := @DenselyOrdered.dense αᵒᵈ _ _ (toDual b) (toDual a) hab
    ⟨ofDual c, hcb, hac⟩⟩,
   fun _ ↦ inferInstance⟩
