/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Hom.Basic

/-!
# Reverse Lexicographic order
This file defines the reverse lexicographic relation for pairs of orders, partial orders and linear
orders. We implement RevLex as a type alias with a single-field structure to avoid defeq abuse.

## Main declarations
* `Prod.RevLex.LexEquiv`: The order equivalence between a Lex product and a RevLex product.

## Notation
* `α ×ᵣ β`: `RevLex α × β`, equipped with the reverse lexicographic order

## TODO
* `Prod.revLex.<pre/partial/linear>Order`: Instances lifting the orders on `α` and `β` to `α ×ᵣ β`.
* Copy more things from `Mathlib.Data.Prod.Lex`.

-/

variable {α β : Type*}

/-- A one-field structure as a type synonym to equip a type with its reverse lexicographic order. -/
structure RevLex (α : Type*) where
/-- The underlying object -/
  obj : α

/-- `toRevLex` is the identity equivalence to the type synonym. -/
def toRevLex : α ≃ RevLex α where
  toFun a := ⟨ a ⟩
  invFun a := a.obj
  left_inv := congrFun rfl
  right_inv := congrFun rfl

/-- `ofRevLex` is the identity equivalence from the type synonym. -/
def ofRevLex : RevLex α ≃ α :=
  toRevLex.symm

@[simp]
theorem toRevLex_symm_eq : (@toRevLex α).symm = ofRevLex :=
  rfl

@[simp]
theorem ofRevLex_symm_eq : (@ofRevLex α).symm = toRevLex :=
  rfl

@[simp]
theorem toRevLex_ofRevLex (a : RevLex α) : toRevLex (ofRevLex a) = a :=
  rfl

@[simp]
theorem ofRevLex_toRevLex (a : α) : ofRevLex (toRevLex a) = a :=
  rfl

theorem toRevLex_inj {a b : α} : toRevLex a = toRevLex b ↔ a = b := by simp

theorem ofRevLex_inj {a b : RevLex α} : ofRevLex a = ofRevLex b ↔ a = b := by simp

namespace Prod

variable {α : Type*} {β : Type*}
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)

/-- The relation on a reverse lexicographic product. -/
protected inductive RevLex : α × β → α × β → Prop where
  /--
  If the second projections of two pairs are ordered, then they are reverse lexicographically
  ordered.
  -/
  | left  {a₁} (b₁) {a₂} (b₂) (h : rb b₁ b₂) : Prod.RevLex (a₁, b₁) (a₂, b₂)
  /--
  If the second projections of two pairs are equal, then they are reverse lexicographically ordered
  if the first projections are ordered.
  -/
  | right (b) {a₁ a₂} (h : ra a₁ a₂)         : Prod.RevLex (a₁, b) (a₂, b)

theorem revLex_def {r : α → α → Prop} {s : β → β → Prop} {p q : α × β} :
    Prod.RevLex r s p q ↔ s p.2 q.2 ∨ p.2 = q.2 ∧ r p.1 q.1 :=
  ⟨fun h => by cases h <;> simp [*], fun h =>
    match p, q, h with
    | _, _, Or.inl h => RevLex.left _ _ h
    | (_, _), (_, _), Or.inr ⟨e, h⟩ => by subst e; exact RevLex.right _ h⟩

namespace RevLex

open Batteries

@[inherit_doc] notation:35 α " ×ᵣ " β:34 => RevLex (Prod α β)

/-- Reverse lexicographic ordering on pairs. -/
instance instLE (α β : Type*) [LE α] [LT β] : LE (α ×ᵣ β) where
  le x y := Prod.RevLex (· ≤ ·) (· < ·) (ofRevLex x) (ofRevLex y)

instance instLT (α β : Type*) [LT α] [LT β] : LT (α ×ᵣ β) where
  lt x y := Prod.RevLex (· < ·) (· < ·) (ofRevLex x) (ofRevLex y)

theorem toRevLex_le_toRevLex [LE α] [LT β] {x y : α × β} :
    toRevLex x ≤ toRevLex y ↔ x.2 < y.2 ∨ x.2 = y.2 ∧ x.1 ≤ y.1 :=
  Prod.revLex_def

theorem toRevLex_lt_toRevLex [LT α] [LT β] {x y : α × β} :
    toRevLex x < toRevLex y ↔ x.2 < y.2 ∨ x.2 = y.2 ∧ x.1 < y.1 :=
  Prod.revLex_def

lemma le_iff [LE α] [LT β] {x y : α ×ᵣ β} :
    x ≤ y ↔ (ofRevLex x).2 < (ofRevLex y).2 ∨ (ofRevLex x).2 =
      (ofRevLex y).2 ∧ (ofRevLex x).1 ≤ (ofRevLex y).1 :=
  Prod.revLex_def

lemma lt_iff [LT α] [LT β] {x y : α ×ᵣ β} :
    x < y ↔ (ofRevLex x).2 < (ofRevLex y).2 ∨ (ofRevLex x).2 =
      (ofRevLex y).2 ∧ (ofRevLex x).1 < (ofRevLex y).1 :=
  Prod.revLex_def

/-- An order equivalence between a lex product and a reverse lex product with inputs switched. -/
def LexEquiv [LT α] [LE β] :
    α ×ₗ β ≃o β ×ᵣ α where
  toFun a := toRevLex ⟨(ofLex a).2, (ofLex a).1⟩
  invFun a := toLex ⟨(ofRevLex a).2, (ofRevLex a).1⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro a b
    simp [le_iff, Lex.le_iff]

theorem LexEquiv_le_iff [LT α] [LE β] (a b : α ×ₗ β) :
    LexEquiv a ≤ LexEquiv b ↔ a ≤ b :=
  OrderIso.le_iff_le LexEquiv

theorem LexEquiv_symm_le [LT α] [LE β] (a b : β ×ᵣ α) :
    LexEquiv.symm a ≤ LexEquiv.symm b ↔ a ≤ b :=
  (OrderIso.le_iff_le LexEquiv).symm

end Prod.RevLex
