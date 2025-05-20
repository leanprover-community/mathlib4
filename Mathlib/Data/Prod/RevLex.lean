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

* `Prod.revLex.<pre/partial/linear>Order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ᵣ β`: `RevLex α × β`, equipped with the reverse lexicographic order

## TODO

Linear order, well-order?

-/

variable {α β : Type*}

/-- A one-field structure as a type synonym to equip a type with its reverse lexicographic order. -/
structure RevLex (α : Type*) where
/-- The underlying object -/
  obj : α

/-- `toRevLex` is the identity function to the `Lex` of a type. -/
--@[match_pattern]
def toRevLex : α ≃ RevLex α where
  toFun a := ⟨ a ⟩
  invFun a := a.obj
  left_inv := congrFun rfl
  right_inv := congrFun rfl

/-- `ofRevLex` is the identity function from the `Lex` of a type. -/
--@[match_pattern]
def ofRevLex : RevLex α ≃ α :=
  toRevLex.symm

theorem obj_eq_ofRevLex (a : RevLex α) : a.obj = ofRevLex a := rfl

theorem obj_eq_toRevLex (a : α) : {obj := a} = toRevLex a := rfl

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

section
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

end

namespace RevLex

open Batteries

@[inherit_doc] notation:35 α " ×ᵣ " β:34 => RevLex (Prod α β)

@[simp]
theorem Lex_swap_iff {r : α → α → Prop} {s : β → β → Prop} {x y : α × β} :
    Prod.Lex s r (Prod.swap x) (Prod.swap y) ↔ Prod.RevLex r s x y := by
  constructor <;> intro h <;> simpa [revLex_def, lex_iff] using h

@[simp]
theorem swap_iff_Lex {r : α → α → Prop} {s : β → β → Prop} {x y : α × β} :
    Prod.RevLex s r (Prod.swap x) (Prod.swap y) ↔ Prod.Lex r s x y := by
  constructor <;> intro h <;> simpa [revLex_def, lex_def] using h

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

instance preorder (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ᵣ β) where
  le_refl x := by simp [le_iff]
  le_trans x y z hxy hyz := by
    simp only [ge_iff_le, le_iff] at *
    obtain h | ⟨h₁, h₂⟩ := hxy
    · obtain h' | ⟨h₃, h₄⟩ := hyz
      · exact Or.inl <| gt_trans h' h
      · exact Or.inl <| lt_of_lt_of_eq h h₃
    · obtain h' | ⟨h₃, h₄⟩ := hyz
      · exact Or.inl <| lt_of_eq_of_lt h₁ h'
      · exact Or.inr <|
          ⟨h₁.trans h₃, Preorder.le_trans (ofRevLex x).1 (ofRevLex y).1 (ofRevLex z).1 h₂ h₄⟩
  lt_iff_le_not_le x y := by
    simp only [gt_iff_lt, lt_iff, ge_iff_le, le_iff, not_or, not_and]
    constructor
    · intro hxy
      obtain h | ⟨h₁, h₂⟩ := hxy
      · exact ⟨Or.inl h, ⟨not_lt_of_gt h, fun he ↦ ((ne_of_lt h) he.symm).elim⟩⟩
      · exact ⟨Or.inr <| ⟨h₁, le_of_lt h₂⟩, ⟨by simp [h₁, gt_irrefl], fun _ ↦ not_le_of_lt h₂⟩⟩
    · intro h
      obtain ⟨h₁ | ⟨h₂, h₃⟩, ⟨h₄, h₅⟩⟩ := h
      · exact Or.inl h₁
      · exact Or.inr ⟨h₂, lt_of_le_not_le h₃ (h₅ h₂.symm)⟩

/-- Reverse lexicographic partial order for pairs. -/
instance partialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] : PartialOrder (α ×ᵣ β) where
  le_antisymm x y hxy hyx := by
    simp only [ge_iff_le, le_iff] at hxy hyx
    obtain h | ⟨h₁, h₂⟩ := hxy
    · obtain h' | ⟨h₃, h₄⟩ := hyx
      · exact (not_lt_of_gt h' h).elim
      · exact (ne_of_lt h h₃.symm).elim
    · obtain h' | ⟨h₃, h₄⟩ := hyx
      · exact (ne_of_lt h' h₁.symm).elim
      · exact ofRevLex_inj.mp <| Prod.ext_iff.mpr ⟨le_antisymm h₂ h₄, h₁⟩

/-- An order equivalence between a lex product and a reverse lex product with inputs switched. -/
def lexEquiv (α β : Type*) [PartialOrder α] [PartialOrder β] : α ×ₗ β ≃o β ×ᵣ α where
  toFun a := toRevLex ⟨(ofLex a).2, (ofLex a).1⟩
  invFun a := toLex ⟨(ofRevLex a).2, (ofRevLex a).1⟩
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_rel_iff' := by
    intro a b
    simp [le_iff, Lex.le_iff]

theorem LexEquiv_le (α β : Type*) [PartialOrder α] [PartialOrder β] (a b : α ×ₗ β) :
    lexEquiv α β a ≤ lexEquiv α β b ↔ a ≤ b :=
  OrderIso.le_iff_le (lexEquiv α β)

theorem LexEquiv_symm_le (α β : Type*) [PartialOrder α] [PartialOrder β] (a b : β ×ᵣ α) :
    (lexEquiv α β).symm a ≤ (lexEquiv α β).symm b ↔ a ≤ b :=
  (OrderIso.le_iff_le (lexEquiv α β)).symm

instance linearOrder (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ᵣ β) where
  le_total x y := by
    rw [← LexEquiv_symm_le, ← LexEquiv_symm_le]
    exact LinearOrder.le_total ((lexEquiv β α).symm x) ((lexEquiv β α).symm y)
  toDecidableLE x y := by
    rw [← LexEquiv_symm_le]
    exact Lex.instDecidableRelOfDecidableEq ((lexEquiv β α).symm x) ((lexEquiv β α).symm y)

end Prod.RevLex
