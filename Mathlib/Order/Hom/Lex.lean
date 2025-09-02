/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Order.Hom.Set
import Mathlib.Order.RelIso.Set

/-!
# Lexicographic order and order isomorphisms

## Main declarations

* `OrderIso.sumLexIioIci` and `OrderIso.sumLexIicIoi`: if `α` is a linear order and `x : α`,
  then `α` is order isomorphic to both `Iio x ⊕ₗ Ici x` and `Iic x ⊕ₗ Ioi x`.
* `Prod.Lex.prodUnique` and `Prod.Lex.uniqueProd`: `α ×ₗ β` is order isomorphic to one side if the
  other side is `Unique`.
-/

open Set

variable {α : Type*}

/-! ### Relation isomorphism -/

namespace RelIso

variable {r : α → α → Prop} {x y : α} [IsTrans α r] [IsTrichotomous α r] [DecidableRel r]

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements less than `x` and elements not
less than `x`. -/
def sumLexComplLeft : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  toEquiv := .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
    · simpa using fun h ↦ ha <| trans h hb
    · simp

@[simp]
theorem sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

@[simp]
theorem sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements not greater than `x` and elements
greater than `x`. -/
def sumLexComplRight : Sum.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r where
  toEquiv := (Equiv.sumComm _ _).trans <| .sumCompl (r x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
    · simpa using fun h ↦ hb <| trans ha h
    · simp

@[simp]
theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

@[simp]
theorem sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

end RelIso

/-! ### Order isomorphism -/

namespace OrderIso

variable [LinearOrder α] {x y : α}

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less than `x` and elements
greater or equal to `x`. -/
def sumLexIioIci : Iio x ⊕ₗ Ici x ≃o α :=
  (sumLexCongr (refl _) (setCongr (Ici x) {y | ¬ y < x} (by ext; simp))).trans <|
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

@[simp]
theorem sumLexIioIci_apply_inl (a : Iio x) : sumLexIioIci x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexIioIci_apply_inr (a : Ici x) : sumLexIioIci x (toLex <| Sum.inr a) = a :=
  rfl

theorem sumLexIioIci_symm_apply_of_lt (h : y < x) :
    (sumLexIioIci x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIioIci_apply_inl]

theorem sumLexIioIci_symm_apply_of_ge {y : α} (h : x ≤ y) :
    (sumLexIioIci x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIioIci_apply_inr]

@[simp]
theorem sumLexIioIci_symm_apply_Iio (a : Iio x) : (sumLexIioIci x).symm a = toLex (Sum.inl a) :=
  sumLexIioIci_symm_apply_of_lt a.2

@[simp]
theorem sumLexIioIci_symm_apply_Ici (a : Ici x) : (sumLexIioIci x).symm a = toLex (Sum.inr a) :=
  sumLexIioIci_symm_apply_of_ge a.2

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less or equal to `x` and
elements greater than `x`. -/
def sumLexIicIoi : Iic x ⊕ₗ Ioi x ≃o α :=
  (sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans <|
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]
theorem sumLexIicIoi_apply_inl (a : Iic x) : sumLexIicIoi x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexIicIoi_apply_inr (a : Ioi x) : sumLexIicIoi x (toLex <| Sum.inr a) = a :=
  rfl

theorem sumLexIicIoi_symm_apply_of_le (h : y ≤ x) :
    (sumLexIicIoi x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inl]

theorem sumLexIicIoi_symm_apply_of_lt {y : α} (h : x < y) :
    (sumLexIicIoi x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inr]

@[simp]
theorem sumLexIicIoi_symm_apply_Iic (a : Iic x) : (sumLexIicIoi x).symm a = Sum.inl a :=
  sumLexIicIoi_symm_apply_of_le a.2

@[simp]
theorem sumLexIicIoi_symm_apply_Ioi (a : Ioi x) : (sumLexIicIoi x).symm a = Sum.inr a :=
  sumLexIicIoi_symm_apply_of_lt a.2

end OrderIso

/-! ### Degenerate products -/

namespace Prod.Lex
variable (α β : Type*)

/-- Lexicographic product type with `Unique` type on the right is `OrderIso` to the left. -/
def prodUnique [PartialOrder α] [Preorder β] [Unique β] : α ×ₗ β ≃o α where
  toFun x := (ofLex x).1
  invFun x := toLex (x, default)
  left_inv x := x.rec fun (a, b) ↦ by simpa using Unique.default_eq b
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a ↦ b.rec fun b ↦ by
    simpa [Prod.Lex.toLex_le_toLex] using le_iff_lt_or_eq

variable {α β} in
@[simp]
theorem prodUnique_apply [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β) :
    prodUnique α β x = (ofLex x).1 := rfl

/-- Lexicographic product type with `Unique` type on the left is `OrderIso` to the right. -/
def uniqueProd [Preorder α] [Unique α] [LE β] : α ×ₗ β ≃o β where
  toFun x := (ofLex x).2
  invFun x := toLex (default, x)
  left_inv x := x.rec fun (a, b) ↦ by simpa using Unique.default_eq a
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a ↦ b.rec fun b ↦ by
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    simp [Prod.Lex.toLex_le_toLex, heq]

variable {α β} in
@[simp]
theorem uniqueProd_apply [Preorder α] [Unique α] [LE β] (x : α ×ₗ β) :
    uniqueProd α β x = (ofLex x).2 := rfl

end Prod.Lex
