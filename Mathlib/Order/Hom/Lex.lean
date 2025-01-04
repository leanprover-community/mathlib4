/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Sum.Order
import Mathlib.Order.Hom.Set
import Mathlib.Order.RelIso.Set

/-!
# Lexicographic order and order isomorphisms

The main result in this file is the following: if `α` is a linear order and `x : α`, then `α` is
order isomorphic to either of `Iio x ⊕ₗ Ici x` or `Iic x ⊕ₗ Ioi x`.
-/

open Set

variable {α : Type*}

/-! ### Relation isomorphism -/

namespace RelIso

variable {r : α → α → Prop} {x y : α} [IsTrans α r] [IsTrichotomous α r] [DecidableRel r]

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements less than `x` and elements not
less than `x`. -/
-- The explicit type signature stops `simp` from complaining.
def sumLexComplLeft :
    @Sum.Lex {y // r y x} {y // ¬ r y x} (Subrel r {y | r y x}) (Subrel r {y | ¬ r y x}) ≃r r where
  toEquiv := Equiv.sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
    · simpa using fun h ↦ ha <| trans h hb
    · simp

@[simp]
theorem sumLexComplLeft_apply_inl (a : {y // r y x}) : sumLexComplLeft r x (Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexComplLeft_apply_inr (a : {y // ¬ r y x}) : sumLexComplLeft r x (Sum.inr a) = a :=
  rfl

theorem sumLexComplLeft_symm_apply_of_mem (h : r y x) :
    (sumLexComplLeft r x).symm y = Sum.inl ⟨y, h⟩ :=
  Equiv.sumCompl_apply_symm_of_pos (r · x) _ h

theorem sumLexComplLeft_symm_apply_of_not_mem (h : ¬ r y x) :
    (sumLexComplLeft r x).symm y = Sum.inr ⟨y, h⟩ :=
  Equiv.sumCompl_apply_symm_of_neg (r · x) _ h

@[simp]
theorem sumLexComplLeft_symm_apply (a : {y // r y x}) :
    (sumLexComplLeft r x).symm a = Sum.inl a :=
  sumLexComplLeft_symm_apply_of_mem a.2

@[simp]
theorem sumLexComplLeft_symm_apply_neg (a : {y // ¬ r y x}) :
    (sumLexComplLeft r x).symm a = Sum.inr a :=
  sumLexComplLeft_symm_apply_of_not_mem a.2

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements not greater than `x` and elements
greater than `x`. -/
-- The explicit type signature stops `simp` from complaining.
def sumLexComplRight :
    @Sum.Lex {y // ¬ r x y} {y // r x y} (Subrel r {y | ¬ r x y}) (Subrel r {y | r x y}) ≃r r where
  toEquiv := (Equiv.sumComm _ _).trans <| Equiv.sumCompl (r x ·)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
    · simpa using fun h ↦ hb <| trans ha h
    · simp

@[simp]
theorem sumLexComplRight_apply_inl (a : {y // ¬ r x y}) : sumLexComplRight r x (Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexComplRight_apply_inr (a : {y // r x y}) : sumLexComplRight r x (Sum.inr a) = a :=
  rfl

theorem sumLexComplRight_symm_apply_of_mem (h : r x y) :
    (sumLexComplRight r x).symm y = Sum.inr ⟨y, h⟩ := by
  simp [sumLexComplRight, h]

theorem sumLexComplRight_symm_apply_of_not_mem (h : ¬ r x y) :
    (sumLexComplRight r x).symm y = Sum.inl ⟨y, h⟩ := by
  simp [sumLexComplRight, h]

@[simp]
theorem sumLexComplRight_symm_apply (a : {y // r x y}) :
    (sumLexComplRight r x).symm a = Sum.inr a :=
  sumLexComplRight_symm_apply_of_mem a.2

@[simp]
theorem sumLexComplRight_symm_apply_neg (a : {y // ¬ r x y}) :
    (sumLexComplRight r x).symm a = Sum.inl a :=
  sumLexComplRight_symm_apply_of_not_mem a.2

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
theorem sumLexIioIci_apply_inl (a : Iio x) : sumLexIioIci x (Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexIioIci_apply_inr (a : Ici x) : sumLexIioIci x (Sum.inr a) = a :=
  rfl

theorem sumLexIioIci_symm_apply_of_lt (h : y < x) :
    (sumLexIioIci x).symm y = Sum.inl ⟨y, h⟩ := by
  rw [symm_apply_eq, sumLexIioIci_apply_inl]

theorem sumLexIioIci_symm_apply_of_le {y : α} (h : x ≤ y) :
    (sumLexIioIci x).symm y = Sum.inr ⟨y, h⟩ := by
  rw [symm_apply_eq, sumLexIioIci_apply_inr]

@[simp]
theorem sumLexIioIci_symm_apply_Iio (a : Iio x) : (sumLexIioIci x).symm a = Sum.inl a :=
  sumLexIioIci_symm_apply_of_lt a.2

@[simp]
theorem sumLexIioIci_symm_apply_Ici (a : Ici x) : (sumLexIioIci x).symm a = Sum.inr a :=
  sumLexIioIci_symm_apply_of_le a.2

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less or equal to `x` and
elements greater than `x`. -/
def sumLexIicIoi : Iic x ⊕ₗ Ioi x ≃o α :=
  (sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans <|
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]
theorem sumLexIicIoi_apply_inl (a : Iic x) : sumLexIicIoi x (Sum.inl a) = a :=
  rfl

@[simp]
theorem sumLexIicIoi_apply_inr (a : Ioi x) : sumLexIicIoi x (Sum.inr a) = a :=
  rfl

theorem sumLexIicIoi_symm_apply_of_le (h : y ≤ x) :
    (sumLexIicIoi x).symm y = Sum.inl ⟨y, h⟩ := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inl]

theorem sumLexIicIoi_symm_apply_of_lt {y : α} (h : x < y) :
    (sumLexIicIoi x).symm y = Sum.inr ⟨y, h⟩ := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inr]

@[simp]
theorem sumLexIicIoi_symm_apply_Iic (a : Iic x) : (sumLexIicIoi x).symm a = Sum.inl a :=
  sumLexIicIoi_symm_apply_of_le a.2

@[simp]
theorem sumLexIicIoi_symm_apply_Ioi (a : Ioi x) : (sumLexIicIoi x).symm a = Sum.inr a :=
  sumLexIicIoi_symm_apply_of_lt a.2

end OrderIso
