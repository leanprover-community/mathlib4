/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Order.CompleteLattice.Basic

/-!
# ObjectProperty is a complete lattice

-/

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

example : CompleteLattice (ObjectProperty C) := inferInstance

section

variable (P Q : ObjectProperty C) (X : C)

@[simp high] lemma prop_inf_iff : (P ⊓ Q) X ↔ P X ∧ Q X := Iff.rfl

@[simp high] lemma prop_sup_iff : (P ⊔ Q) X ↔ P X ∨ Q X := Iff.rfl

lemma isoClosure_sup : (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure := by
  ext X
  simp only [prop_sup_iff]
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_sup_iff] at hY
    obtain hY | hY := hY
    · exact Or.inl ⟨Y, hY, ⟨e⟩⟩
    · exact Or.inr ⟨Y, hY, ⟨e⟩⟩
  · rintro (hY | hY)
    · exact monotone_isoClosure le_sup_left _ hY
    · exact monotone_isoClosure le_sup_right _ hY

instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (P ⊔ Q).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_sup, isoClosure_eq_self]

end

section

variable {α : Sort*} (P : α → ObjectProperty C) (X : C)

@[simp high] lemma prop_iSup_iff :
    (⨆ (a : α), P a) X ↔ ∃ (a : α), P a X := by simp

lemma isoClosure_iSup :
    ((⨆ (a : α), P a)).isoClosure = ⨆ (a : α), (P a).isoClosure := by
  refine le_antisymm ?_ ?_
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hY ⊢
    obtain ⟨a, hY⟩ := hY
    exact ⟨a, _, hY, ⟨e⟩⟩
  · simp only [iSup_le_iff]
    intro a
    rw [isoClosure_le_iff]
    exact (le_iSup P a).trans (le_isoClosure _)

instance [∀ a, (P a).IsClosedUnderIsomorphisms] :
    ((⨆ (a : α), P a)).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self,
    isoClosure_iSup, isoClosure_eq_self]

end

end CategoryTheory.ObjectProperty
