/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.CompleteLattice.Basic

/-!
# ObjectProperty is a complete lattice

-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

example : CompleteLattice (ObjectProperty C) := inferInstance

section

variable (P Q : ObjectProperty C) (X : C)

@[simp high] lemma prop_inf_iff : (P ⊓ Q) X ↔ P X ∧ Q X := Iff.rfl

@[simp high] lemma prop_sup_iff : (P ⊔ Q) X ↔ P X ∨ Q X := Iff.rfl

instance nonempty_sup_left [P.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inl P.prop_arbitrary)

instance nonempty_sup_right [Q.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inr Q.prop_arbitrary)

instance nonempty_top [Nonempty C] : (⊤ : ObjectProperty C).Nonempty :=
  nonempty_of_prop (X := Classical.arbitrary C) (by trivial)

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

instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P ⊓ Q) where
  of_iso e h := ⟨IsClosedUnderIsomorphisms.of_iso e h.1, IsClosedUnderIsomorphisms.of_iso e h.2⟩

instance : IsClosedUnderIsomorphisms (⊥ : ObjectProperty C) where
  of_iso _ h := h

instance : IsClosedUnderIsomorphisms (⊤ : ObjectProperty C) where
  of_iso := by simp

end

section

variable {α : Sort*} (P : α → ObjectProperty C) (X : C)

@[simp high] lemma prop_iSup_iff :
    (⨆ (a : α), P a) X ↔ ∃ (a : α), P a X := by simp

lemma nonempty_iSup (a : α) [(P a).Nonempty] : (⨆ a, P a).Nonempty :=
  nonempty_of_prop ((prop_iSup_iff P _).mpr ⟨a, (P a).prop_arbitrary⟩)

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

@[push]
lemma ne_bot_iff_exists (P : ObjectProperty C) : ¬ P = ⊥ ↔ ∃ X, P X := by
  simp [← le_bot_iff, not_le_iff_exists]

lemma nonempty_iff_ne_bot (P : ObjectProperty C) : P.Nonempty ↔ ¬ P = ⊥ := by
  rw [ne_bot_iff_exists, nonempty_iff]

@[push]
lemma not_nonempty_iff_eq_bot (P : ObjectProperty C) : ¬ P.Nonempty ↔ P = ⊥ := by
  rw [P.nonempty_iff_ne_bot, not_not]

@[simp]
lemma ι_map_top (P : ObjectProperty C) :
    (⊤ : ObjectProperty _).map P.ι = P.isoClosure := by
  ext X
  constructor
  · rintro ⟨⟨Y, hY⟩, _, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, by simp, ⟨e.symm⟩⟩

end CategoryTheory.ObjectProperty
