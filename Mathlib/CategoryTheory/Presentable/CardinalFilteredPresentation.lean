/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Presentable generators

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

structure CardinalFilteredPresentation (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] where
  J : Type w
  category : Category.{w} J := by infer_instance
  isCardinalFiltered : IsCardinalFiltered J κ := by infer_instance
  F : J ⥤ C
  ι : F ⟶ (Functor.const _).obj X
  isColimit : IsColimit (Cocone.mk _ ι)

namespace CardinalFilteredPresentation

attribute [instance] category isCardinalFiltered

variable {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (p : CardinalFilteredPresentation X κ)

lemma isCardinalPresentable_pt (h : ∀ (j : p.J), IsCardinalPresentable (p.F.obj j) κ)
    [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow p.J) κ') :
    IsCardinalPresentable X κ' := by
  have : ∀ (k : p.J), IsCardinalPresentable (p.F.obj k) κ' :=
    fun _ ↦ isCardinalPresentable_of_le _ h
  exact isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end CardinalFilteredPresentation

@[simps J F ι isColimit]
def CardinalFilteredPresentation.ofIsColimit {J : Type w} [Category.{w} J]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] :
    CardinalFilteredPresentation c.pt κ where
  J := J
  F := F
  ι := c.ι
  isColimit := hc

variable {ι : Type w} (G : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

structure AreCardinalFilteredGenerators : Prop where
  nonempty_cardinalFilteredPresentation (X : C) :
      ∃ (p : CardinalFilteredPresentation X κ),
        ∀ (j : p.J), ∃ (i : ι), Nonempty (p.F.obj j ≅ G i)

namespace AreCardinalFilteredGenerators

variable {G κ} (h : AreCardinalFilteredGenerators G κ) (X : C)

noncomputable def presentation : CardinalFilteredPresentation X κ :=
  (h.nonempty_cardinalFilteredPresentation X).choose

lemma exists_presentation_obj_iso (j : (h.presentation X).J) :
    ∃ (i : ι), Nonempty ((h.presentation X).F.obj j ≅ G i) :=
  (h.nonempty_cardinalFilteredPresentation X).choose_spec j

instance (j : (h.presentation X).J) [∀ i, IsCardinalPresentable (G i) κ] :
    IsCardinalPresentable ((h.presentation X).F.obj j) κ := by
  obtain ⟨i, ⟨e⟩⟩ := (h.exists_presentation_obj_iso X j)
  exact isCardinalPresentable_of_iso e.symm κ

include h in
lemma presentable [LocallySmall.{w} C] (X : C) : IsPresentable.{w} X := by
  have := h
  sorry

end AreCardinalFilteredGenerators

end CategoryTheory
