/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Finally small filtered categories
-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace FinallySmall

lemma exists_of_isFiltered [IsFiltered C] [LocallySmall.{w} C] [FinallySmall.{w} C] :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  have : ∀ (C₀ : Type u) (_ : Category.{w} C₀) ( _ : IsFiltered C₀)
      (_ : FinallySmall.{w} C₀),
      ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C₀), F.Final := by
    intro C₀ _ _ _
    obtain ⟨(P : ObjectProperty C₀), h₁, h₂⟩ :=
      FinallySmall.exists_small_weakly_terminal_set.{w} C₀
    have : Nonempty C₀ := IsFiltered.nonempty
    have : IsFiltered P.FullSubcategory :=
      { nonempty := by
          obtain ⟨X, hX, _⟩ := h₂ (Classical.arbitrary C₀)
          exact ⟨⟨X, hX⟩⟩
        cocone_objs := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩
          obtain ⟨Z, hZ, ⟨f⟩⟩ := h₂ (IsFiltered.max X Y)
          exact ⟨⟨Z, hZ⟩, (IsFiltered.leftToMax X Y ≫ f :),
            (IsFiltered.rightToMax X Y ≫ f :), by tauto⟩
        cocone_maps := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩ (f₁ : X ⟶ Y) (f₂ : X ⟶ Y)
          obtain ⟨Z, hZ, ⟨g⟩⟩ := h₂ (IsFiltered.coeq f₁ f₂)
          exact ⟨⟨Z, hZ⟩, (IsFiltered.coeqHom f₁ f₂ ≫ g :),
            IsFiltered.coeq_condition_assoc _ _ _⟩}
    have : ObjectProperty.Small.{w} P := h₁
    have : P.ι.Final := by
      rw [Functor.final_iff_of_isFiltered]
      constructor
      · intro X₀
        obtain ⟨Y, hY, ⟨f⟩⟩ := h₂ X₀
        exact ⟨⟨Y, hY⟩, ⟨f⟩⟩
      · intro X₀ ⟨Y, hY⟩ f₁ f₂
        obtain ⟨Z, hZ, ⟨g⟩⟩ := h₂ (IsFiltered.coeq f₁ f₂)
        exact ⟨⟨Z, hZ⟩, (IsFiltered.coeqHom f₁ f₂ ≫ g :),
          IsFiltered.coeq_condition_assoc _ _ _⟩
    let e := equivSmallModel.{w} P.FullSubcategory
    exact ⟨SmallModel.{w} P.FullSubcategory, inferInstance,
      IsFiltered.of_equivalence e,
      e.inverse ⋙ P.ι, inferInstance⟩
  let e := ShrinkHoms.equivalence.{w} C
  obtain ⟨D, _, _, F, _⟩ := this (ShrinkHoms.{u} C) inferInstance
    (IsFiltered.of_equivalence e) (finallySmall_of_final_of_finallySmall e.functor)
  exact ⟨D, inferInstance, inferInstance, F ⋙ e.inverse, inferInstance⟩

variable [IsFiltered C] [LocallySmall.{w} C] [FinallySmall.{w} C]

def FilteredFinalModel : Type w := (exists_of_isFiltered.{w} C).choose

noncomputable instance : Category (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose

instance : IsFiltered (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose

noncomputable def fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose

instance : (fromFilteredFinalModel.{w} C).Final :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

end FinallySmall

end CategoryTheory
