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


namespace exists_of_isFiltered

lemma aux₁ [FinallySmall.{w} C] [IsFiltered C] :
    ∃ (D : Type w) (_ : Category.{v} D) (_ : IsFiltered D) (_ : FinallySmall.{w} D)
    (F : D ⥤ C), F.Final := by
  let P : ObjectProperty C := Set.range (fromFinalModel C).obj
  sorry

lemma aux₂ (C : Type w) [Category.{v} C] [FinallySmall.{w} C] [IsFiltered C] :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  sorry

end exists_of_isFiltered

variable [IsFiltered C] [FinallySmall.{w} C]

open exists_of_isFiltered in
lemma exists_of_isFiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  obtain ⟨D, _, _, _, F, _⟩  := aux₁.{w} C
  obtain ⟨E, _, _, G, _⟩  := aux₂.{w} D
  exact ⟨E, inferInstance, inferInstance, G ⋙ F, inferInstance⟩

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
