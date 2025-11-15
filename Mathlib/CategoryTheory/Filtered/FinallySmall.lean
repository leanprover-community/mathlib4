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
  let e := ShrinkHoms.equivalence.{w} C
  sorry

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
