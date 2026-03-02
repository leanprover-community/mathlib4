/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Finally small filtered categories

In this file, we show that if `C` is a filtered finally small category
that is locally small, there exists a final functor `D ⥤ C` from
a small filtered category. The dual result is also obtained.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace FinallySmall

attribute [local instance] IsFiltered.nonempty

open IsFiltered

variable [IsFiltered C] [LocallySmall.{w} C] [FinallySmall.{w} C]

lemma exists_of_isFiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  /- First, under the assumption `Category.{w}` (instead of `LocallySmall.{w}`),
  we get most of the conclusion but instead of `D : Type w`,
  we only get a `w`-small `D : Type u`. -/
  have (C₀ : Type u) [Category.{w} C₀] [IsFiltered C₀] [FinallySmall.{w} C₀] :
      ∃ (D : Type u) (_ : Small.{w} D) (_ : Category.{w} D) (_ : IsFiltered D) (F : D ⥤ C₀),
        F.Final := by
    /- For `D`, we can choose the full subcategory of `C₀` which is the strict image
    of the final functor `fromFinalModel.{w} C₀ : FinalModel.{w} C₀ ⥤ C₀`,
    where `FinalModel.{w} C₀` is a `w`-small category. -/
    let P : ObjectProperty C₀ := ObjectProperty.strictMap ⊤ (fromFinalModel.{w} C₀)
    have hP (X : C₀) : ∃ (Y : C₀) (hY : P Y), Nonempty (X ⟶ Y) := by
      let f : StructuredArrow X (fromFinalModel.{w} C₀) := Classical.arbitrary _
      exact ⟨_, ObjectProperty.strictMap_obj _ _ (X := f.right) (by tauto), ⟨f.hom⟩⟩
    have : IsFiltered P.FullSubcategory :=
      { nonempty := by
          obtain ⟨X, hX, _⟩ := hP (Classical.arbitrary C₀)
          exact ⟨X, hX⟩
        cocone_objs := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩
          obtain ⟨Z, hZ, ⟨f⟩⟩ := hP (max X Y)
          exact ⟨⟨Z, hZ⟩, (leftToMax X Y ≫ f :),
            (rightToMax X Y ≫ f :), by tauto⟩
        cocone_maps := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩ (f₁ : X ⟶ Y) (f₂ : X ⟶ Y)
          obtain ⟨Z, hZ, ⟨g⟩⟩ := hP (coeq f₁ f₂)
          exact ⟨⟨Z, hZ⟩, (coeqHom f₁ f₂ ≫ g :), coeq_condition_assoc _ _ _⟩ }
    let G : FinalModel.{w} C₀ ⥤ P.FullSubcategory :=
      { obj X := ⟨(fromFinalModel.{w} C₀).obj X, by tauto⟩
        map f := (fromFinalModel.{w} C₀).map f }
    have : (G ⋙ P.ι).Final := inferInstanceAs (fromFinalModel.{w} C₀).Final
    exact ⟨P.FullSubcategory, small_of_surjective (f := G.obj)
      (by rintro ⟨_, Y, _, rfl⟩; exact ⟨Y, rfl⟩), inferInstance, inferInstance, P.ι,
      Functor.final_of_comp_full_faithful' G P.ι ⟩
  /- We get the conclusion under the assumption `Category.{w}`
  (instead of `LocallySmall.{w}`). -/
  have (C₀ : Type u) [Category.{w} C₀] (_ : IsFiltered C₀) (_ : FinallySmall.{w} C₀) :
      ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C₀), F.Final := by
    obtain ⟨D, _, _, _, F, _⟩ := this C₀
    let e := equivSmallModel.{w} D
    exact ⟨_, _, of_equivalence e, e.inverse ⋙ F, inferInstance⟩
  /- To get the conclusion for the given category `C`, it suffices to apply
  the previous result to the category `ShrinkHoms C`. -/
  let e := ShrinkHoms.equivalence.{w} C
  obtain ⟨D, _, _, F, _⟩ := this (ShrinkHoms C)
    (of_equivalence e) (finallySmall_of_final_of_finallySmall e.functor)
  exact ⟨D, inferInstance, inferInstance, F ⋙ e.inverse, inferInstance⟩

/-- If `C` is a locally small filtered finally small category,
this is a small filtered category, equipped with a final functor to `C`
(see `fromFilteredFinalModel`). -/
def FilteredFinalModel : Type w := (exists_of_isFiltered.{w} C).choose

noncomputable instance : Category (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose

instance : IsFiltered (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small filtered finally small category,
this is a final functor from a small filtered category. -/
noncomputable def fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose

instance : (fromFilteredFinalModel.{w} C).Final :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

end FinallySmall

namespace InitiallySmall

variable [IsCofiltered C] [LocallySmall.{w} C] [InitiallySmall.{w} C]

lemma exists_of_isCofiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C), F.Initial := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Cᵒᵖ
  exact ⟨Dᵒᵖ, inferInstance, inferInstance, F.leftOp, inferInstance⟩

/-- If `C` is a locally small cofiltered initially small category,
this is a small cofiltered category, equipped with an initial functor to `C`
(see `fromCofilteredInitialModel`). -/
def CofilteredInitialModel : Type w := (exists_of_isCofiltered.{w} C).choose

noncomputable instance : Category (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose

instance : IsCofiltered (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small cofiltered initially small category,
this is an initial functor from a small cofiltered category. -/
noncomputable def fromCofilteredInitialModel : CofilteredInitialModel.{w} C ⥤ C :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose

instance : (fromCofilteredInitialModel.{w} C).Initial :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

end InitiallySmall

end CategoryTheory
