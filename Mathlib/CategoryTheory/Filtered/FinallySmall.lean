/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Finally small filtered categories

We introduce a typeclass `FinallySmallFiltered.{w} C` saying that
there exists a final functor `S ⥤ C` where `S` is a `w`-small filtered category.
We show that if `C` is a filtered finally small category that is locally small,
then it satisfies `FinallySmallFiltered.{w} C`. The dual result is also obtained.

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Functor

/-- A category is `FinallySmallFiltered.{w}` if there is a final functor
from a filtered `w`-small category. -/
class FinallySmallFiltered (C : Type u) [Category.{v} C] : Prop where
  /-- There is a final functor from a small filtered category. -/
  final_smallCategory (C) : ∃ (S : Type w) (_ : SmallCategory S)
    (_ : IsFiltered S) (F : S ⥤ C), F.Final

/-- A category is `InitiallySmallCofiltered.{w}` if there is an initial functor
from a cofiltered `w`-small category. -/
class InitiallySmallCofiltered (C : Type u) [Category.{v} C] : Prop where
  /-- There is an initial functor from a small cofiltered category. -/
  initial_smallCategory (C) : ∃ (S : Type w) (_ : SmallCategory S)
    (_ : IsCofiltered S) (F : S ⥤ C), F.Initial

variable (C : Type u) [Category.{v} C]

section

variable [FinallySmallFiltered.{w} C]

/-- If a category `C` satisfies `FinallySmallFiltered.{w} C`, this is
a `w`-small filtered category equipped with a final functor
`fromFilteredFinalModel C`. -/
def FilteredFinalModel : Type w :=
  (FinallySmallFiltered.final_smallCategory C).choose

noncomputable instance : SmallCategory (FilteredFinalModel.{w} C) :=
  (FinallySmallFiltered.final_smallCategory C).choose_spec.choose

noncomputable instance : IsFiltered (FilteredFinalModel.{w} C) :=
  (FinallySmallFiltered.final_smallCategory C).choose_spec.choose_spec.choose

/-- If a category `C` satisfies `FinallySmallFiltered.{w} C`, this is
a final functor `FilteredFinalModel.{w} C ⥤ C` from a `w`-small filtered category. -/
noncomputable def fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C :=
  (FinallySmallFiltered.final_smallCategory C).choose_spec.choose_spec.choose_spec.choose

instance : (fromFilteredFinalModel.{w} C).Final :=
  (FinallySmallFiltered.final_smallCategory C).choose_spec.choose_spec.choose_spec.choose_spec

instance : FinallySmall.{w} C :=
  finallySmall_of_final_of_essentiallySmall (fromFilteredFinalModel.{w} C)

@[deprecated (since := "2026-02-21")]
alias FinallySmall.FilteredFinalModel := FilteredFinalModel
@[deprecated (since := "2026-02-21")]
alias FinallySmall.fromFilteredFinalModel := fromFilteredFinalModel

end

section

variable [InitiallySmallCofiltered.{w} C]

/-- If a category `C` satisfies `InitiallySmallCofiltered.{w} C`, this is
a `w`-small cofiltered category equipped with an initial functor
`fromCofilteredInitialModel C`. -/
def CofilteredInitialModel : Type w :=
  (InitiallySmallCofiltered.initial_smallCategory C).choose

noncomputable instance : Category (CofilteredInitialModel.{w} C) :=
  (InitiallySmallCofiltered.initial_smallCategory C).choose_spec.choose

noncomputable instance : IsCofiltered (CofilteredInitialModel.{w} C) :=
  (InitiallySmallCofiltered.initial_smallCategory C).choose_spec.choose_spec.choose

/-- If a category `C` satisfies `InitiallySmallCofiltered.{w} C`, this is
an initial functor `FilteredFinalModel.{w} C ⥤ C` from a `w`-small filtered category. -/
noncomputable def fromCofilteredInitialModel : CofilteredInitialModel.{w} C ⥤ C :=
  (InitiallySmallCofiltered.initial_smallCategory C).choose_spec.choose_spec.choose_spec.choose

instance : (fromCofilteredInitialModel.{w} C).Initial :=
  (InitiallySmallCofiltered.initial_smallCategory C).choose_spec.choose_spec.choose_spec.choose_spec

instance : InitiallySmall.{w} C :=
  initiallySmall_of_initial_of_essentiallySmall (fromCofilteredInitialModel.{w} C)

@[deprecated (since := "2026-02-21")]
alias InitiallySmall.CofilteredInitialModel := CofilteredInitialModel
@[deprecated (since := "2026-02-21")]
alias InitiallySmall.fromCofilteredInitialModel := fromCofilteredInitialModel

end

variable {C} in
lemma finallySmallFiltered_of_final {C₀ : Type*} [Category* C₀] (F : C₀ ⥤ C)
    [IsFiltered C₀] [EssentiallySmall.{w} C₀] [F.Final] :
    FinallySmallFiltered.{w} C where
  final_smallCategory :=
    ⟨_, inferInstance, IsFiltered.of_equivalence (equivSmallModel.{w} C₀),
      (equivSmallModel.{w} C₀).inverse ⋙ F, inferInstance⟩

variable {C} in
lemma initiallySmallCofiltered_of_initial {C₀ : Type*} [Category* C₀] (F : C₀ ⥤ C)
    [IsCofiltered C₀] [EssentiallySmall.{w} C₀] [F.Initial] :
    InitiallySmallCofiltered.{w} C where
  initial_smallCategory :=
    ⟨_, inferInstance, IsCofiltered.of_equivalence (equivSmallModel.{w} C₀),
      (equivSmallModel.{w} C₀).inverse ⋙ F, inferInstance⟩


instance [InitiallySmallCofiltered.{w} C] :
    FinallySmallFiltered.{w} Cᵒᵖ :=
  finallySmallFiltered_of_final (fromCofilteredInitialModel.{w} C).op

instance [FinallySmallFiltered.{w} C] :
    InitiallySmallCofiltered.{w} Cᵒᵖ :=
  initiallySmallCofiltered_of_initial (fromFilteredFinalModel.{w} C).op

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
          exact ⟨⟨Z, hZ⟩, ObjectProperty.homMk (leftToMax X Y ≫ f),
            ObjectProperty.homMk (rightToMax X Y ≫ f), by tauto⟩
        cocone_maps := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩ ⟨f₁ : X ⟶ Y⟩ ⟨f₂ : X ⟶ Y⟩
          obtain ⟨Z, hZ, ⟨g⟩⟩ := hP (coeq f₁ f₂)
          exact ⟨⟨Z, hZ⟩, ObjectProperty.homMk (coeqHom f₁ f₂ ≫ g),
            ObjectProperty.hom_ext _ (coeq_condition_assoc _ _ _) ⟩ }
    let G : FinalModel.{w} C₀ ⥤ P.FullSubcategory :=
      { obj X := ⟨(fromFinalModel.{w} C₀).obj X, by tauto⟩
        map f := ObjectProperty.homMk ((fromFinalModel.{w} C₀).map f) }
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

instance : FinallySmallFiltered.{w} C where
  final_smallCategory := exists_of_isFiltered C

end FinallySmall

namespace InitiallySmall

variable [IsCofiltered C] [LocallySmall.{w} C] [InitiallySmall.{w} C]

lemma exists_of_isCofiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C), F.Initial := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Cᵒᵖ
  exact ⟨Dᵒᵖ, inferInstance, inferInstance, F.leftOp, inferInstance⟩

instance : InitiallySmallCofiltered.{w} C where
  initial_smallCategory := exists_of_isCofiltered C

end InitiallySmall

end CategoryTheory
