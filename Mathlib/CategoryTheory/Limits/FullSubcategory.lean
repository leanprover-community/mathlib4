/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Limits in full subcategories

We introduce the notion of a property closed under taking limits and show that if `P` is closed
under taking limits, then limits in `FullSubcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/


noncomputable section

universe w' w v u

open CategoryTheory

namespace CategoryTheory.Limits

/-- We say that a property is closed under limits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any limit of this diagram also has the property. -/
def ClosedUnderLimitsOfShape {C : Type u} [Category.{v} C] (J : Type w) [Category.{w'} J]
    (P : ObjectProperty C) : Prop :=
  ∀ ⦃F : J ⥤ C⦄ ⦃c : Cone F⦄ (_hc : IsLimit c), (∀ j, P (F.obj j)) → P c.pt

/-- We say that a property is closed under colimits of shape `J` if whenever all objects in a
    `J`-shaped diagram have the property, any colimit of this diagram also has the property. -/
def ClosedUnderColimitsOfShape {C : Type u} [Category.{v} C] (J : Type w) [Category.{w'} J]
    (P : ObjectProperty C) : Prop :=
  ∀ ⦃F : J ⥤ C⦄ ⦃c : Cocone F⦄ (_hc : IsColimit c), (∀ j, P (F.obj j)) → P c.pt

section

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] {P : ObjectProperty C}

theorem closedUnderLimitsOfShape_of_limit [P.IsClosedUnderIsomorphisms]
    (h : ∀ {F : J ⥤ C} [HasLimit F], (∀ j, P (F.obj j)) → P (limit F)) :
    ClosedUnderLimitsOfShape J P := by
  intros F c hc hF
  have : HasLimit F := ⟨_, hc⟩
  exact P.prop_of_iso ((limit.isLimit _).conePointUniqueUpToIso hc) (h hF)

theorem closedUnderColimitsOfShape_of_colimit [P.IsClosedUnderIsomorphisms]
    (h : ∀ {F : J ⥤ C} [HasColimit F], (∀ j, P (F.obj j)) → P (colimit F)) :
    ClosedUnderColimitsOfShape J P := by
  intros F c hc hF
  have : HasColimit F := ⟨_, hc⟩
  exact P.prop_of_iso ((colimit.isColimit _).coconePointUniqueUpToIso hc) (h hF)

theorem ClosedUnderLimitsOfShape.limit (h : ClosedUnderLimitsOfShape J P) {F : J ⥤ C} [HasLimit F] :
    (∀ j, P (F.obj j)) → P (limit F) :=
  h (limit.isLimit _)

theorem ClosedUnderColimitsOfShape.colimit (h : ClosedUnderColimitsOfShape J P) {F : J ⥤ C}
    [HasColimit F] : (∀ j, P (F.obj j)) → P (colimit F) :=
  h (colimit.isColimit _)

end

section

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cone (F ⋙ P.ι)} (hc : IsLimit c) (h : P c.pt) :
    CreatesLimit F P.ι :=
  createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasLimit (F ⋙ P.ι)] (h : P (limit (F ⋙ P.ι))) :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cocone (F ⋙ P.ι)} (hc : IsColimit c) (h : P c.pt) :
    CreatesColimit F P.ι :=
  createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasColimit (F ⋙ P.ι)]
    (h : P (colimit (F ⋙ P.ι))) :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitFullSubcategoryInclusionOfClosed (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion F (h.limit fun j => (F.obj j).property)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J P.ι where
  CreatesLimit := @fun F => createsLimitFullSubcategoryInclusionOfClosed h F

theorem hasLimit_of_closedUnderLimits (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] : HasLimit F :=
  have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed h F
  hasLimit_of_created F P.ι

theorem hasLimitsOfShape_of_closedUnderLimits (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : HasLimitsOfShape J P.FullSubcategory :=
  { has_limit := fun F => hasLimit_of_closedUnderLimits h F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitFullSubcategoryInclusionOfClosed (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion F (h.colimit fun j => (F.obj j).property)

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J P.ι where
  CreatesColimit := @fun F => createsColimitFullSubcategoryInclusionOfClosed h F

theorem hasColimit_of_closedUnderColimits (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : HasColimit F :=
  have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed h F
  hasColimit_of_created F P.ι

theorem hasColimitsOfShape_of_closedUnderColimits (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : HasColimitsOfShape J P.FullSubcategory :=
  { has_colimit := fun F => hasColimit_of_closedUnderColimits h F }

end

end CategoryTheory.Limits
