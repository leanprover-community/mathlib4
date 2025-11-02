/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Limits in full subcategories

If a property of objects `P` is closed under taking limits,
then limits in `FullSubcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/


noncomputable section

universe w' w v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

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

variable (P J)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion F (P.prop_limit _ fun j => (F.obj j).property)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
instance createsLimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J P.ι where
  CreatesLimit := @fun F => createsLimitFullSubcategoryInclusionOfClosed J P F

theorem hasLimit_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] : HasLimit F :=
  have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed J P F
  hasLimit_of_created F P.ι

instance hasLimitsOfShape_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : HasLimitsOfShape J P.FullSubcategory :=
  { has_limit := fun F => hasLimit_of_closedUnderLimits J P F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion F (P.prop_colimit _ fun j => (F.obj j).property)

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
instance createsColimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J P.ι where
  CreatesColimit := @fun F => createsColimitFullSubcategoryInclusionOfClosed J P F

theorem hasColimit_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : HasColimit F :=
  have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed J P F
  hasColimit_of_created F P.ι

instance hasColimitsOfShape_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : HasColimitsOfShape J P.FullSubcategory :=
  { has_colimit := fun F => hasColimit_of_closedUnderColimits J P F }

end

variable {J : Type w} [Category.{w'} J]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

/-- The essential image of a functor is closed under the limits it preserves. -/
instance [HasLimitsOfShape J C] [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderLimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨limit (Functor.essImage.liftFunctor G F hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves F (limit.isLimit _)) (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

/-- The essential image of a functor is closed under the colimits it preserves. -/
instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderColimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _)) (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

end CategoryTheory.Limits
