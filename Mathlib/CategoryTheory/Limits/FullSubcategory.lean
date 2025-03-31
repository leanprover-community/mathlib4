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

universe w' w v v₁ v₂ u u₁ u₂

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

protected lemma ClosedUnderLimitsOfShape.limit (h : ClosedUnderLimitsOfShape J P) {F : J ⥤ C}
    [HasLimit F] : (∀ j, P (F.obj j)) → P (limit F) :=
  h (limit.isLimit _)

protected lemma ClosedUnderColimitsOfShape.colimit (h : ClosedUnderColimitsOfShape J P) {F : J ⥤ C}
    [HasColimit F] : (∀ j, P (F.obj j)) → P (colimit F) :=
  h (colimit.isColimit _)

end

section

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {P : C → Prop}

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion' (F : J ⥤ FullSubcategory P)
    {c : Cone (F ⋙ fullSubcategoryInclusion P)} (hc : IsLimit c) (h : P c.pt) :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
def createsLimitFullSubcategoryInclusion (F : J ⥤ FullSubcategory P)
    [HasLimit (F ⋙ fullSubcategoryInclusion P)] (h : P (limit (F ⋙ fullSubcategoryInclusion P))) :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion' (F : J ⥤ FullSubcategory P)
    {c : Cocone (F ⋙ fullSubcategoryInclusion P)} (hc : IsColimit c) (h : P c.pt) :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
def createsColimitFullSubcategoryInclusion (F : J ⥤ FullSubcategory P)
    [HasColimit (F ⋙ fullSubcategoryInclusion P)]
    (h : P (colimit (F ⋙ fullSubcategoryInclusion P))) :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitFullSubcategoryInclusionOfClosed (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasLimit (F ⋙ fullSubcategoryInclusion P)] :
    CreatesLimit F (fullSubcategoryInclusion P) :=
  createsLimitFullSubcategoryInclusion F (h.limit fun j => (F.obj j).property)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
def createsLimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J (fullSubcategoryInclusion P) where
  CreatesLimit := @fun F => createsLimitFullSubcategoryInclusionOfClosed h F

theorem hasLimit_of_closedUnderLimits (h : ClosedUnderLimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasLimit (F ⋙ fullSubcategoryInclusion P)] : HasLimit F :=
  have : CreatesLimit F (fullSubcategoryInclusion P) :=
    createsLimitFullSubcategoryInclusionOfClosed h F
  hasLimit_of_created F (fullSubcategoryInclusion P)

theorem hasLimitsOfShape_of_closedUnderLimits (h : ClosedUnderLimitsOfShape J P)
    [HasLimitsOfShape J C] : HasLimitsOfShape J (FullSubcategory P) :=
  { has_limit := fun F => hasLimit_of_closedUnderLimits h F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitFullSubcategoryInclusionOfClosed (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasColimit (F ⋙ fullSubcategoryInclusion P)] :
    CreatesColimit F (fullSubcategoryInclusion P) :=
  createsColimitFullSubcategoryInclusion F (h.colimit fun j => (F.obj j).property)

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
def createsColimitsOfShapeFullSubcategoryInclusion (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J (fullSubcategoryInclusion P) where
  CreatesColimit := @fun F => createsColimitFullSubcategoryInclusionOfClosed h F

theorem hasColimit_of_closedUnderColimits (h : ClosedUnderColimitsOfShape J P)
    (F : J ⥤ FullSubcategory P) [HasColimit (F ⋙ fullSubcategoryInclusion P)] : HasColimit F :=
  have : CreatesColimit F (fullSubcategoryInclusion P) :=
    createsColimitFullSubcategoryInclusionOfClosed h F
  hasColimit_of_created F (fullSubcategoryInclusion P)

theorem hasColimitsOfShape_of_closedUnderColimits (h : ClosedUnderColimitsOfShape J P)
    [HasColimitsOfShape J C] : HasColimitsOfShape J (FullSubcategory P) :=
  { has_colimit := fun F => hasColimit_of_closedUnderColimits h F }

end

variable {J : Type w} [Category.{w'} J]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

/-- The essential image of a functor is closed under the limits it preserves. -/
protected lemma ClosedUnderLimitsOfShape.essImage [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] : ClosedUnderLimitsOfShape J F.essImage := by
  rintro G c hc hG
  choose Hobj e using hG
  replace e i := (e i).some
  have hF : F.FullyFaithful := .ofFullyFaithful _
  let H : J ⥤ C := {
    obj := Hobj
    map {i j} f := hF.preimage <| (e i).hom ≫ G.map f ≫ (e j).inv
    map_id i := F.map_injective <| by simp
    map_comp {i j k} f g := F.map_injective <| by simp
  }
  exact ⟨Limits.limit H, ⟨IsLimit.conePointsIsoOfNatIso (s := F.mapCone <| limit.cone H)
    (isLimitOfPreserves _ (limit.isLimit H)) hc <| NatIso.ofComponents e⟩⟩

/-- The essential image of a functor is closed under the colimits it preserves. -/
protected lemma ClosedUnderColimitsOfShape.essImage [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] [F.Full] [F.Faithful] :
    ClosedUnderColimitsOfShape J F.essImage := by
  rintro G c hc hG
  choose Hobj e using hG
  replace e i := (e i).some
  have hF : F.FullyFaithful := .ofFullyFaithful _
  let H : J ⥤ C := {
    obj := Hobj
    map {i j} f := hF.preimage <| (e i).hom ≫ G.map f ≫ (e j).inv
    map_id i := F.map_injective <| by simp
    map_comp {i j k} f g := F.map_injective <| by simp
  }
  exact ⟨Limits.colimit H, ⟨IsColimit.coconePointsIsoOfNatIso (s := F.mapCocone <| colimit.cocone H)
    (isColimitOfPreserves _ (colimit.isColimit H)) hc <| NatIso.ofComponents e⟩⟩

end CategoryTheory.Limits
