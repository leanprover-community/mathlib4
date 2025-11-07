/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preservation of (co)limits in the functor category

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
  for `F : C ⥤ D` preserves colimits.

  The idea of the proof is simply that products and colimits in the functor category are computed
  pointwise, so pointwise preservation implies general preservation.
* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

# References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/


universe w w' v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Limits Functor

section

variable {C : Type u} [Category.{v₁} C]
variable {D : Type u₂} [Category.{u} D]
variable {E : Type u} [Category.{v₂} E]

/-- If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a special case.
That is, even with a formalised proof of the general statement, there would still need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅
  prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
lemma FunctorCategory.prod_preservesColimits [HasBinaryProducts D] [HasColimits D]
    [∀ X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F) where
  preservesColimitsOfShape {J : Type u} [Category.{u, u} J] :=
    {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let this :=
              isColimitOfPreserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply IsColimit.mapCoconeEquiv _ this
            apply (NatIso.ofComponents _ _).symm
            · intro G
              apply asIso (prodComparison ((evaluation C D).obj k) F G)
            · intro G G'
              apply prodComparison_natural ((evaluation C D).obj k) (𝟙 F)⟩ } ) }

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

instance whiskeringLeft_preservesLimitsOfShape (J : Type u) [Category.{v} J]
    [HasLimitsOfShape J D] (F : C ⥤ E) :
    PreservesLimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro Y
      change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

instance whiskeringLeft_preservesColimitsOfShape (J : Type u) [Category.{v} J]
    [HasColimitsOfShape J D] (F : C ⥤ E) :
    PreservesColimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro Y
      change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

instance whiskeringLeft_preservesLimits [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesLimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesLimitsOfShape J F⟩

instance whiskeringLeft_preservesColimit [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesColimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesColimitsOfShape J F⟩

instance whiskeringRight_preservesLimitsOfShape {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

/-- Whiskering right and then taking a limit is the same as taking the limit and applying the
functor. -/
def limitCompWhiskeringRightIsoLimitComp {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    limit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ limit G ⋙ F :=
  (preservesLimitIso _ _).symm

@[reassoc (attr := simp)]
theorem limitCompWhiskeringRightIsoLimitComp_inv_π {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).inv ≫
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j = whiskerRight (limit.π G j) F := by
  simp [limitCompWhiskeringRightIsoLimitComp]

@[reassoc (attr := simp)]
theorem limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).hom ≫ whiskerRight (limit.π G j) F =
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [← Iso.eq_inv_comp]

instance whiskeringRight_preservesColimitsOfShape {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun k => ?_)
      change IsColimit (((evaluation _ _).obj k ⋙ F).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

/-- Whiskering right and then taking a colimit is the same as taking the colimit and applying the
functor. -/
def colimitCompWhiskeringRightIsoColimitComp {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    colimit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ colimit G ⋙ F :=
  (preservesColimitIso _ _).symm

@[reassoc (attr := simp)]
theorem ι_colimitCompWhiskeringRightIsoColimitComp_hom {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j ≫
      (colimitCompWhiskeringRightIsoColimitComp F G).hom = whiskerRight (colimit.ι G j) F := by
  simp [colimitCompWhiskeringRightIsoColimitComp]

@[reassoc (attr := simp)]
theorem whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv {C : Type*} [Category C]
    {D : Type*} [Category D] {E : Type*} [Category E] {J : Type*} [Category J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    whiskerRight (colimit.ι G j) F ≫ (colimitCompWhiskeringRightIsoColimitComp F G).inv =
      colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [Iso.comp_inv_eq]

instance whiskeringRightPreservesLimits {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : D ⥤ E) [HasLimitsOfSize.{w, w'} D]
    [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩

instance whiskeringRightPreservesColimits {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : D ⥤ E) [HasColimitsOfSize.{w, w'} D]
    [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩

/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
lemma preservesLimit_of_lan_preservesLimit {C D : Type u} [SmallCategory C]
    [SmallCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J]
    [PreservesLimitsOfShape J (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F :=
  letI := preservesLimitsOfShape_of_natIso (J := J)
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm
  preservesLimitsOfShape_of_reflects_of_preserves F uliftYoneda.{u}

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
lemma preservesFiniteLimits_of_evaluation {D : Type*} [Category D] {E : Type*} [Category E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteLimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteLimits F :=
  ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteLimits _⟩

/-- `F : C ⥤ D ⥤ E` preserves finite limits if it does for each `d : D`. -/
lemma preservesFiniteColimits_of_evaluation {D : Type*} [Category D] {E : Type*} [Category E]
    (F : C ⥤ D ⥤ E) (h : ∀ d : D, PreservesFiniteColimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteColimits F :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteColimits _⟩

end

section

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable {D : Type u₃} [Category.{v₃} D]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]

noncomputable instance : PreservesLimitsOfShape J (colim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesLimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (colim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        colimit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (colimitObjIsoColimitCompEvaluation _ _) ≪≫
          (by exact HasColimit.isoOfNatIso (Iso.refl _)) ≪≫
          (colimitObjIsoColimitCompEvaluation _ _).symm)
        (fun {F G} η => colimit_obj_ext (fun j => by simp [← NatTrans.comp_app_assoc]))
    preservesLimitsOfShape_of_natIso (i ≪≫ colimitFlipIsoCompColim _).symm)

end

section

variable [HasColimitsOfShape J C] [HasLimitsOfShape K C]
variable [PreservesColimitsOfShape J (lim : (K ⥤ C) ⥤ _)]

noncomputable instance : PreservesColimitsOfShape J (lim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesColimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (lim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        limit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (limitObjIsoLimitCompEvaluation _ _) ≪≫
          (by exact HasLimit.isoOfNatIso (Iso.refl _)) ≪≫
          (limitObjIsoLimitCompEvaluation _ _).symm)
        (fun {F G} η => limit_obj_ext (fun j => by simp [← NatTrans.comp_app]))
    preservesColimitsOfShape_of_natIso (i ≪≫ limitFlipIsoCompLim _).symm)

end

end

end CategoryTheory
