/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Bracket operation
-/

@[expose] public section

universe w u

open CategoryTheory

@[simps!]
def _root_.CategoryTheory.CategoryOfElements.mapπiso
    {C : Type*} [Category* C] {F G : C ⥤ Type u} (f : F ⟶ G) :
    CategoryOfElements.map f ⋙ CategoryOfElements.π G ≅ CategoryOfElements.π F :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

@[simp]
lemma CategoryTheory.CategoryOfElements.map_id_obj
    {C : Type*} [Category* C] {F : C ⥤ Type u} (j : F.Elements) :
    (map (𝟙 F)).obj j = j :=
  rfl

@[simp]
lemma CategoryTheory.CategoryOfElements.map_comp_obj
    {C : Type*} [Category* C] {F G H : C ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H)
    (j : F.Elements) :
    (map (f ≫ g)).obj j = (map g).obj ((map f).obj j) :=
  rfl

namespace CategoryTheory

open Limits

variable {C A : Type*} [Category* C] [Category* A]
  (X : C ⥤ A) (K : C ⥤ Type w)

abbrev bracketDiag : K.Elements ⥤ A :=
  CategoryOfElements.π K ⋙ X

abbrev HasBracket : Prop :=
  HasLimit (bracketDiag X K)

/-- The object property of existence of `X[-]`. -/
abbrev hasBracket : ObjectProperty (C ⥤ Type w) :=
  fun K ↦ HasBracket X K

instance (K : (hasBracket X).FullSubcategory) : HasBracket X K.obj := K.property

instance (K : (hasBracket X).FullSubcategory) : HasBracket X ((hasBracket X).ι.obj K) := K.property

noncomputable abbrev bracket [HasBracket X K] : A :=
  limit (bracketDiag X K)

variable {K L M : C ⥤ Type w} [HasBracket X K] [HasBracket X L] [HasBracket X M]

/-- The bracket `X[-]` is functorial in the copresheaf. -/
noncomputable def bracketMap (f : K ⟶ L) : bracket X L ⟶ bracket X K :=
  haveI : HasLimit (CategoryOfElements.map f ⋙ bracketDiag X L) :=
    hasLimit_of_iso (Functor.isoWhiskerRight (CategoryOfElements.mapπiso f) _).symm
  limit.pre (bracketDiag _ _) (CategoryOfElements.map f) ≫
    (HasLimit.isoOfNatIso <| (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryOfElements.mapπiso _) _).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma bracketMap_π (f : K ⟶ L) (j : K.Elements) :
    bracketMap X f ≫ limit.π _ j = limit.π _ ((CategoryOfElements.map f).obj j) := by
  simp [bracketMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bracketMap_id : bracketMap X (𝟙 K) = 𝟙 (bracket X K) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma bracketMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    bracketMap X (f ≫ g) = bracketMap X g ≫ bracketMap X f := by cat_disch

/-- The bracket `X[-]` as a functor on the subcategory where the brackets exist. -/
@[simps]
noncomputable def bracketFunctor : (hasBracket.{w} X).FullSubcategoryᵒᵖ ⥤ A where
  obj K := bracket X K.unop.obj
  map f := bracketMap X f.unop.hom

attribute [local instance] preservesLimitsOfShape_op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable
def isLimit_mapCone_bracketFunctor {J : Type*} [Category* J] [HasColimitsOfShape J (Type w)]
    (D : J ⥤ (hasBracket.{w} X).FullSubcategory)
    (c : Cocone D) (hc : IsColimit ((hasBracket X).ι.mapCocone c)) :
    IsLimit ((bracketFunctor X).mapCone c.op) := by
  letI c'' (s : Cone (D.op ⋙ bracketFunctor X)) (U : C) :
      ((D ⋙ (hasBracket X).ι) ⋙ (evaluation C (Type w)).obj U).CoconeTypes :=
    { pt := s.pt ⟶ X.obj U
      ι j x := s.π.app (.op j) ≫ limit.π (bracketDiag X (D.obj j).obj) (Functor.elementsMk _ U x)
      ι_naturality u :=by
        ext
        simp [← dsimp% s.w u.op]
        rfl }
  letI hU (U : C) := (Types.isColimit_iff_coconeTypesIsColimit _).mp
    ⟨isColimitOfPreserves ((evaluation _ _).obj U) hc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s
    dsimp [bracketFunctor]
    refine limit.lift (bracketDiag X c.pt.obj)
      { pt := s.pt
        π.app := ?_
        π.naturality := ?_ }
    · intro U
      letI hc' := isColimitOfPreserves ((evaluation _ _).obj U.1) hc
      exact (hU U.1).desc (c'' s U.1) U.2
    · intro ⟨U, xU⟩ ⟨V, xV⟩ ⟨(f : U ⟶ V), hf⟩
      dsimp at hf
      obtain ⟨j, a, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective (hU U) xU
      obtain ⟨k, b, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective (hU V) xV
      have := (hU U).fac_apply (c'' s U) j
      simp only [Functor.coconeTypesEquiv_symm_apply_ι, Functor.comp_obj, ObjectProperty.ι_obj,
        evaluation_obj_obj, Functor.mapCocone_pt, Functor.const_obj_obj, Functor.mapCocone_ι_app,
        ObjectProperty.ι_map, evaluation_obj_map, CategoryOfElements.π_obj, Functor.const_obj_map,
        dsimp% (hU V).fac_apply (c'' s V) k, Category.id_comp, dsimp% (hU U).fac_apply (c'' s U) j,
        Functor.comp_map, CategoryOfElements.π_map]
      simp only [Functor.comp_obj, Functor.op_obj, bracketFunctor_obj, Category.assoc, c'']
      dsimp at a
      dsimp at b hf
      have := (D.obj j).obj.map f
      have := limit.w (bracketDiag X (D.obj j).obj)
        (j := Functor.elementsMk _ _ a) (j' := Functor.elementsMk _ V ((D.obj j).obj.map f a))
        (f := CategoryOfElements.homMk _ _ f rfl)
      dsimp at this
      rw [this]
      have := s.w (j := .op j) (j' := .op k) sorry
      -- have := s.w _
      sorry
  · sorry
  · sorry

end CategoryTheory
