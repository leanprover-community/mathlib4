/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Bracket operation on copresheaves

Given a functor `X : C ⥤ A` and a copresheaf `K : C ⥤ Type w`, we define the object
`X[K] : A`, which is the limit over the diagram `CategoryOfElements.π K ⋙ X : ∫ K ⥤ A`.

This is used to define a bracket operation of a (semi)simplicial object with a (semi)simplicial
set.

## Main declarations

- `CategoryTheory.Functor.bracket`: The bracket `X[K]` if it exists.
- `CategoryTheory.Functor.isLimitMapConeBracketFunctor`: The bracket sends
  colimits to limits: `X[colimⱼ Kⱼ] ≅ limⱼ X[Kⱼ]`.
-/

@[expose] public section

universe w u

open CategoryTheory

namespace CategoryTheory.Functor

open Limits

variable {C A : Type*} [Category* C] [Category* A]
  (X : C ⥤ A) (K : C ⥤ Type w)

/-- The diagram defining the bracket `X[K]` given by `CategoryOfElements.π K ⋙ X`. -/
abbrev bracketDiag : K.Elements ⥤ A :=
  CategoryOfElements.π K ⋙ X

/-- The bracket `X[K]` exists if the limit over `bracketDiag X K` exists. -/
abbrev HasBracket : Prop :=
  HasLimit (bracketDiag X K)

/-- The object property of existence of `X[-]`. -/
abbrev hasBracket : ObjectProperty (C ⥤ Type w) :=
  fun K ↦ HasBracket X K

instance (K : (hasBracket X).FullSubcategory) : HasBracket X K.obj := K.property

instance (K : (hasBracket X).FullSubcategory) : HasBracket X ((hasBracket X).ι.obj K) := K.property

/-- The bracket `X[K]` of a functor `X : C ⥤ A` and a copresheaf `K : C ⥤ Type w` is
the limit over the diagram `CategoryOfElements.π K ⋙ X`. -/
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
/-- `X[-]` sends colimits of copresheaves to limits: `X[colimⱼ Kⱼ] ≅ limⱼ X[Kⱼ]`.
Here the colimits are taken in `C ⥤ Type w`. -/
noncomputable
def isLimitMapConeBracketFunctor {J : Type*} [Category* J] [HasColimitsOfShape J (Type w)]
    (D : J ⥤ (hasBracket.{w} X).FullSubcategory)
    (c : Cocone D) (hc : IsColimit ((hasBracket X).ι.mapCocone c)) :
    IsLimit ((bracketFunctor X).mapCone c.op) := by
  let c'' (s : Cone (D.op ⋙ bracketFunctor X)) (U : C) :
      ((D ⋙ (hasBracket X).ι) ⋙ (evaluation C (Type w)).obj U).CoconeTypes :=
    { pt := s.pt ⟶ X.obj U
      ι j x := s.π.app (.op j) ≫ limit.π (bracketDiag X (D.obj j).obj) (Functor.elementsMk _ U x)
      ι_naturality u := by
        ext
        simp [← dsimp% s.w u.op, CategoryOfElements.map] }
  have hU (U : C) := (Types.isColimit_iff_coconeTypesIsColimit _).mp
    ⟨isColimitOfPreserves ((evaluation _ _).obj U) hc⟩
  let hom (s : Cone (D.op ⋙ bracketFunctor X)) (U : C) : c.pt.obj.obj U → (s.pt ⟶ X.obj U) :=
    (hU U).desc (c'' s U)
  have hom_fac (s : Cone (D.op ⋙ bracketFunctor X)) (U : C) (j : J) (x) :
      hom s U (((c.ι.app j).hom.app U) x) =
        s.π.app (.op j) ≫ limit.π (bracketDiag X (D.obj j).obj) (Functor.elementsMk _ U x) :=
    (hU U).fac_apply (c'' s U) j x
  have hom_comp (s : Cone (D.op ⋙ bracketFunctor X)) (U V : C) (f : U ⟶ V) :
      hom s V ∘ c.pt.obj.map f = (· ≫ X.map f) ∘ hom s U := by
    refine (hU U).funext fun j ↦ ?_
    ext x
    dsimp
    rw [dsimp% hom_fac, ← ConcreteCategory.comp_apply, ← dsimp% (c.ι.app j).hom.naturality f]
    dsimp
    rw [dsimp% hom_fac]
    have := limit.w (bracketDiag X (D.obj j).obj)
      (CategoryOfElements.homMk (Functor.elementsMk _ U x)
        (Functor.elementsMk _ V ((D.obj j).obj.map f x)) f rfl)
    simp [dsimp% this]
  refine ⟨fun s ↦ ?_, ?_, ?_⟩
  · refine limit.lift (bracketDiag X c.pt.obj)
      { pt := s.pt
        π.app U := hom s U.1 U.2
        π.naturality := ?_ }
    · intro A B f
      obtain ⟨U, x, rfl⟩ := Functor.elementsMk_surjective A
      obtain ⟨V, y, rfl⟩ := Functor.elementsMk_surjective B
      obtain ⟨f, hf, rfl⟩ := CategoryOfElements.homMk_surjective f
      simp [← dsimp% congr($(hom_comp s _ _ f) x), dsimp% hf]
  · intro s j
    apply limit.hom_ext
    intro A
    obtain ⟨U, x, rfl⟩ := Functor.elementsMk_surjective A
    simp [dsimp% hom_fac]
  · intro s m hm
    apply limit.hom_ext (F := bracketDiag X c.pt.obj)
    intro A
    obtain ⟨U, x, rfl⟩ := Functor.elementsMk_surjective A
    obtain ⟨j, a, rfl⟩ := (hU U).ι_jointly_surjective x
    simp [dsimp% hom_fac, ← hm, CategoryOfElements.map]

end CategoryTheory.Functor
