/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier, Lyne Moser, Nima Rasekh
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Weighted.HasWeightedLimit

/-!
# Weighted limits preserve limits

-/

@[expose] public section

universe w v'' u'' v' u' v u

namespace CategoryTheory

open Limits Opposite

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  {K : Type*} [Category* K]

namespace Functor

namespace weightedLimFlipObj'

namespace preservesLimit'

variable [HasColimitsOfShape K (Type w)]
  {F : J ⥤ C} {G : K ⥤ (hasWeightedLimit.{w} F).FullSubcategory}
  {c : Cocone G} (hc : IsColimit ((hasWeightedLimit.{w} F).ι.mapCocone c))
  (s : Cone (G.op ⋙ weightedLimFlipObj'.{w} F))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `Functor.weightedLimFlipObj'.preservesLimit'` -/
private noncomputable def π (j : J) : c.pt.obj.obj j → (s.pt ⟶ F.obj j) :=
  ((Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨isColimitOfPreserves ((evaluation _ _).obj j) hc⟩).desc
      (CoconeTypes.mk _ (fun k x ↦ s.π.app (op k) ≫ weightedLimObjObjπ _ _ x)
    (fun {k₁ k₂} f ↦ by ext; simp [← s.w_assoc f.op]))

set_option backward.defeqAttrib.useBackward true in
@[simp]
private lemma π_ι_app_hom_app_apply ⦃j : J⦄ ⦃k : K⦄ (x : (G.obj k).obj.obj j) :
    dsimp% π hc s j ((c.ι.app k).hom.app j x) =
      s.π.app (op k) ≫ weightedLimObjObjπ _ _ x :=
  ((Types.isColimit_iff_coconeTypesIsColimit _).1
      ⟨isColimitOfPreserves ((evaluation _ _).obj j) hc⟩).fac_apply ..

end preservesLimit'

open preservesLimit' in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `F : J ⥤ C` and `K` be a category. We consider a cocone `c`
for a functor `G` from `K` to the fullsubcategory of `J ⥤ Type w` defined
by `hasWeightedLimit.{w} F`. Assuming the cocone `c` is a colimit as a cocone
in `J ⥤ Type w`, we show that after the application of the contravariant
functor `F.weightedLimFlipObj'.{w}`, the corresponding cone in `C` is a limit. -/
@[no_expose]
noncomputable def preservesLimit'
    [HasColimitsOfShape K (Type w)]
    {F : J ⥤ C} {G : K ⥤ (hasWeightedLimit.{w} F).FullSubcategory}
    (c : Cocone G) (hc : IsColimit ((hasWeightedLimit.{w} F).ι.mapCocone c)) :
    IsLimit ((weightedLimFlipObj'.{w} F).mapCone c.op) where
  lift s := (isLimitWeightedLimCone c.pt.obj F).lift (π hc s) (fun j₁ j₂ x f ↦ by
    obtain ⟨k, y, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj j₁) hc) x
    dsimp
    rw [π_ι_app_hom_app_apply, Category.assoc, weightedLimObjObj_w,
      ← π_ι_app_hom_app_apply hc, NatTrans.naturality_apply])
  fac s k := by
    dsimp
    ext j x
    simp
  uniq s m hm := by
    dsimp
    ext j x
    obtain ⟨k, y, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj j) hc) x
    simp [← hm]

set_option backward.defeqAttrib.useBackward true in
lemma preservesLimit
    [HasColimitsOfShape Kᵒᵖ (Type w)]
    (F : J ⥤ C) (G : K ⥤ (hasWeightedLimit.{w} F).FullSubcategoryᵒᵖ)
    [PreservesColimit G.leftOp (hasWeightedLimit.{w} F).ι] :
    PreservesLimit G (weightedLimFlipObj'.{w} F) where
  preserves {c} hc := ⟨by
    refine (IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ?_).1
      ((preservesLimit' (coconeLeftOpOfCone c)
        (isColimitOfPreserves (hasWeightedLimit.{w} F).ι
          (isColimitCoconeLeftOpOfCone _ hc))).whiskerEquivalence
      (opOpEquivalence K).symm)
    exact Cone.ext (Iso.refl _)⟩

end weightedLimFlipObj'

namespace weightedLimObj

variable (W : J ⥤ Type w) [HasWeightedLimObj.{w} W C] [HasLimitsOfShape K C]
  {G : K ⥤ J ⥤ C} {c : Cone G} (hc : IsLimit c)

namespace preservesLimit

variable (s : Cone (G ⋙ W.weightedLimObj))

set_option backward.defeqAttrib.useBackward true in
noncomputable def coneEval ⦃j : J⦄ (x : W.obj j) :
    Cone (G ⋙ (evaluation J C).obj j) where
  pt := s.pt
  π.app k := s.π.app k ≫ W.weightedLimObjObjπ (G.obj k) x
  π.naturality k₁ k₂ f := by simp [← s.w f]

noncomputable def liftAux ⦃j : J⦄ (x : W.obj j) : s.pt ⟶ c.pt.obj j :=
  (isLimitOfPreserves ((evaluation _ _).obj j) hc).lift (coneEval W s x)

@[reassoc (attr := simp)]
lemma liftAux_π_app_app ⦃j : J⦄ (x : W.obj j) (k) :
    liftAux W hc s x ≫ (c.π.app k).app j =
      s.π.app k ≫ W.weightedLimObjObjπ (G.obj k) x :=
  (isLimitOfPreserves ((evaluation _ _).obj j) hc).fac (coneEval W s x) k

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable def isLimitMapCone : IsLimit (W.weightedLimObj.mapCone c) where
  lift s :=
    (isLimitWeightedLimCone W c.pt).lift
      (fun j x ↦ liftAux W hc s x)
      (fun j₁ j₂ x f ↦ (isLimitOfPreserves ((evaluation _ _).obj j₂) hc).hom_ext (by simp))
  uniq s m hm := by
    dsimp
    ext j x
    refine (isLimitOfPreserves ((evaluation _ _).obj j) hc).hom_ext ?_
    simp [← hm]

end preservesLimit

instance preservesLimit : PreservesLimit G (weightedLimObj.{w} W (C := C)) where
  preserves hc := ⟨preservesLimit.isLimitMapCone _ hc⟩

end weightedLimObj

instance [HasColimitsOfShape Kᵒᵖ (Type w)]
    (F : J ⥤ C) [HasWeightedLimFlipObj.{w} F] :
    PreservesLimitsOfShape K (weightedLimFlipObj'.{w} F) where
  preservesLimit := weightedLimFlipObj'.preservesLimit ..

instance [HasColimitsOfShape Kᵒᵖ (Type w)]
    (F : J ⥤ C) [HasWeightedLimFlipObj.{w} F] :
    PreservesLimitsOfShape K (weightedLimFlipObj.{w} F) :=
  preservesLimitsOfShape_of_natIso (weightedLimFlipObjIso.{w} F)

instance [HasColimitsOfSize.{v'', u''} (Type w)]
    (F : J ⥤ C) [HasWeightedLimFlipObj.{w} F] :
    PreservesLimitsOfSize.{v'', u''} (weightedLimFlipObj'.{w} F) where

instance [HasColimitsOfSize.{v'', u''} (Type w)]
    (F : J ⥤ C) [HasWeightedLimFlipObj.{w} F] :
    PreservesLimitsOfSize.{v'', u''} (weightedLimFlipObj.{w} F) where

instance [HasLimitsOfShape K C] (W : J ⥤ Type w) [HasWeightedLimObj.{w} W (C := C)] :
    PreservesLimitsOfShape K (weightedLimObj.{w} W (C := C)) where

instance [HasLimitsOfSize.{v'', u''} C] (W : J ⥤ Type w) [HasWeightedLimObj.{w} W C] :
    PreservesLimitsOfSize.{v'', u''} (W.weightedLimObj (C := C)) where

end Functor

end CategoryTheory
