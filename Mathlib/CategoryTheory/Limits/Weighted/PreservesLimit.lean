/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier, Lyne Moser, Nima Rasekh
-/
module

public import Mathlib.CategoryTheory.Limits.Weighted.HasWeightedLimit
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Weighted limits preserve limits on the weight variable

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  {K : Type*} [Category* K]

namespace Functor.weightedLimFlipObj'

noncomputable def preservesLimit'
    [HasColimitsOfShape K (Type w)]
    {F : J ⥤ C} {G : K ⥤ (hasWeightedLimit.{w} F).FullSubcategory}
    (c : Cocone G) (hc : IsColimit ((ObjectProperty.ι _).mapCocone c)) :
    IsLimit ((weightedLimFlipObj'.{w} F).mapCone c.op) := by
  sorry

/-set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def preservesLimit
    [HasColimitsOfShape Kᵒᵖ (Type w)]
    {F : J ⥤ C} {G : K ⥤ (hasWeightedLimit.{w} F).FullSubcategoryᵒᵖ}
    (c : Cone G) (hc : IsColimit ((ObjectProperty.ι _).mapCocone (coconeLeftOpOfCone c))) :
    IsLimit ((weightedLimFlipObj'.{w} F).mapCone c) where
  lift s := by
    refine (isLimitWeightedLimCone c.pt.unop.obj F).lift (fun j ↦ ?_) sorry
    refine ((Types.isColimit_iff_coconeTypesIsColimit _).1
      ⟨isColimitOfPreserves ((evaluation _ _).obj j) hc⟩).desc
        (CoconeTypes.mk _ (fun k x ↦ s.π.app k.unop ≫ weightedLimObjObjπ _ _ x) sorry)
  fac := sorry
  uniq := sorry-/

end Functor.weightedLimFlipObj'

end CategoryTheory
