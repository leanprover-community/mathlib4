/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.limits from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Isomorphisms about functors which preserve (co)limits

If `G` preserves limits, and `C` and `D` have limits, then for any diagram `F : J ⥤ C` we have a
canonical isomorphism `preservesLimitsIso : G.obj (Limit F) ≅ Limit (F ⋙ G)`.
We also show that we can commute `IsLimit.lift` of a preserved limit with `Functor.mapCone`:
`(PreservesLimit.preserves t).lift (G.mapCone c₂) = G.map (t.lift c₂)`.

The duals of these are also given. For functors which preserve (co)limits of specific shapes, see
`preserves/shapes.lean`.
-/


universe w' w v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {J : Type w} [Category.{w'} J]

variable (F : J ⥤ C)

section

variable [PreservesLimit F G]

@[simp]
theorem preserves_lift_mapCone (c₁ c₂ : Cone F) (t : IsLimit c₁) :
    (PreservesLimit.preserves t).lift (G.mapCone c₂) = G.map (t.lift c₂) :=
  ((PreservesLimit.preserves t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm
                                                          -- 🎉 no goals
#align category_theory.preserves_lift_map_cone CategoryTheory.preserves_lift_mapCone

variable [HasLimit F] [HasLimit (F ⋙ G)]

/-- If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preservesLimitIso : G.obj (limit F) ≅ limit (F ⋙ G) :=
  (PreservesLimit.preserves (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)
#align category_theory.preserves_limit_iso CategoryTheory.preservesLimitIso

@[reassoc (attr := simp)]
theorem preservesLimitsIso_hom_π (j) :
    (preservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j
#align category_theory.preserves_limits_iso_hom_π CategoryTheory.preservesLimitsIso_hom_π

@[reassoc (attr := simp)]
theorem preservesLimitsIso_inv_π (j) :
    (preservesLimitIso G F).inv ≫ G.map (limit.π F j) = limit.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ j
#align category_theory.preserves_limits_iso_inv_π CategoryTheory.preservesLimitsIso_inv_π

@[reassoc (attr := simp)]
theorem lift_comp_preservesLimitsIso_hom (t : Cone F) :
    G.map (limit.lift _ t) ≫ (preservesLimitIso G F).hom =
    limit.lift (F ⋙ G) (G.mapCone _) := by
  ext
  -- ⊢ (G.map (limit.lift F t) ≫ (preservesLimitIso G F).hom) ≫ limit.π (F ⋙ G) j✝  …
  simp [← G.map_comp]
  -- 🎉 no goals
#align category_theory.lift_comp_preserves_limits_iso_hom CategoryTheory.lift_comp_preservesLimitsIso_hom

variable [PreservesLimitsOfShape J G] [HasLimitsOfShape J D] [HasLimitsOfShape J C]

/-- If `C, D` has all limits of shape `J`, and `G` preserves them, then `preservesLimitsIso` is
functorial wrt `F`. -/
@[simps!]
def preservesLimitNatIso : lim ⋙ G ≅ (whiskeringRight J C D).obj G ⋙ lim :=
  NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      -- ⊢ (lim ⋙ G).map f ≫ ((fun F => preservesLimitIso G F) Y✝).hom = ((fun F => pre …
      apply limit.hom_ext; intro j
      -- ⊢ ∀ (j : J), ((lim ⋙ G).map f ≫ ((fun F => preservesLimitIso G F) Y✝).hom) ≫ l …
                           -- ⊢ ((lim ⋙ G).map f ≫ ((fun F => preservesLimitIso G F) Y✝).hom) ≫ limit.π (((w …
      dsimp
      -- ⊢ (G.map (limMap f) ≫ (preservesLimitIso G Y✝).hom) ≫ limit.π (Y✝ ⋙ G) j = ((p …
      simp only [preservesLimitsIso_hom_π, whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitsIso_hom_π_assoc, ← G.map_comp])
#align category_theory.preserves_limit_nat_iso CategoryTheory.preservesLimitNatIso

end

section

variable [PreservesColimit F G]

@[simp]
theorem preserves_desc_mapCocone (c₁ c₂ : Cocone F) (t : IsColimit c₁) :
    (PreservesColimit.preserves t).desc (G.mapCocone _) = G.map (t.desc c₂) :=
  ((PreservesColimit.preserves t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm
                                                             -- 🎉 no goals
#align category_theory.preserves_desc_map_cocone CategoryTheory.preserves_desc_mapCocone

variable [HasColimit F] [HasColimit (F ⋙ G)]

-- TODO: think about swapping the order here
/-- If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
def preservesColimitIso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  (PreservesColimit.preserves (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)
#align category_theory.preserves_colimit_iso CategoryTheory.preservesColimitIso

@[reassoc (attr := simp)]
theorem ι_preservesColimitsIso_inv (j : J) :
    colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j
#align category_theory.ι_preserves_colimits_iso_inv CategoryTheory.ι_preservesColimitsIso_inv

@[reassoc (attr := simp)]
theorem ι_preservesColimitsIso_hom (j : J) :
    G.map (colimit.ι F j) ≫ (preservesColimitIso G F).hom = colimit.ι (F ⋙ G) j :=
  (PreservesColimit.preserves (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j
#align category_theory.ι_preserves_colimits_iso_hom CategoryTheory.ι_preservesColimitsIso_hom

@[reassoc (attr := simp)]
theorem preservesColimitsIso_inv_comp_desc (t : Cocone F) :
    (preservesColimitIso G F).inv ≫ G.map (colimit.desc _ t) =
    colimit.desc _ (G.mapCocone t) := by
  ext
  -- ⊢ colimit.ι (F ⋙ G) j✝ ≫ (preservesColimitIso G F).inv ≫ G.map (colimit.desc F …
  simp [← G.map_comp]
  -- 🎉 no goals
#align category_theory.preserves_colimits_iso_inv_comp_desc CategoryTheory.preservesColimitsIso_inv_comp_desc

variable [PreservesColimitsOfShape J G] [HasColimitsOfShape J D] [HasColimitsOfShape J C]

/-- If `C, D` has all colimits of shape `J`, and `G` preserves them, then `preservesColimitIso`
is functorial wrt `F`. -/
@[simps!]
def preservesColimitNatIso : colim ⋙ G ≅ (whiskeringRight J C D).obj G ⋙ colim :=
  NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      -- ⊢ (colim ⋙ G).map f ≫ ((fun F => preservesColimitIso G F) Y✝).hom = ((fun F => …
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
      -- ⊢ ((fun F => preservesColimitIso G F) X✝).inv ≫ (colim ⋙ G).map f = ((whiskeri …
      apply colimit.hom_ext; intro j
      -- ⊢ ∀ (j : J), colimit.ι (((whiskeringRight J C D).obj G).obj X✝) j ≫ ((fun F => …
                             -- ⊢ colimit.ι (((whiskeringRight J C D).obj G).obj X✝) j ≫ ((fun F => preservesC …
      dsimp
      -- ⊢ colimit.ι (X✝ ⋙ G) j ≫ (preservesColimitIso G X✝).inv ≫ G.map (colimMap f) = …
      erw [ι_colimMap_assoc]
      -- ⊢ colimit.ι (X✝ ⋙ G) j ≫ (preservesColimitIso G X✝).inv ≫ G.map (colimMap f) = …
      simp only [ι_preservesColimitsIso_inv, whiskerRight_app, Category.assoc,
        ι_preservesColimitsIso_inv_assoc, ← G.map_comp]
      erw [ι_colimMap])
      -- 🎉 no goals
#align category_theory.preserves_colimit_nat_iso CategoryTheory.preservesColimitNatIso

end

end CategoryTheory
