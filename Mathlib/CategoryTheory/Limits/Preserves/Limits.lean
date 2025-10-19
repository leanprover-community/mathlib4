/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic

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
    (isLimitOfPreserves G t).lift (G.mapCone c₂) = G.map (t.lift c₂) :=
  ((isLimitOfPreserves G t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm

variable [HasLimit F]

/-- If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preservesLimitIso : G.obj (limit F) ≅ limit (F ⋙ G) :=
  (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem preservesLimitIso_hom_π (j) :
    (preservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

@[reassoc (attr := simp)]
theorem preservesLimitIso_inv_π (j) :
    (preservesLimitIso G F).inv ≫ G.map (limit.π F j) = limit.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

@[reassoc (attr := simp)]
theorem lift_comp_preservesLimitIso_hom (t : Cone F) :
    G.map (limit.lift _ t) ≫ (preservesLimitIso G F).hom =
    limit.lift (F ⋙ G) (G.mapCone _) := by
  ext
  simp [← G.map_comp]

instance : IsIso (limit.post F G) :=
  show IsIso (preservesLimitIso G F).hom from inferInstance

variable [PreservesLimitsOfShape J G] [HasLimitsOfShape J D] [HasLimitsOfShape J C]

/-- If `C, D` has all limits of shape `J`, and `G` preserves them, then `preservesLimitsIso` is
functorial w.r.t. `F`. -/
@[simps!]
def preservesLimitNatIso : lim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ lim :=
  NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      apply limit.hom_ext; intro j
      dsimp
      simp only [preservesLimitIso_hom_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitIso_hom_π_assoc, ← G.map_comp])

end

section

variable [HasLimit F] [HasLimit (F ⋙ G)]

/-- If the comparison morphism `G.obj (limit F) ⟶ limit (F ⋙ G)` is an isomorphism, then `G`
preserves limits of `F`. -/
lemma preservesLimit_of_isIso_post [IsIso (limit.post F G)] : PreservesLimit F G :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit F) (by
    convert IsLimit.ofPointIso (limit.isLimit (F ⋙ G))
    assumption)

end

section

variable [PreservesColimit F G]

@[simp]
theorem preserves_desc_mapCocone (c₁ c₂ : Cocone F) (t : IsColimit c₁) :
    (isColimitOfPreserves G t).desc (G.mapCocone _) = G.map (t.desc c₂) :=
  ((isColimitOfPreserves G t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm

variable [HasColimit F]

-- TODO: think about swapping the order here
/-- If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
def preservesColimitIso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  (isColimitOfPreserves G (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
theorem ι_preservesColimitIso_inv (j : J) :
    colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j

@[reassoc (attr := simp)]
theorem ι_preservesColimitIso_hom (j : J) :
    G.map (colimit.ι F j) ≫ (preservesColimitIso G F).hom = colimit.ι (F ⋙ G) j :=
  (isColimitOfPreserves G (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j

@[reassoc (attr := simp)]
theorem preservesColimitIso_inv_comp_desc (t : Cocone F) :
    (preservesColimitIso G F).inv ≫ G.map (colimit.desc _ t) =
    colimit.desc _ (G.mapCocone t) := by
  ext
  simp [← G.map_comp]

instance : IsIso (colimit.post F G) :=
  show IsIso (preservesColimitIso G F).inv from inferInstance

variable [PreservesColimitsOfShape J G] [HasColimitsOfShape J D] [HasColimitsOfShape J C]

/-- If `C, D` has all colimits of shape `J`, and `G` preserves them, then `preservesColimitIso`
is functorial w.r.t. `F`. -/
@[simps!]
def preservesColimitNatIso : colim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ colim :=
  NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
      apply colimit.hom_ext; intro j
      dsimp
      rw [ι_colimMap_assoc]
      simp only [ι_preservesColimitIso_inv, Functor.whiskerRight_app,
        ι_preservesColimitIso_inv_assoc, ← G.map_comp]
      rw [ι_colimMap])

end

section

variable [HasColimit F] [HasColimit (F ⋙ G)]

/-- If the comparison morphism `colimit (F ⋙ G) ⟶ G.obj (colimit F)` is an isomorphism, then `G`
preserves colimits of `F`. -/
lemma preservesColimit_of_isIso_post [IsIso (colimit.post F G)] : PreservesColimit F G :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) (by
    convert IsColimit.ofPointIso (colimit.isColimit (F ⋙ G))
    assumption)

end

end CategoryTheory
