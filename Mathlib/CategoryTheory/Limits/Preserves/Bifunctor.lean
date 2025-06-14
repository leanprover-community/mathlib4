/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Preservations of limits for bifunctors

Let `G : C₁ ⥤ C₂ ⥤ C` a functor. We introduce a class `PreservesLimit₂ K₁ K₂ G` that encodes
the hypothesis that the curried functor `F : C₁ × C₂ ⥤ C` preserves limits of the diagram
`K₁ × K₂ : J₁ × J₂ ⥤ C₁ × C₂`. We give a basic API to extract isomorphisms
$\lim_{(j_1,j_2)} G(K_1(j_1), K_2(j_2)) \simeq G(\lim K_1, \lim K_2)$
out of this typeclass.

-/

namespace CategoryTheory

open Category Limits

variable {J₁ J₂ : Type*} [Category J₁] [Category J₂]
  {C₁ C₂ C : Type*} [Category C₁] [Category C₂] [Category C]

/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cocones
over these diagrams, `G.mapCocone₂ c₁ c₂` is the cocone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
def Functor.mapCocone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cocone K₁) (c₂ : Cocone K₂) :
    Cocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  ι :=
    { app := fun ⟨j₁, j₂⟩ ↦ (G.map <| c₁.ι.app j₁).app _ ≫ (G.obj _).map (c₂.ι.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, comp_id, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w] }

/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cones
over these diagrams, `G.mapCone₂ c₁ c₂` is the cone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
def Functor.mapCone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cone K₁) (c₂ : Cone K₂) :
    Cone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  π :=
    { app := fun ⟨j₁, j₂⟩ ↦ (G.map <| c₁.π.app j₁).app _ ≫ (G.obj _).map (c₂.π.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, id_comp, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w, c₂.w] }

namespace Limits

/-- A functor `PreservesColimit₂ K₁ K₂` if whenever `c₁` is a colimit cocone and `c₂` is a colimit
cocone then `G.mapCocone₂ c₁ c₂` is a colimit cocone. This can be thought of as the data of an
isomorphism
$\mathrm{colim}_{(j_1,j_2)} G(K_1(j_1),K_2(j_2)) \simeq G(\mathrm{colim} K_1,\mathrm{colim} K_2)$.
-/
class PreservesColimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  nonempty_isColimit_mapCocone₂ {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
      {c₂ : Cocone K₂} (hc₂ : IsColimit c₂) :
    Nonempty <| IsColimit <| G.mapCocone₂ c₁ c₂

/-- A functor `PreservesLimit₂ K₁ K₂` if whenever `c₁` is a limit cone and `c₂` is a limit
cone then `G.mapCone₂ c₁ c₂` is a limit cone. This can be thought of as the data of an
isomorphism $\lim_{(j_1,j_2)} G(K_1(j_1), K_2(j_2)) \simeq G(\lim K_1, \lim K_2)$.
-/
class PreservesLimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  nonempty_isLimit_mapCone₂ {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
      {c₂ : Cone K₂} (hc₂ : IsLimit c₂) :
    Nonempty <| IsLimit <| G.mapCone₂ c₁ c₂

variable {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂} (G : C₁ ⥤ C₂ ⥤ C)

/-- If `PreservesColimit₂ K₁ K₂ G`, obtain that `G.mapCocone₂ c₁ c₂` is a colimit cocone
whenever c₁ c₂ are colimit cocones. -/
noncomputable def isColimitOfPreserves₂ [PreservesColimit₂ K₁ K₂ G]
    {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone K₂} (hc₂ : IsColimit c₂) :
    IsColimit (G.mapCocone₂ c₁ c₂) :=
  PreservesColimit₂.nonempty_isColimit_mapCocone₂ hc₁ hc₂|>.some

/-- If `PreservesLimit₂ K₁ K₂ G`, obtain that `G.mapCone₂ c₁ c₂` is a limit cone
whenever c₁ c₂ are limit cones. -/
noncomputable def isLimitOfPreserves₂ [PreservesLimit₂ K₁ K₂ G]
    {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
    {c₂ : Cone K₂} (hc₂ : IsLimit c₂) :
    IsLimit (G.mapCone₂ c₁ c₂) :=
  PreservesLimit₂.nonempty_isLimit_mapCone₂ hc₁ hc₂|>.some

instance [HasColimit K₁] [HasColimit K₂] [PreservesColimit₂ K₁ K₂ G] :
    HasColimit <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  exists_colimit := ⟨{
    cocone := _
    isColimit :=
      PreservesColimit₂.nonempty_isColimit_mapCocone₂
        (getColimitCocone K₁).isColimit
        (getColimitCocone K₂).isColimit|>.some }⟩

instance [HasLimit K₁] [HasLimit K₂] [PreservesLimit₂ K₁ K₂ G] :
    HasLimit <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G) where
  exists_limit := ⟨{
    cone := _
    isLimit :=
      PreservesLimit₂.nonempty_isLimit_mapCone₂
        (getLimitCone K₁).isLimit
        (getLimitCone K₂).isLimit|>.some }⟩

namespace PreservesColimit₂

variable [PreservesColimit₂ K₁ K₂ G]

/-- Given a `PreservesColimit₂` instance, extract the isomorphism between
a colimit of `uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)` and
`(G.obj c₁).obj c₂` where c₁ (resp. c₂) is a colimit of `K₁` (resp `K₂`). -/
noncomputable def isoObjCoconePointsOfIsColimit
    {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone K₂} (hc₂ : IsColimit c₂)
    {c₃ : Cocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)}
    (hc₃ : IsColimit c₃) :
    (G.obj c₁.pt).obj c₂.pt ≅ c₃.pt :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves₂ G hc₁ hc₂) hc₃

section

variable {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
  {c₂ : Cocone K₂} (hc₂ : IsColimit c₂)
  {c₃ : Cocone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)}
  (hc₃ : IsColimit c₃)

/-- Characterize the inverse direction of the isomorphism
`PreservesColimit₂.isoObjCoconePointsOfIsColimit` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma ι_comp_isoObjConePointsOfIsColimit_inv (j : J₁ × J₂) :
    c₃.ι.app j ≫
      (isoObjCoconePointsOfIsColimit G hc₁ hc₂ hc₃).inv =
    (G.map <| c₁.ι.app j.1).app (K₂.obj j.2) ≫ (G.obj c₁.pt).map (c₂.ι.app j.2) := by
  dsimp [isoObjCoconePointsOfIsColimit, Functor.mapCocone₂]
  aesop_cat

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoObjCoconePointsOfIsColimit` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma map_ι_comp_isoObjConePointsOfIsColimit_hom (j : J₁ × J₂) :
    (G.map (c₁.ι.app j.1)).app (K₂.obj j.2) ≫ (G.obj c₁.pt).map (c₂.ι.app j.2) ≫
      (isoObjCoconePointsOfIsColimit G hc₁ hc₂ hc₃).hom =
    c₃.ι.app j := by
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  simp

end

variable (K₁ K₂) [HasColimit K₁] [HasColimit K₂]

/-- Extract the isomorphism between
`colim (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G))` and
`(G.obj (colim K₁)).obj (colim K₂)` from a `PreservesColimit₂` instance, provided the relevant
colimits exist. -/
noncomputable def isoColimitUncurryWhiskeringLeft₂ :
    colimit (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) ≅
    (G.obj <| colimit K₁).obj (colimit K₂) :=
  isoObjCoconePointsOfIsColimit G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)|>.symm

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma ι_comp_isoColimitUncurryWhiskeringLeft₂_hom (j : J₁ × J₂) :
    colimit.ι (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom =
    (G.map <| colimit.ι K₁ j.1).app (K₂.obj j.2) ≫ (G.obj <| colimit K₁).map (colimit.ι K₂ j.2) :=
  ι_comp_isoObjConePointsOfIsColimit_inv G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
lemma map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv (j : J₁ × J₂) :
    (G.map (colimit.ι K₁ j.1)).app (K₂.obj j.2) ≫ (G.obj <| colimit K₁).map (colimit.ι K₂ j.2) ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv =
    colimit.ι (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j :=
  map_ι_comp_isoObjConePointsOfIsColimit_hom G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

end PreservesColimit₂

namespace PreservesLimit₂

variable [PreservesLimit₂ K₁ K₂ G]

/-- Given a `PreservesLimit₂` instance, extract the isomorphism between
a limit of `uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)` and
`(G.obj c₁).obj c₂` where c₁ (resp. c₂) is a limit of `K₁` (resp `K₂`). -/
noncomputable def isoObjConePointsOfIsLimit
    {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
    {c₂ : Cone K₂} (hc₂ : IsLimit c₂)
    {c₃ : Cone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)}
    (hc₃ : IsLimit c₃) :
    (G.obj c₁.pt).obj c₂.pt ≅ c₃.pt :=
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves₂ G hc₁ hc₂) hc₃

section

variable {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
  {c₂ : Cone K₂} (hc₂ : IsLimit c₂)
  {c₃ : Cone <| uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)}
  (hc₃ : IsLimit c₃)

/-- Characterize the forward direction of the isomorphism
`PreservesLimit₂.isoObjConePointsOfIsLimit` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma isoObjConePointsOfIsLimit_hom_comp_π (j : J₁ × J₂) :
    (isoObjConePointsOfIsLimit G hc₁ hc₂ hc₃).hom ≫ c₃.π.app j =
    (G.map <| c₁.π.app j.1).app c₂.pt ≫ (G.obj <| K₁.obj j.1).map (c₂.π.app j.2) := by
  dsimp [isoObjConePointsOfIsLimit, Functor.mapCocone₂]
  aesop_cat

/-- Characterize the inverse direction of the isomorphism
`PreservesLimit₂.isoObjConePointsOfIsLimit` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma isoObjConePointsOfIsColimit_inv_comp_map_π (j : J₁ × J₂) :
    (isoObjConePointsOfIsLimit G hc₁ hc₂ hc₃).inv ≫
      (G.map (c₁.π.app j.1)).app c₂.pt ≫ (G.obj <| K₁.obj j.1).map (c₂.π.app j.2) =
    c₃.π.app j := by
  rw [Iso.inv_comp_eq]
  simp

end

variable (K₁) (K₂) [HasLimit K₁] [HasLimit K₂]

/-- Extract the isomorphism between
`colim (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G))` and
`(G.obj (colim K₁)).obj (colim K₂)` from a `PreservesLimit₂` instance, provided the relevant
limits exist. -/
noncomputable def isoLimitUncurryWhiskeringLeft₂ :
    limit (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) ≅
    (G.obj <| limit K₁).obj (limit K₂) :=
  isoObjConePointsOfIsLimit G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)|>.symm

/-- Characterize the inverse direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma isoLimitUncurryWhiskeringLeft₂_inv_comp_π (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv ≫
      limit.π (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j =
    (G.map <| limit.π K₁ j.1).app (limit K₂) ≫ (G.obj <| K₁.obj j.1).map (limit.π K₂ j.2) :=
  isoObjConePointsOfIsLimit_hom_comp_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

/-- Characterize the forward direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t the canonical maps to the limit. -/
@[reassoc (attr := simp)]
lemma isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom ≫
      (G.map (limit.π K₁ j.1)).app (limit K₂) ≫ (G.obj <| K₁.obj j.1).map (limit.π K₂ j.2) =
    limit.π (uncurry.obj (whiskeringLeft₂ C|>.obj K₁|>.obj K₂|>.obj G)) j :=
  isoObjConePointsOfIsColimit_inv_comp_map_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

end PreservesLimit₂

end Limits

end CategoryTheory
