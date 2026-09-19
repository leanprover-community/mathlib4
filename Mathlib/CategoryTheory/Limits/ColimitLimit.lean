/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The morphism comparing a colimit of limits with the corresponding limit of colimits.

In this file, we introduce morphisms which allow to study the commutation of limits
with colimits.

In the case of an uncurried functor `F : J × K ⥤ C` there is always a
morphism $\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$ (see `colimitLimitToLimitColimit`).
While it is not usually an isomorphism, with additional hypotheses on `J` and `K` it may be,
in which case we say that "colimits commute with limits".

We also study the case of curried bifunctors `F : J ⥤ K ⥤ C`. In this case,
we define a morphism `colimitLimToLimitColim : colimit (F.flip ⋙ lim) ⟶ limit (F ⋙ colim)`.
We show that this morphism is an isomorphism iff `lim : (J ⥤ C) ⥤ C` preserves the
colimit of `F.flip`, and this is also equivalent to saying that `colim : (K ⥤ C) ⥤ C`
preserves the limit of `F`. In particular, `lim : (J ⥤ C) ⥤ C` preserves colimits
of shape `K` iff `colim : (K ⥤ C) ⥤ C` preserves limits of shape `J`.

The prototypical example, proved in `CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`,
is that when `C = Type`, filtered colimits commute with finite limits.

## References
* Borceux, Handbook of categorical algebra 1, Section 2.13
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

@[expose] public section


universe v₁ v₂ v u₁ u₂ u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type u₁} {K : Type u₂} [Category.{v₁} J] [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]

section

variable (F : J × K ⥤ C)

open CategoryTheory.prod CategoryTheory.Prod

theorem map_id_left_eq_curry_map {j : J} {k k' : K} {f : k ⟶ k'} :
    F.map (𝟙 j ×ₘ f) = ((curry.obj F).obj j).map f :=
  rfl

theorem map_id_right_eq_curry_swap_map {j j' : J} {f : j ⟶ j'} {k : K} :
    F.map (f ×ₘ 𝟙 k) = ((curry.obj (Prod.swap K J ⋙ F)).obj k).map f :=
  rfl

variable [HasLimitsOfShape J C]
variable [HasColimitsOfShape K C]

set_option backward.defeqAttrib.useBackward true in
/-- The universal morphism
$\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
-/
noncomputable def colimitLimitToLimitColimit :
    colimit (curry.obj (Prod.swap K J ⋙ F) ⋙ lim) ⟶ limit (curry.obj F ⋙ colim) :=
  limit.lift (curry.obj F ⋙ colim)
    { pt := _
      π :=
        { app := fun j =>
            colimit.desc (curry.obj (Prod.swap K J ⋙ F) ⋙ lim)
              { pt := _
                ι :=
                  { app := fun k =>
                      limit.π ((curry.obj (Prod.swap K J ⋙ F)).obj k) j ≫
                        colimit.ι ((curry.obj F).obj j) k
                    naturality := by
                      intro k k' f
                      simp only [Functor.comp_obj, lim_obj, colimit.cocone_x,
                        Functor.const_obj_obj, Functor.comp_map, lim_map,
                        curry_obj_obj_obj, Prod.swap_obj, limMap_π_assoc, curry_obj_map_app,
                        Prod.swap_map, Functor.const_obj_map, Category.comp_id]
                      rw [map_id_left_eq_curry_map, colimit.w] } }
          naturality := by
            intro j j' f
            dsimp
            ext k
            simp only [Functor.comp_obj, lim_obj, Category.id_comp, colimit.ι_desc,
              colimit.ι_desc_assoc, Category.assoc, ι_colimMap,
              curry_obj_obj_obj, curry_obj_map_app]
            rw [map_id_right_eq_curry_swap_map, limit.w_assoc] } }

/-- Since `colimit_limit_to_limit_colimit` is a morphism from a colimit to a limit,
this lemma characterises it.
-/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem ι_colimitLimitToLimitColimit_π (j) (k) :
    colimit.ι _ k ≫ colimitLimitToLimitColimit F ≫ limit.π _ j =
      limit.π ((curry.obj (Prod.swap K J ⋙ F)).obj k) j ≫ colimit.ι ((curry.obj F).obj j) k := by
  dsimp [colimitLimitToLimitColimit]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- The map `colimit_limit_to_limit_colimit` realized as a map of cones. -/
@[simps]
noncomputable def colimitLimitToLimitColimitCone (G : J ⥤ K ⥤ C) [HasLimit G] :
    colim.mapCone (limit.cone G) ⟶ limit.cone (G ⋙ colim) where
  hom :=
    colim.map (limitIsoSwapCompLim G).hom ≫
      colimitLimitToLimitColimit (uncurry.obj G :) ≫
        lim.map (whiskerRight (currying.unitIso.app G).inv colim)
  w j := by
    dsimp
    ext1 k
    simp only [Category.assoc, limMap_π, Functor.comp_obj, colim_obj, whiskerRight_app,
      colim_map, ι_colimMap_assoc, lim_obj, limitIsoSwapCompLim_hom_app,
      ι_colimitLimitToLimitColimit_π_assoc, curry_obj_obj_obj, Prod.swap_obj,
      uncurry_obj_obj, ι_colimMap, currying_unitIso_inv_app_app_app, Category.id_comp,
      limMap_π_assoc, Functor.flip_obj_obj, flipIsoCurrySwapUncurry_hom_app_app]
    simp [compEvaluation]

end

section

variable [HasColimitsOfShape K C] [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C)

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` as colimits of shape `K`,
this is the cocone of `F.flip` with point `F ⋙ colim`. -/
@[simps, implicit_reducible]
noncomputable def colim.coconeFlip : Cocone F.flip where
  pt := F ⋙ colim
  ι.app k := { app j := colimit.ι (F.obj j) k }

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` has colimits of shape `K`,
the colimit of `F.flip` is `F ⋙ colim`. -/
@[no_expose]
noncomputable def colim.isColimitCoconeFlip : IsColimit (colim.coconeFlip F) :=
  evaluationJointlyReflectsColimits _ (fun _ ↦ colimit.isColimit _)

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` has limits of shape `J`,
this is the cone of `F` with point `F.flip ⋙ lim`. -/
@[simps, implicit_reducible]
noncomputable def lim.cone : Cone F where
  pt := F.flip ⋙ lim
  π.app j := { app k := limit.π (F.flip.obj k) j }
  π.naturality _ _ f := by ext k; simp [dsimp% limit.w (F.flip.obj k) f]

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` has limits of shape `J`,
the limit of `F` is `F.flip ⋙ lim`. -/
@[no_expose]
noncomputable def lim.isLimitCone : IsLimit (lim.cone F) :=
  evaluationJointlyReflectsLimits _ (fun _ ↦ limit.isLimit _)

/-- Given a bifunctor `F : J ⥤ K ⥤ C`, and assuming that `C` has limits of shape `J` and
colimit of shape `K`, this is the canonical morphism from the colimit of `F.flip ⋙ lim`
and the limit of `F ⋙ colimit`. -/
@[no_expose]
noncomputable def colimitLimToLimitColim :
    colimit (F.flip ⋙ lim) ⟶ limit (F ⋙ colim) :=
  colimit.desc (F.flip ⋙ lim) (lim.mapCocone (colim.coconeFlip F))

@[reassoc (attr := simp)]
lemma ι_colimitToLimit_π (j : J) (k : K) :
    colimit.ι _ k ≫ colimitLimToLimitColim F ≫ limit.π _ j =
    limit.π (F.flip.obj k) j ≫ colimit.ι (F.obj j) k := by
  simp [colimitLimToLimitColim]

lemma colimitLimToLimitColim_eq_colimit_desc :
    colimitLimToLimitColim F =
      colimit.desc (F.flip ⋙ lim) (lim.mapCocone (colim.coconeFlip F)) := by
  cat_disch

lemma colimitLimToLimitColim_eq_limit_lift :
    colimitLimToLimitColim F =
      limit.lift (F ⋙ colim) (colim.mapCone (lim.cone F)) := by
  cat_disch

lemma isIso_colimitLimToLimitColim_iff_preservesColimit :
    IsIso (colimitLimToLimitColim F) ↔ PreservesColimit F.flip lim := by
  rw [preservesColimit_iff_isColimit_mapCocone (colim.isColimitCoconeFlip F),
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc,
    colimit.isColimit_desc, colimitLimToLimitColim_eq_colimit_desc]

lemma isIso_colimitLimToLimitColim_iff_preservesLimit :
    IsIso (colimitLimToLimitColim F) ↔ PreservesLimit F colim := by
  rw [preservesLimit_iff_isLimit_mapCone (lim.isLimitCone F),
    (limit.isLimit _).nonempty_isLimit_iff_isIso_lift,
    limit.isLimit_lift, colimitLimToLimitColim_eq_limit_lift]

lemma preservesColimit_flip_lim_iff_preservesLimit_colim :
    PreservesColimit F.flip lim ↔ PreservesLimit F colim := by
  rw [← isIso_colimitLimToLimitColim_iff_preservesColimit,
    isIso_colimitLimToLimitColim_iff_preservesLimit]

lemma preservesColimit_lim_iff_preservesLimit_colim (F : K ⥤ J ⥤ C) :
    PreservesColimit F lim ↔ PreservesLimit F.flip colim :=
  preservesColimit_flip_lim_iff_preservesLimit_colim F.flip

end

variable (J K C) in
lemma preservesColimitsOfShape_lim_iff_preservesLimitsOfShape_colim
    [HasColimitsOfShape K C] [HasLimitsOfShape J C] :
    PreservesColimitsOfShape K (lim : (J ⥤ C) ⥤ C) ↔
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ C) := by
  refine ⟨fun _ ↦ ⟨fun {F} ↦ ?_⟩, fun _ ↦ ⟨fun {F} ↦ ?_⟩⟩
  · rw [← preservesColimit_flip_lim_iff_preservesLimit_colim]
    infer_instance
  · rw [preservesColimit_lim_iff_preservesLimit_colim]
    infer_instance

end CategoryTheory.Limits
