/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.colimit_limit
! leanprover-community/mathlib commit 59382264386afdbaf1727e617f5fdda511992eb9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Functor.Currying
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# The morphism comparing a colimit of limits with the corresponding limit of colimits.

For `F : J × K ⥤ C` there is always a morphism $\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
While it is not usually an isomorphism, with additional hypotheses on `J` and `K` it may be,
in which case we say that "colimits commute with limits".

The prototypical example, proved in `category_theory.limits.filtered_colimit_commutes_finite_limit`,
is that when `C = Type`, filtered colimits commute with finite limits.

## References
* Borceux, Handbook of categorical algebra 1, Section 2.13
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/


universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {J K : Type v} [SmallCategory J] [SmallCategory K]

variable {C : Type u} [Category.{v} C]

variable (F : J × K ⥤ C)

open CategoryTheory.prod

theorem map_id_left_eq_curry_map {j : J} {k k' : K} {f : k ⟶ k'} :
    F.map ((𝟙 j, f) : (j, k) ⟶ (j, k')) = ((curry.obj F).obj j).map f :=
  rfl
#align category_theory.limits.map_id_left_eq_curry_map CategoryTheory.Limits.map_id_left_eq_curry_map

theorem map_id_right_eq_curry_swap_map {j j' : J} {f : j ⟶ j'} {k : K} :
    F.map ((f, 𝟙 k) : (j, k) ⟶ (j', k)) = ((curry.obj (swap K J ⋙ F)).obj k).map f :=
  rfl
#align category_theory.limits.map_id_right_eq_curry_swap_map CategoryTheory.Limits.map_id_right_eq_curry_swap_map

variable [HasLimitsOfShape J C]

variable [HasColimitsOfShape K C]

/-- The universal morphism
$\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
-/
noncomputable def colimitLimitToLimitColimit :
    colimit (curry.obj (swap K J ⋙ F) ⋙ lim) ⟶ limit (curry.obj F ⋙ colim) :=
  limit.lift (curry.obj F ⋙ colim)
    { pt := _
      π :=
        { app := fun j =>
            colimit.desc (curry.obj (swap K J ⋙ F) ⋙ lim)
              { pt := _
                ι :=
                  { app := fun k =>
                      limit.π ((curry.obj (swap K J ⋙ F)).obj k) j ≫
                        colimit.ι ((curry.obj F).obj j) k
                    naturality' := by
                      dsimp
                      intro k k' f
                      simp only [functor.comp_map, curry_obj_map_app, limits.lim_map_π_assoc,
                        swap_map, category.comp_id, map_id_left_eq_curry_map, colimit.w] } }
          naturality' := by
            dsimp
            intro j j' f
            ext k
            simp only [limits.colimit.ι_map, curry_obj_map_app, limits.colimit.ι_desc_assoc,
              limits.colimit.ι_desc, category.id_comp, category.assoc,
              map_id_right_eq_curry_swap_map, limit.w_assoc] } }
#align category_theory.limits.colimit_limit_to_limit_colimit CategoryTheory.Limits.colimitLimitToLimitColimit

/-- Since `colimit_limit_to_limit_colimit` is a morphism from a colimit to a limit,
this lemma characterises it.
-/
@[simp, reassoc.1]
theorem ι_colimitLimitToLimitColimit_π (j) (k) :
    colimit.ι _ k ≫ colimitLimitToLimitColimit F ≫ limit.π _ j =
      limit.π ((curry.obj (swap K J ⋙ F)).obj k) j ≫ colimit.ι ((curry.obj F).obj j) k :=
  by
  dsimp [colimit_limit_to_limit_colimit]
  simp
#align category_theory.limits.ι_colimit_limit_to_limit_colimit_π CategoryTheory.Limits.ι_colimitLimitToLimitColimit_π

@[simp]
theorem ι_colimitLimitToLimitColimit_π_apply (F : J × K ⥤ Type v) (j) (k) (f) :
    limit.π (curry.obj F ⋙ colim) j
        (colimitLimitToLimitColimit F (colimit.ι (curry.obj (swap K J ⋙ F) ⋙ lim) k f)) =
      colimit.ι ((curry.obj F).obj j) k (limit.π ((curry.obj (swap K J ⋙ F)).obj k) j f) :=
  by
  dsimp [colimit_limit_to_limit_colimit]
  simp
#align category_theory.limits.ι_colimit_limit_to_limit_colimit_π_apply CategoryTheory.Limits.ι_colimitLimitToLimitColimit_π_apply

/-- The map `colimit_limit_to_limit_colimit` realized as a map of cones. -/
@[simps]
noncomputable def colimitLimitToLimitColimitCone (G : J ⥤ K ⥤ C) [HasLimit G] :
    colim.mapCone (limit.cone G) ⟶ limit.cone (G ⋙ colim)
    where
  Hom :=
    colim.map (limitIsoSwapCompLim G).Hom ≫
      colimitLimitToLimitColimit (uncurry.obj G : _) ≫
        lim.map (whiskerRight (currying.unitIso.app G).inv colim)
  w' j := by
    ext1 k
    simp only [limit_obj_iso_limit_comp_evaluation_hom_π_assoc, iso.app_inv,
      ι_colimit_limit_to_limit_colimit_π_assoc, whisker_right_app, colimit.ι_map,
      functor.map_cone_π_app, category.id_comp, eq_to_hom_refl, eq_to_hom_app, colimit.ι_map_assoc,
      limit.cone_π, lim_map_π_assoc, lim_map_π, category.assoc, currying_unit_iso_inv_app_app_app,
      limit_iso_swap_comp_lim_hom_app, lim_map_eq_lim_map]
    dsimp
    simp only [category.id_comp]
    erw [limit_obj_iso_limit_comp_evaluation_hom_π_assoc]
#align category_theory.limits.colimit_limit_to_limit_colimit_cone CategoryTheory.Limits.colimitLimitToLimitColimitCone

end CategoryTheory.Limits

