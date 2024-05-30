/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.monoidal.internal.limits from "leanprover-community/mathlib"@"12921e9eaa574d0087ae4856860e6dda8690a438"

/-!
# Limits of monoid objects.

If `C` has limits, so does `Mon_ C`, and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `MonCat`, `SemiRingCat`, `RingCat`, and `AlgebraCat R`.)
-/


open CategoryTheory Limits Monoidal

universe v u

noncomputable section

namespace Mon_

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasLimits C] [MonoidalCategory.{v} C]

/-- We construct the (candidate) limit of a functor `F : J ⥤ Mon_ C`
by interpreting it as a functor `Mon_ (J ⥤ C)`,
and noting that taking limits is a lax monoidal functor,
and hence sends monoid objects to monoid objects.
-/
@[simps!]
def limit (F : J ⥤ Mon_ C) : Mon_ C :=
  limLax.mapMon.obj (MonFunctorCategoryEquivalence.inverse.obj F)
set_option linter.uppercaseLean3 false in
#align Mon_.limit Mon_.limit

/-- Implementation of `Mon_.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon_ C`.
-/
@[simps]
def limitCone (F : J ⥤ Mon_ C) : Cone F where
  pt := limit F
  π :=
    { app := fun j => { hom := limit.π (F ⋙ Mon_.forget C) j }
      naturality := fun j j' f => by ext; exact (limit.cone (F ⋙ Mon_.forget C)).π.naturality f }
set_option linter.uppercaseLean3 false in
#align Mon_.limit_cone Mon_.limitCone

/-- The image of the proposed limit cone for `F : J ⥤ Mon_ C` under the forgetful functor
`forget C : Mon_ C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
def forgetMapConeLimitConeIso (F : J ⥤ Mon_ C) :
    (forget C).mapCone (limitCone F) ≅ limit.cone (F ⋙ forget C) :=
  Cones.ext (Iso.refl _) (by aesop_cat)
set_option linter.uppercaseLean3 false in
#align Mon_.forget_map_cone_limit_cone_iso Mon_.forgetMapConeLimitConeIso

/-- Implementation of `Mon_.hasLimits`:
the proposed cone over a functor `F : J ⥤ Mon_ C` is a limit cone.
-/
@[simps]
def limitConeIsLimit (F : J ⥤ Mon_ C) : IsLimit (limitCone F) where
  lift s :=
    { hom := limit.lift (F ⋙ Mon_.forget C) ((Mon_.forget C).mapCone s)
      mul_hom := by
        dsimp
        ext
        simp only [Functor.comp_obj, forget_obj, Category.assoc, limit.lift_π, Functor.mapCone_pt,
          Functor.mapCone_π_app, forget_map, Hom.mul_hom, limit_mul, Cones.postcompose_obj_pt,
          Cones.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, tensorObj_obj,
          MonFunctorCategoryEquivalence.Inverse.obj_mul_app]
        slice_rhs 1 2 => rw [← MonoidalCategory.tensor_comp, limit.lift_π]
        rfl }
  fac s h := by ext; simp
  uniq s m w := by
    ext1
    refine limit.hom_ext (fun j => ?_)
    dsimp; simp only [Mon_.forget_map, limit.lift_π, Functor.mapCone_π_app]
    exact congr_arg Mon_.Hom.hom (w j)
set_option linter.uppercaseLean3 false in
#align Mon_.limit_cone_is_limit Mon_.limitConeIsLimit

instance hasLimits : HasLimits (Mon_ C) where
  has_limits_of_shape _ _ :=
    { has_limit := fun F =>
        HasLimit.mk
          { cone := limitCone F
            isLimit := limitConeIsLimit F } }
set_option linter.uppercaseLean3 false in
#align Mon_.has_limits Mon_.hasLimits

instance forgetPreservesLimits : PreservesLimits (Mon_.forget C) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Mon_.forget C))
            (forgetMapConeLimitConeIso F).symm) }
set_option linter.uppercaseLean3 false in
#align Mon_.forget_preserves_limits Mon_.forgetPreservesLimits

end Mon_
