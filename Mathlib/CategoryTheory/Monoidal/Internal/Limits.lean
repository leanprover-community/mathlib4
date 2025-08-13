/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits of monoid objects.

If `C` has limits (of a given shape), so does `Mon_ C`,
and the forgetful functor preserves these limits.

(This could potentially replace many individual constructions for concrete categories,
in particular `MonCat`, `SemiRingCat`, `RingCat`, and `AlgCat R`.)
-/


open CategoryTheory Limits Monoidal MonoidalCategory

universe v u w

noncomputable section

namespace Mon_

variable {J : Type w} [SmallCategory J]
variable {C : Type u} [Category.{v} C] [HasLimitsOfShape J C] [MonoidalCategory.{v} C]

/-- We construct the (candidate) limit of a functor `F : J ⥤ Mon_ C`
by interpreting it as a functor `Mon_ (J ⥤ C)`,
and noting that taking limits is a lax monoidal functor,
and hence sends monoid objects to monoid objects.
-/
@[simps!]
def limit (F : J ⥤ Mon_ C) : Mon_ C :=
  lim.mapMon.obj ((monFunctorCategoryEquivalence J C).inverse.obj F)

/-- Implementation of `Mon_.hasLimits`: a limiting cone over a functor `F : J ⥤ Mon_ C`.
-/
@[simps]
def limitCone (F : J ⥤ Mon_ C) : Cone F where
  pt := limit F
  π :=
    { app := fun j => .mk' (limit.π (F ⋙ Mon_.forget C) j)
      naturality := fun j j' f => by ext; exact (limit.cone (F ⋙ Mon_.forget C)).π.naturality f }

/-- The image of the proposed limit cone for `F : J ⥤ Mon_ C` under the forgetful functor
`forget C : Mon_ C ⥤ C` is isomorphic to the limit cone of `F ⋙ forget C`.
-/
def forgetMapConeLimitConeIso (F : J ⥤ Mon_ C) :
    (forget C).mapCone (limitCone F) ≅ limit.cone (F ⋙ forget C) :=
  Cones.ext (Iso.refl _) (by simp)

/-- Implementation of `Mon_.hasLimitsOfShape`:
the proposed cone over a functor `F : J ⥤ Mon_ C` is a limit cone.
-/
@[simps]
def limitConeIsLimit (F : J ⥤ Mon_ C) : IsLimit (limitCone F) where
  lift s :=
    { hom := limit.lift (F ⋙ Mon_.forget C) ((Mon_.forget C).mapCone s)
      is_mon_hom :=
        { mul_hom := limit.hom_ext (fun j ↦ by
          dsimp
          simp only [Category.assoc, limit.lift_π, Functor.mapCone_pt, forget_obj,
            Functor.mapCone_π_app, forget_map, IsMon_Hom.mul_hom, limMap_π, tensorObj_obj,
            Functor.comp_obj, MonFunctorCategoryEquivalence.inverseObj_mon_mul_app, lim_μ_π_assoc,
            lim_obj, ← tensor_comp_assoc]) } }
  fac s h := by ext; simp
  uniq s m w := by
    ext1
    refine limit.hom_ext (fun j => ?_)
    dsimp; simp only [Mon_.forget_map, limit.lift_π, Functor.mapCone_π_app]
    exact congr_arg Mon_.Hom.hom (w j)

instance hasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (Mon_ C) where
  has_limit := fun F => HasLimit.mk
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

instance forget_preservesLimitsOfShape : PreservesLimitsOfShape J (Mon_.forget C) where
  preservesLimit := fun {F} =>
    preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
      (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Mon_.forget C)) (forgetMapConeLimitConeIso F).symm)

end Mon_
