/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.over from "leanprover-community/mathlib"@"3e0dd193514c9380edc69f1da92e80c02713c41d"

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : Over X ⥤ C` creates colimits, and hence `Over X` has
any colimits that `C` has (as well as the dual that `forget X : Under X ⟶ C` creates limits).

Note that the folder `CategoryTheory.Limits.Shapes.Constructions.Over` further shows that
`forget X : Over X ⥤ C` creates connected limits (so `Over X` has connected limits), and that
`Over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.
-/


noncomputable section

-- morphism levels before object levels. See note [category_theory universes].
universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

instance hasColimit_of_hasColimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)] :
    HasColimit F :=
  CostructuredArrow.hasColimit (i₁ := i)
#align category_theory.over.has_colimit_of_has_colimit_comp_forget CategoryTheory.Over.hasColimit_of_hasColimit_comp_forget

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Over X) where

instance [HasColimits C] : HasColimits (Over X) :=
  ⟨inferInstance⟩

instance createsColimitsOfSize : CreatesColimitsOfSize.{w, w'} (forget X) :=
  CostructuredArrow.createsColimitsOfSize
#align category_theory.over.creates_colimits CategoryTheory.Over.createsColimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
example [HasColimits C] : PreservesColimits (forget X) :=
  inferInstance

example : ReflectsColimits (forget X) :=
  inferInstance

theorem epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h.left :=
  CostructuredArrow.epi_left_of_epi _
#align category_theory.over.epi_left_of_epi CategoryTheory.Over.epi_left_of_epi

theorem epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi h.left :=
  CostructuredArrow.epi_iff_epi_left _
#align category_theory.over.epi_iff_epi_left CategoryTheory.Over.epi_iff_epi_left

instance createsColimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesColimitsOfSize.{w, w'} (map f ⋙ forget Y) :=
  show CreatesColimitsOfSize.{w, w'} (forget X) from inferInstance

instance preservesColimitsOfSizeMap [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{w, w'} (map f) :=
  preservesColimitsOfReflectsOfPreserves (map f) (forget Y)

/-- If `c` is a colimit cocone, then so is the cocone `c.toOver` with cocone point `𝟙 c.pt`. -/
def isColimitToOver {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsColimit c.toOver :=
  isColimitOfReflects (forget c.pt) <| IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

/-- If `F` has a colimit, then the cocone `colimit.toOver F` with cocone point `𝟙 (colimit F)` is
    also a colimit cocone. -/
def _root_.CategoryTheory.Limits.colimit.isColimitToOver (F : J ⥤ C) [HasColimit F] :
    IsColimit (colimit.toOver F) :=
  Over.isColimitToOver (colimit.isColimit F)

end CategoryTheory.Over

namespace CategoryTheory.Under

instance hasLimit_of_hasLimit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)] :
    HasLimit F :=
  StructuredArrow.hasLimit (i₁ := i)
#align category_theory.under.has_limit_of_has_limit_comp_forget CategoryTheory.Under.hasLimit_of_hasLimit_comp_forget

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Under X) where

instance [HasLimits C] : HasLimits (Under X) :=
  ⟨inferInstance⟩

theorem mono_right_of_mono [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h] : Mono h.right :=
  StructuredArrow.mono_right_of_mono _
#align category_theory.under.mono_right_of_mono CategoryTheory.Under.mono_right_of_mono

theorem mono_iff_mono_right [HasPullbacks C] {f g : Under X} (h : f ⟶ g) : Mono h ↔ Mono h.right :=
  StructuredArrow.mono_iff_mono_right _
#align category_theory.under.mono_iff_mono_right CategoryTheory.Under.mono_iff_mono_right

instance createsLimitsOfSize : CreatesLimitsOfSize.{w, w'} (forget X) :=
  StructuredArrow.createsLimitsOfSize
#align category_theory.under.creates_limits CategoryTheory.Under.createsLimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects limits.
example [HasLimits C] : PreservesLimits (forget X) :=
  inferInstance

example : ReflectsLimits (forget X) :=
  inferInstance

instance createLimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesLimitsOfSize.{w, w'} (map f ⋙ forget X) :=
  show CreatesLimitsOfSize.{w, w'} (forget Y) from inferInstance

instance preservesLimitsOfSizeMap [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesLimitsOfSize.{w, w'} (map f) :=
  preservesLimitsOfReflectsOfPreserves (map f) (forget X)

/-- If `c` is a limit cone, then so is the cone `c.toUnder` with cone point `𝟙 c.pt`. -/
def isLimitToUnder {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) : IsLimit c.toUnder :=
  isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

/-- If `F` has a limit, then the cone `limit.toUnder F` with cone point `𝟙 (limit F)` is
    also a limit cone. -/
def _root_.CategoryTheory.Limits.limit.isLimitToOver (F : J ⥤ C) [HasLimit F] :
    IsLimit (limit.toUnder F) :=
  Under.isLimitToUnder (limit.isLimit F)

end CategoryTheory.Under
