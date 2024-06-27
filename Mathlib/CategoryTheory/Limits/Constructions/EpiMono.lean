/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

#align_import category_theory.limits.constructions.epi_mono from "leanprover-community/mathlib"@"f7baecbb54bd0f24f228576f97b1752fc3c9b318"

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (F : C ⥤ D)

/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
theorem preserves_mono_of_preservesLimit {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F]
    [Mono f] : Mono (F.map f) := by
  have := isLimitPullbackConeMapOfIsLimit F _ (PullbackCone.isLimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ this
#align category_theory.preserves_mono_of_preserves_limit CategoryTheory.preserves_mono_of_preservesLimit

instance (priority := 100) preservesMonomorphisms_of_preservesLimitsOfShape
    [PreservesLimitsOfShape WalkingCospan F] : F.PreservesMonomorphisms where
  preserves f _ := preserves_mono_of_preservesLimit F f
#align category_theory.preserves_monomorphisms_of_preserves_limits_of_shape CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono_of_reflectsLimit {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F]
    [Mono (F.map f)] : Mono f := by
  have := PullbackCone.isLimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ (isLimitOfIsLimitPullbackConeMap F _ this)
#align category_theory.reflects_mono_of_reflects_limit CategoryTheory.reflects_mono_of_reflectsLimit

instance (priority := 100) reflectsMonomorphisms_of_reflectsLimitsOfShape
    [ReflectsLimitsOfShape WalkingCospan F] : F.ReflectsMonomorphisms where
  reflects f _ := reflects_mono_of_reflectsLimit F f
#align category_theory.reflects_monomorphisms_of_reflects_limits_of_shape CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape

/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
theorem preserves_epi_of_preservesColimit {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F]
    [Epi f] : Epi (F.map f) := by
  have := isColimitPushoutCoconeMapOfIsColimit F _ (PushoutCocone.isColimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PushoutCocone.epi_of_isColimitMkIdId _ this
#align category_theory.preserves_epi_of_preserves_colimit CategoryTheory.preserves_epi_of_preservesColimit

instance (priority := 100) preservesEpimorphisms_of_preservesColimitsOfShape
    [PreservesColimitsOfShape WalkingSpan F] : F.PreservesEpimorphisms where
  preserves f _ := preserves_epi_of_preservesColimit F f
#align category_theory.preserves_epimorphisms_of_preserves_colimits_of_shape CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape

/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
theorem reflects_epi_of_reflectsColimit {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F]
    [Epi (F.map f)] : Epi f := by
  have := PushoutCocone.isColimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply
    PushoutCocone.epi_of_isColimitMkIdId _
      (isColimitOfIsColimitPushoutCoconeMap F _ this)
#align category_theory.reflects_epi_of_reflects_colimit CategoryTheory.reflects_epi_of_reflectsColimit

instance (priority := 100) reflectsEpimorphisms_of_reflectsColimitsOfShape
    [ReflectsColimitsOfShape WalkingSpan F] : F.ReflectsEpimorphisms where
  reflects f _ := reflects_epi_of_reflectsColimit F f
#align category_theory.reflects_epimorphisms_of_reflects_colimits_of_shape CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape

end CategoryTheory
