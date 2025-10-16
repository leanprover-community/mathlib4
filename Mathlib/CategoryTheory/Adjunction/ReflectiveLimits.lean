/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Existence of limits deduced from adjunctions

Let `adj : F ⊣ G` be an adjunction.

If `G : D ⥤ C` is fully faithful (i.e. `G` is reflective),
then colimits of shape `J` exist in `D` if they exist in `C`.

If `F : C ⥤ D` is fully faithful (i.e. `F` is coreflective),
then limits of shape `J` exist in `C` if they exist in `D`.

-/

namespace CategoryTheory.Adjunction

open Limits Functor

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

lemma hasColimitsOfShape [G.Full] [G.Faithful]
    (J : Type*) [Category J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D where
  has_colimit K := by
    have := adj.isLeftAdjoint
    exact ⟨_, (IsColimit.precomposeInvEquiv
      (associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso adj.counit) ≪≫ rightUnitor _) _).2
      (isColimitOfPreserves F (colimit.isColimit (K ⋙ G)))⟩

lemma hasLimitsOfShape [F.Full] [F.Faithful]
    (J : Type*) [Category J] [HasLimitsOfShape J D] :
    HasLimitsOfShape J C where
  has_limit K := by
    have := adj.isRightAdjoint
    exact ⟨_, (IsLimit.postcomposeHomEquiv
      ((associator _ _ _ ≪≫ isoWhiskerLeft _ (asIso adj.unit).symm ≪≫ rightUnitor K)) _).2
        (isLimitOfPreserves G (limit.isLimit (K ⋙ F)))⟩

end CategoryTheory.Adjunction
