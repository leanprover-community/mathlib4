/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Existence of limits deduced from adjunctions

Let `adj : F ⊣ G` be an adjunction.

If `G : D ⥤ C` is fully faithful (i.e. `G` is reflective),
then colimits of shape `J` exist in `D` if they exist in `C`.

If `F : C ⥤ D` is fully faithful (i.e. `F` is coreflective),
then limits of shape `J` exist in `C` if they exist in `D`.

-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits Functor

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

lemma hasColimitsOfShape [G.Full] [G.Faithful]
    (J : Type*) [Category J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D :=
  letI : Reflective G := ⟨_, adj⟩
  hasColimitsOfShape_of_reflective G

lemma hasLimitsOfShape [F.Full] [F.Faithful]
    (J : Type*) [Category J] [HasLimitsOfShape J D] :
    HasLimitsOfShape J C :=
  letI : Coreflective F := ⟨_, adj⟩
  hasLimitsOfShape_of_coreflective F

end CategoryTheory.Adjunction
