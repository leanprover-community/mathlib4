/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# The category of presheaves of modules is Grothendieck abelian

-/

universe u

open CategoryTheory Limits

namespace PresheafOfModules

public instance {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun J _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦ by
    have : PreservesLimit F (colim (J := J) ⋙ PresheafOfModules.toPresheaf R) := by
      apply preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    apply preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

end PresheafOfModules
