/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# The category of sheaves of modules is abelian

-/

universe v v' u u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace PresheafOfModules

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.val)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

-- some of these instances may be moved in a better place

noncomputable instance :
     PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _) :=
  compPreservesFiniteLimits (SheafOfModules.forget.{v} R) (toPresheaf R.val)

noncomputable instance : (sheafToPresheaf J AddCommGroupCat.{v}).ReflectsIsomorphisms :=
  (fullyFaithfulSheafToPresheaf J AddCommGroupCat).reflectsIsomorphisms

noncomputable instance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R) :=
  preservesFiniteLimitsOfReflectsOfPreserves _ (sheafToPresheaf _ _)

instance : (SheafOfModules.forget.{v} R).ReflectsIsomorphisms :=
  (SheafOfModules.fullyFaithfulForget.{v} R).reflectsIsomorphisms

instance : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms

instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_comp' (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)

noncomputable instance : ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R) where
  reflects _ _ _ := inferInstance

variable [HasSheafify J AddCommGroupCat.{v}] [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

noncomputable instance :
    PreservesFiniteLimits (sheafification.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
  compPreservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGroupCat)

noncomputable instance : PreservesFiniteLimits (sheafification.{v} α) :=
  preservesFiniteLimitsOfReflectsOfPreserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

end PresheafOfModules

namespace SheafOfModules

variable (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGroupCat.{v}]
  [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

noncomputable instance : Abelian (SheafOfModules.{v} R) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.val)
  exact abelianOfAdjunction _ _ (asIso (adj.counit)) adj

end SheafOfModules
