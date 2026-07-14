/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsLaxMonoidal

/-!
# The pushforward of presheaves of modules is lax-monoidal

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

noncomputable abbrev pushforwardOfCommRing :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{v} (S ⋙ forget₂ _ _) :=
  pushforward (Functor.whiskerRight φ (forget₂ _ _))

noncomputable instance : (pushforwardOfCommRing.{u} φ).LaxMonoidal :=
  inferInstanceAs (pushforward₀OfCommRingCat F R ⋙ restrictScalarsOfCommRing φ).LaxMonoidal

end PresheafOfModules
