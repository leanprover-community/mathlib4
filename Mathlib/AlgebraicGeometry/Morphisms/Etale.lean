/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!

# Etale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if it is smooth of relative dimension zero. We
also define the category of schemes étale over `X`.

-/

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes is étale if it is smooth of relative dimension zero. -/
abbrev IsEtale {X Y : Scheme.{u}} (f : X ⟶ Y) := IsSmoothOfRelativeDimension 0 f

namespace IsEtale

variable {X : Scheme.{u}}

instance : IsStableUnderBaseChange @IsEtale :=
  isSmoothOfRelativeDimension_isStableUnderBaseChange 0

end IsEtale

/-- The category `Etale X` is the category of schemes étale over `X`. -/
def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @IsEtale ⊤ X

variable (X : Scheme.{u})

instance : Category (Etale X) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsEtale ⊤ X)

/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
def Etale.forget : Etale X ⥤ Over X :=
  MorphismProperty.Over.forget @IsEtale ⊤ X

/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (Etale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (Etale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

end AlgebraicGeometry
