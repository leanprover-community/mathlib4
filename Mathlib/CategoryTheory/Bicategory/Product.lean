/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Cartesian products of bicategories

We define the bicategory instance on `B × C` when `B` and `C` are bicategories.

We define:
* `sectL B c` : the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ ⟨X, c⟩`
* `sectR b C` : the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ ⟨b, Y⟩`
* `fst`       : the strict pseudofunctor `⟨X, Y⟩ ↦ X`
* `snd`       : the strict pseudofunctor `⟨X, Y⟩ ↦ Y`
* `swap`      : the strict pseudofunctor `B × C ⥤ C × B` given by `⟨X, Y⟩ ↦ ⟨Y, X⟩`

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Bicategory

open Prod

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- The cartesian product of two bicategories. -/
@[simps! (notRecursive := [])] -- notRecursive to generate simp lemmas like _fst and _snd
instance prod (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C] :
    Bicategory (B × C) where
  homCategory X Y := CategoryTheory.prod' (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := f.1 ◁ θ.1 ×ₘ f.2 ◁ θ.2
  whiskerRight θ g := θ.1 ▷ g.1 ×ₘ θ.2 ▷ g.2
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (λ_ f.1) (λ_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  whisker_exchange η θ := Prod.ext (whisker_exchange η.1 θ.1) (whisker_exchange η.2 θ.2)

namespace Prod

/-- `sectL B c` is the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ (X, c)`. -/
@[simps!]
def sectL (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C] (c : C) :
    StrictlyUnitaryPseudofunctor B (B × C) := .mk'
  { obj X := (X, c)
    map f := f ×ₘ 𝟙 c
    map₂ η := η ×ₘ 𝟙 _
    mapComp f g := Iso.prod (Iso.refl _) (λ_ (g, 𝟙 c).2).symm }

/-- `sectR b C` is the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ (b, Y)`. -/
@[simps!]
def sectR {B : Type u₁} [Bicategory.{w₁, v₁} B] (b : B) (C : Type u₂) [Bicategory.{w₂, v₂} C] :
    StrictlyUnitaryPseudofunctor C (B × C) := .mk'
  { obj Y := (b, Y)
    map f := 𝟙 b ×ₘ f
    map₂ η := 𝟙 _ ×ₘ η
    mapComp f g := Iso.prod (ρ_ (𝟙 b)).symm (Iso.refl _) }

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]

/-- `fst` is the strict pseudofunctor given by projection to the first factor. -/
@[simps!]
def fst : StrictPseudofunctor (B × C) B := .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 }

/-- `snd` is the strict pseudofunctor given by projection to the second factor. -/
@[simps!]
def snd : StrictPseudofunctor (B × C) C := .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

/-- The pseudofunctor swapping the factors of a cartesian product of bicategories,
`B × C ⥤ C × B`. -/
@[simps!]
def swap : StrictPseudofunctor (B × C) (C × B) := .mk'
  { obj X := (X.2, X.1)
    map f := f.2 ×ₘ f.1
    map₂ η := η.2 ×ₘ η.1 }

end Prod

section

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₁) [Bicategory.{w₁, v₁} C]

/-- `Bicategory.uniformProd B C` is an additional instance specialised so both factors have the same
universe levels. This helps typeclass resolution.
-/
instance uniformProd : Bicategory (B × C) :=
  Bicategory.prod B C

end

end CategoryTheory.Bicategory
