/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Strict
import Mathlib.CategoryTheory.Products.Basic


namespace CategoryTheory.Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

-- TODO: notation for pseudofunctors

-- TODO: clean up Proucts.Basic file

/-- The product of two bicategories. -/
@[simps (notRecursive := [])] -- TODO
instance prod : Bicategory (B × C) where
  Hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := ⟨𝟙 X.1, 𝟙 X.2⟩
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  homCategory X Y := CategoryTheory.prod (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := ⟨f.1 ◁ θ.1, f.2 ◁ θ.2⟩
  whiskerRight θ g := ⟨θ.1 ▷ g.1, θ.2 ▷ g.2⟩
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (λ_ f.1) (λ_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  whisker_exchange η θ := Prod.ext (whisker_exchange η.1 θ.1) (whisker_exchange η.2 θ.2)

namespace Prod

/-- `sectL C c` is the pseudofunctor `B ⥤ B × C` given by `X ↦ (X, c)`. -/
@[simps!]
def sectL (c : C) : StrictlyUnitaryPseudofunctor B (B × C) := .mk'
  { obj X := (X, c)
    map f := (f, 𝟙 c)
    map₂ η := (η, 𝟙 _)
    map_id f := rfl
    mapComp f g := Iso.prod (Iso.refl _) (λ_ (g, 𝟙 c).2).symm }

/-- `sectR Z D` is the pseudofunctor `B ⥤ B × C` given by `Y ↦ (c, Y)`. -/
@[simps!]
def sectR (b : B) : StrictlyUnitaryPseudofunctor C (B × C) := .mk'
  { obj Y := (b, Y)
    map f := (𝟙 b, f)
    map₂ η := (𝟙 _, η)
    map_id f := rfl
    mapComp f g := Iso.prod (ρ_ (𝟙 b)).symm (Iso.refl _) }

/-- `fst` is the functor `(X, Y) ↦ X`. -/
@[simps!]
def fst : StrictPseudofunctor (B × C) B := .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 } -- TODO: check that map_id and map_comp are dsimp lemmas

/-- `snd` is the functor `(X, Y) ↦ Y`. -/
@[simps!]
def snd : StrictPseudofunctor (B × C) C := .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

/-- The pseudofunctor swapping the factors of a Cartesian product of bicategories,
`B × C ⥤ C × B`. -/
@[simps!]
def swap : StrictPseudofunctor (B × C) (C × B) := .mk'
  { obj X := (X.2, X.1)
    map f := (f.2, f.1)
    map₂ η := (η.2, η.1) }

end Prod

end CategoryTheory.Bicategory
