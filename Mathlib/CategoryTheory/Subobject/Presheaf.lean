/-
Copyright (c) 2025 Pablo Donato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Subobjects presheaf

Following Section I.3 of [Sheaves in Geometry and Logic][MM92], we define the subobjects presheaf
`Subobject.presheaf C` mapping any object `X` to its type of subobjects `Subobject X`.

## Main definitions

Let `C` refer to a category with pullbacks.

* `CategoryTheory.Subobject.presheaf C` is the presheaf that sends every object `X : C` to its type
  of subobjects `Subobject X`, and every morphism `f : X ⟶ Y` to the function `Subobject Y →
  Subobject X` that maps every subobject of `Y` to its pullback along `f`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in geometry and logic: A first introduction to topos
  theory*][MM92]

## Tags

subobject, representable functor, presheaf, topos theory
-/

open CategoryTheory Subobject

namespace Subobject

universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasPullbacks C]

/-- This is the presheaf that sends every object `X : C` to its type of subobjects `Subobject X`,
    and every morphism `f : X ⟶ Y` to the function `Subobject Y → Subobject X` that maps every
    subobject of `Y` to its pullback along `f`. -/
@[simps]
noncomputable def presheaf : Cᵒᵖ ⥤ Type max u v where
  obj X := Subobject X.unop
  map f := (pullback f.unop).obj
  map_id _ := by ext : 1; simp [pullback_id]
  map_comp _ _ := by ext : 1; simp [pullback_comp]

end Subobject
