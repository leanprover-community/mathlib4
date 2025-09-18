/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Subpresheaf.Basic

/-!
# Subcomplexes of a simplicial set

Given a simplicial set `X`, this file defines the type `X.Subcomplex`
of subcomplexes of `X` as an abbreviation for `Subpresheaf X`.
It also introduces a coercion from `X.Subcomplex` to `SSet`.

## Implementation note

`SSet.{u}` is defined as `Cᵒᵖ ⥤ Type u`, but it is not an abbreviation.
This is the reason why `Subpresheaf.ι` is redefined here as `Subcomplex.ι`
so that this morphism appears as a morphism in `SSet` instead of a morphism
in the category of presheaves.

-/

universe u

open CategoryTheory

namespace SSet

variable (X : SSet.{u})

/-- The complete lattice of subcomplexes of a simplicial set. -/
abbrev Subcomplex := Subpresheaf X

variable {X}

/-- The underlying simplicial set of a subcomplex. -/
abbrev Subcomplex.toSSet (A : X.Subcomplex) : SSet.{u} := A.toPresheaf

instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S ↦ S.toSSet

/-- If `A : Subcomplex X`, this is the inclusion `A ⟶ X` in the category `SSet`. -/
abbrev Subcomplex.ι (A : Subcomplex X) : Quiver.Hom (V := SSet) A X := Subpresheaf.ι A

instance (A : X.Subcomplex) : Mono A.ι :=
  inferInstanceAs (Mono (Subpresheaf.ι A))

end SSet
