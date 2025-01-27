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

-/

universe u

open CategoryTheory

namespace SSet

variable (X : SSet.{u})

/-- The complete lattice of subcomplexes of a simplicial set. -/
abbrev Subcomplex := Subpresheaf X

instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S ↦ S.toPresheaf

variable {X}

/-- If `A : Subcomplex X`, this is the inclusion `A ⟶ X` considered in the
category `SSet` (which is definitionally equal to `SimplexCategoryᵒᵖ ⥤ Type _`). -/
abbrev Subcomplex.ι (A : Subcomplex X) : Quiver.Hom (V := SSet) A X := Subpresheaf.ι A

instance (A : X.Subcomplex) :
    Mono A.ι :=
  inferInstanceAs (Mono (Subpresheaf.ι A))

end SSet
