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

end SSet
