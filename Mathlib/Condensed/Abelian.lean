/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.AbelianSheaf
import Mathlib.Condensed.Basic

/-!

Condensed abelian groups form an abelian category.

-/

universe u

/--
The category of condensed abelian groups, defined as sheaves of abelian groups over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedAb := Condensed.{u} AddCommGroupCat.{u+1}

noncomputable instance CondensedAb.abelian : CategoryTheory.Abelian CondensedAb :=
  CategoryTheory.AbelianSheaf.abelian _
