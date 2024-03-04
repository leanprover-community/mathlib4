/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Condensed.Basic

/-!

Condensed abelian groups form an abelian category.

-/

universe u

open CategoryTheory Limits

/--
The category of condensed abelian groups, defined as sheaves of abelian groups over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedAb := Condensed.{u} AddCommGrp.{u+1}

noncomputable instance CondensedAb.abelian :
    CategoryTheory.Abelian CondensedAb.{u} :=
  letI : PreservesLimits (forget AddCommGrp.{u+1}) :=
    AddCommGrp.forgetPreservesLimits.{u+1}
  CategoryTheory.sheafIsAbelian
