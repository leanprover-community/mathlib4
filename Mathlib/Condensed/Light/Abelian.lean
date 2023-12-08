/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Condensed.Light.Basic

/-!

Light condensed abelian groups form an abelian category.

-/

universe u

open CategoryTheory Limits

/--
The category of condensed abelian groups, defined as sheaves of abelian groups over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondensed.{u} AddCommGroupCat.{u}

-- TODO: add the instance that implies this to `Sites/Equivalence`
instance : PreservesFiniteLimits
  (presheafToSheaf (coherentTopology LightProfinite.{u}) AddCommGroupCat.{u}) := sorry

-- TODO: use the equivalence with sheaves on an essentially small site
instance : HasLimits <| Sheaf (coherentTopology LightProfinite.{u}) AddCommGroupCat.{u} := sorry

noncomputable instance LightCondAb.abelian :
    CategoryTheory.Abelian LightCondAb.{u} := by
  letI : PreservesLimits (forget AddCommGroupCat.{u}) :=
    AddCommGroupCat.forgetPreservesLimits.{u}
  exact CategoryTheory.sheafIsAbelian (J := coherentTopology LightProfinite.{u})
    (D := AddCommGroupCat.{u})
