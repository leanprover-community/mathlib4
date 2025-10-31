/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/

import Mathlib.CategoryTheory.Bicategory.CatEnriched
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# The strict bicategory of quasicategories

In this file we define a strict bicategory whose objects are quasicategories,
whose `1`-morphisms are maps of simplicial sets, and whose `2`-morphisms are homotopy classes of
homotopies between them, defined using the simplicial interval `Δ[1]`.

This is defined by transfering the simplicial enrichment of the category of quasicategories to
a categorical enrichment by applying `hoFunctor : SSet ⥤ Cat` to the hom-objects.

This strict bicategory serves as a setting to develop the formal category theory of quasicategories.

## References

* [Emily Riehl and Dominic Verity, Elements of ∞-Category Theory][RiehlVerity2022]
* [Emily Riehl and Dominic Verity, The 2-category theory of quasi-categories][RiehlVerity2015]

-/

universe u

namespace SSet

open CategoryTheory Simplicial

/-- `QCat` is the category of quasi-categories defined as the full subcategory of the category
`SSet` of simplicial sets. -/
abbrev QCat := ObjectProperty.FullSubcategory Quasicategory

/-- `QCat` is the category of quasi-categories defined as the full subcategory of the category
`SSet` of simplicial sets. -/
instance : Category QCat := ObjectProperty.FullSubcategory.category Quasicategory

/-- As a full subcategory of `SSet`, the category `QCat` is a simplicially enriched ordinary
category. -/
instance QCat.SimplicialCat : SimplicialCategory QCat where
  Hom X Y := X.obj.functorHom Y.obj
  id X := Functor.natTransEquiv.symm (𝟙 X.obj)
  comp X Y Z := { app := fun _ ⟨f, g⟩ => f.comp g }
  homEquiv := Functor.natTransEquiv.symm

/-- `QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunctor` to the
hom objects in its `SSet`-enriched ordinary structure. -/
noncomputable instance QCat.CatEnrichedOrdinaryCat : EnrichedOrdinaryCategory Cat QCat :=
  TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor hoFunctor_pro_normal_monoidal

/-- The underlying category of the `Cat`-enriched ordinary category of quasicategories is
equivalent to `QCat`. -/
noncomputable def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

/-- The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance QCat.bicategory : Bicategory QCat :=
  CatEnrichedOrdinary.instBicategory

/-- The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance QCat.strictBicategory : Bicategory.Strict QCat :=
  CatEnrichedOrdinary.instStrict

end SSet
