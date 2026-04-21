/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Bicategory.CatEnriched
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
# The strict bicategory of quasicategories

In this file we define a strict bicategory `QCat.strictBicategory` whose objects
are quasicategories.

This strict category is defined from `QCat.catEnrichedOrdinaryCategory` which is
the `Cat`-enriched ordinary category of quasicategories whose hom-categories are the
homotopy categories of the simplicial internal homs, defined by
applying `hoFunctor : SSet ⥤ Cat`.

As an enriched ordinary category, there is an equivalence `QCat.forgetEnrichment.equiv`
between the underlying category and the full subcategory of quasicategories. Thus the
`1`-morphisms of `QCat.strictBicategory` are maps of simplicial sets.

Future work will use the fact that quasicategories define a cartesian closed subcategory
of simplicial sets to identify the `2`-morphisms of `QCat.strictBicategory` with
homotopy classes of homotopies between them, defined using the simplicial interval `Δ[1]`.

This strict bicategory serves as a setting to develop the formal category theory of quasicategories.

## References

* [Emily Riehl and Dominic Verity, Elements of ∞-Category Theory][RiehlVerity2022]
* [Emily Riehl and Dominic Verity, The 2-category theory of quasi-categories][RiehlVerity2015]

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial

/-- `QCat` is the category of quasi-categories defined as the full subcategory of the category
`SSet` of simplicial sets. -/
abbrev QCat := ObjectProperty.FullSubcategory Quasicategory

/-- `QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunctor` to the
hom objects in its `SSet`-enriched ordinary structure. -/
instance QCat.catEnrichedOrdinaryCategory : EnrichedOrdinaryCategory Cat QCat :=
  TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor.{u}
    (hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
      (congrArg (Functor.toCatHom) <| hoFunctor.unitHomEquiv_eq · ·)

/-- The underlying category of the `Cat`-enriched ordinary category of quasicategories is
equivalent to `QCat`. -/
def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

/-- The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
instance QCat.bicategory : Bicategory QCat :=
  CatEnrichedOrdinary.instBicategory

/-- The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
instance QCat.strictBicategory : Bicategory.Strict QCat :=
  CatEnrichedOrdinary.instStrict

end SSet
