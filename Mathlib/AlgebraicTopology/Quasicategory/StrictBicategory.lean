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
whose morphisms are maps of simplicial sets, and whose morphisms are homotopy classes of homotopies
between them, defined using the simplicial interval `Δ[1]`.

This is defined by transfering the simplicial enrichment of the category of quasicategories to
a categorical enrichment by applying `hoFunctor : SSet ⥤ Cat` to the hom-objects.

This strict bicategory serves as a setting to develop the formal category theory of quasicategories.

## References

* Emily Riehl and Dominic Verity, Elements of ∞-Category Theory
* Emily Riehl and Dominic Verity, The 2-category theory of quasi-categories

-/

universe u

namespace SSet

open CategoryTheory Simplicial MonoidalCategory

/-- `QCat` is the category of quasi-categories defined as the full subcategory of the category
`SSet` of simplicial sets. -/
def QCat := ObjectProperty.FullSubcategory Quasicategory

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

theorem hoFunctor_normal (X : SSet.{u}) : Function.Bijective
    fun (f : 𝟙_ SSet ⟶ X) => Functor.LaxMonoidal.ε hoFunctor ≫ hoFunctor.map f := by
  refine Function.bijective_iff_has_inverse.mpr ⟨?_, ?_, ?_⟩
  · intro F
    let eq₁ : 𝟙_ Cat ⥤ (hoFunctor.obj X) ≃ hoFunctor.obj X :=
      Cat.fromChosenTerminalEquiv.{u,u, u,u} (C := hoFunctor.obj X)
    let thing := eq₁.toFun F
    let eq₂ : (𝟙_ SSet ⟶ X) ≃ X _⦋0⦌ := SSet.unitHomEquiv X
    let eq₃ : X _⦋0⦌ ≃ hoFunctor.obj X := sorry
    let equiv := eq₂.trans (eq₃.trans eq₁.symm)
    apply eq₂.invFun
    sorry
  · sorry
  · sorry

/-- `QCat` obtains a `Cat`-enriched ordinary category structure by applying `hoFunctor` to the
hom objects in its `SSet`-enriched ordinary structure. -/
noncomputable instance QCat.CatEnrichedOrdinaryCat : EnrichedOrdinaryCategory Cat QCat :=
  TransportEnrichment.enrichedOrdinaryCategory QCat hoFunctor hoFunctor_normal

/-- The underlying category of the `Cat`-enriched ordinary category of quasicategories is
equivalent to `QCat`. -/
noncomputable def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

/-- As a simplicially enriched ordinary category, `QCat` is a simplicially enriched category. -/
instance QCat.SSetEnrichedCat : EnrichedCategory SSet QCat :=
  QCat.SimplicialCat.toEnrichedCategory

/-- As a `Cat`-enriched ordinary category, `QCat` is a `Cat`-enriched category. -/
noncomputable instance QCat.CatEnrichedCat : EnrichedCategory Cat QCat :=
    QCat.CatEnrichedOrdinaryCat.toEnrichedCategory

end SSet


namespace CategoryTheory

open SSet

/-- The bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance QCat.bicategory : Bicategory QCat := by
  have : EnrichedOrdinaryCategory Cat (ObjectProperty.FullSubcategory Quasicategory) :=
    QCat.CatEnrichedOrdinaryCat
  apply CatEnrichedOrdinary.instBicategory

/-- The strict bicategory of quasicategories extracted from `QCat.CatEnrichedOrdinaryCat`. -/
noncomputable instance QCat.strictBicategory : Bicategory.Strict QCat := by sorry
  -- have : EnrichedOrdinaryCategory Cat (ObjectProperty.FullSubcategory Quasicategory) :=
  --    QCat.CatEnrichedOrdinaryCat
  -- CatEnrichedOrdinary.instStrict

end CategoryTheory
