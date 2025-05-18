/-
Copyright (c) 2025 Emily Riehl and Dominic Verity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dominic Verity
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Presheaf
/-!

# The homotopy category functor preserves binary products.
-/

namespace CategoryTheory

universe u

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve

-- TODO: Is this in mathlib?
def simplexIsNerve (n : ℕ) : Δ[n] ≅ nerve (Fin (n + 1)) := sorry

-- TODO: Replace both representables with nerves of categories. Then apply the fully
-- faithful nerve functor. The map in queestion is then isomorphic to
-- `prodComparion nerve ⋙ hoFunctor ⋙ nerve (Fin (n + 1)) (Fin (m + 1))` which is iso to
-- `prodComparion nerve (Fin (n + 1)) (Fin (m + 1))` which is an isomorphism because the
-- nerve preserves products.
instance hoFunctor.binarySimplexProductIsIso (n m : ℕ) :
    IsIso (prodComparison hoFunctor Δ[n] Δ[m]) := sorry

-- TODO: Use the fact that the domain and codomain of the natural transformation
instance hoFunctor.binaryProductWithSimplexIsIso (X : SSet.{0}) (m : ℕ) :
    IsIso (prodComparison hoFunctor X Δ[m]) := by
  have Xcolim := Presheaf.colimitOfRepresentable (C := SimplexCategory) X
--  have := prodComparisonNatTrans hoFunctor Δ[m]
  sorry

-- TODO: Reduce this to the previous case using the fact that this is a component of a
-- a natural transformation between functors that preserve colimits.
instance hoFunctor.binaryProductIsIsoLevelZero (X : SSet) (Y : SSet.{0}) :
    IsIso (prodComparison hoFunctor X Y) := by
  unfold SSet SimplicialObject at X Y
  have Ycolim := Presheaf.colimitOfRepresentable (C := SimplexCategory) Y
  have := prodComparisonNatTrans hoFunctor X
  sorry

-- TODO: Fix universe error.
-- Presheaf.colimitOfRepresentable requires a functor valued in
--  `Type u` to be indexed by a category whose morphism level is `u`.
-- have := Presheaf.colimitOfRepresentable.{_, u} (C := SimplexCategory) X
instance hoFunctor.binaryProductIsIso (X Y : SSet) :
    IsIso (prodComparison hoFunctor X Y) := sorry

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of
simplicial sets `X` and `Y`. -/
instance hoFunctor.preservesBinaryProducts (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of functors
out of `Discrete Limits.WalkingPair`. -/
instance hoFunctor.preservesBinaryProducts' :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) hoFunctor where
  preservesLimit :=
    fun {F} ↦ preservesLimit_of_iso_diagram hoFunctor (id (diagramIsoPair F).symm)

end CategoryTheory
