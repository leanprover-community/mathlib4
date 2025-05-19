/-
Copyright (c) 2025 Emily Riehl and Dominic Verity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dominic Verity
-/
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Presheaf
/-!

# The homotopy category functor preserves binary products.

The functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is the left adjoint of a reflective subcategory
inclusion, whose right adjoint is the fully faithful `nerveFunctor : Cat ⥤ SSet`;
see `nerveAdjunction : hoFunctor ⊣ nerveFunctor`.

Both `Cat.{u, u}` and `SSet.{u}` are cartesian closed categories. This files proves that
`hoFunctor` preserves binary cartesian products; note it fails to preserve infinite products.

-/

namespace CategoryTheory

universe u v

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve

/-- The Yoneda embedding from the `SimplexCategory` into simplicial sets is naturally
isomorphic to `SimplexCategory.toCat ⋙ nerveFunctor` with component isomorphisms
`Δ[n] ≅ nerve (Fin (n + 1))`. -/
def simplexIsNerve (n : ℕ) : Δ[n] ≅ nerve (Fin (n + 1)) := sorry

/-- Via the whiskered counit (or unit) of `nerveAdjunction`, the triple composite
`nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor` is naturally isomorphic to `nerveFunctor`.
As `nerveFunctor` is a right adjoint, this functor preserves binary products.
Note Mathlib does not seem to recognize that `Cat.{v, u}` has binary products. -/
instance nerveHoNerve.binaryProductIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  sorry

/-- This proof can surely be golfed. -/
instance hoFunctor.binaryProductNerveIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison nerveFunctor
      (hoFunctor.obj (nerve C)) (hoFunctor.obj (nerve D))) := inferInstance
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) := by
      have eq := prodComparison_comp
        nerveFunctor (hoFunctor ⋙ nerveFunctor) (A := Cat.of C) (B := Cat.of D)
      simp only [nerveFunctor_obj] at eq
      have : IsIso
        ((hoFunctor ⋙ nerveFunctor).map
          (prodComparison nerveFunctor (Cat.of C) (Cat.of D))) := inferInstance
      exact IsIso.of_isIso_fac_left eq.symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  apply isIso_of_fully_faithful nerveFunctor

/-- By `simplexIsNerve` this is isomorphic to a map of the form
`hoFunctor.binaryProductNerveIsIso`. -/
instance hoFunctor.binarySimplexProductIsIso (n m : ℕ) :
    IsIso (prodComparison hoFunctor Δ[n] Δ[m]) := sorry

/-- Modulo composing with a symmetry on both ends, the natural transformation
`prodComparisonNatTrans hofunctor Δ[m]` is a natural transformation between cocontinuous
functors whose component at `X : SSet` is `prodComparison hoFunctor X Δ[m]`. This makes use
of cartesian closure of both `SSet.{u}` and `Cat.{u,u}` to establish cocontinuity of the
product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) X` this reduces to
the result proven in `hoFunctor.binarySimplexProductIsIso`. Note we only found the
colimit formula for simplicial sets at level 0 but this can surely be generalized.
-/
instance hoFunctor.binaryProductWithSimplexIsIso (X : SSet.{0}) (m : ℕ) :
    IsIso (prodComparison hoFunctor X Δ[m]) := by
  have Xcolim := Presheaf.colimitOfRepresentable (C := SimplexCategory) X
  sorry

/-- The natural transformation `prodComparisonNatTrans hofunctor X` is a natural
transformation between cocontinuous functors whose component at `Y : SSet` is
`prodComparison hoFunctor X Y`. This makes use of cartesian closure of both `SSet.{u}`
and `Cat.{u,u}` to establish cocontinuity of the product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) Y` this reduces to
the result proven in `hoFunctor.binaryProductWithSimplexIsIso`. Note we only found the
colimit formula for simplicial sets at level 0 but this can surely be generalized.
-/
instance hoFunctor.binaryProductIsIsoLevelZero (X : SSet) (Y : SSet.{0}) :
    IsIso (prodComparison hoFunctor X Y) := by
  unfold SSet SimplicialObject at X Y
  have Ycolim := Presheaf.colimitOfRepresentable (C := SimplexCategory) Y
  have := prodComparisonNatTrans hoFunctor X
  sorry

/-- The same argument used in `hoFunctor.binaryProductIsIsoLevelZero` should work here
once the universe errors are fixed. -/
instance hoFunctor.binaryProductIsIso (X Y : SSet) :
    IsIso (prodComparison hoFunctor X Y) := sorry

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial sets
`X` and `Y`. -/
instance hoFunctor.preservesBinaryProducts (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of functors
out of `Discrete Limits.WalkingPair`. -/
instance hoFunctor.preservesBinaryProducts' :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) hoFunctor where
  preservesLimit :=
    fun {F} ↦ preservesLimit_of_iso_diagram hoFunctor (id (diagramIsoPair F).symm)

/--
QCat is the category of quasi-categories defined as the full subcategory of the category of `SSet`.
-/
def QCat := ObjectProperty.FullSubcategory Quasicategory
instance : Category QCat := ObjectProperty.FullSubcategory.category Quasicategory

/-- As objects characterized by a right lifting property, it is straightforward to directly
verify that. -/
instance QCat.hasBinaryProducts : HasBinaryProducts QCat := sorry

/-- The construction above should form the product in the category `SSet` and verify that this
object is a quasi-category. -/
instance QCat.inclusionPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete Limits.WalkingPair) (ObjectProperty.ι Quasicategory) := sorry

end CategoryTheory
