/-
Copyright (c) 2025 Emily Riehl and Dominic Verity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dominic Verity
-/
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Presheaf
/-!

# The homotopy category functor preserves finite products.

The functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is the left adjoint of a reflective subcategory
inclusion, whose right adjoint is the fully faithful `nerveFunctor : Cat ⥤ SSet`;
see `nerveAdjunction : hoFunctor ⊣ nerveFunctor`.

Both `Cat.{u, u}` and `SSet.{u}` are cartesian closed categories. This files proves that
`hoFunctor` preserves finite cartesian products; note it fails to preserve infinite products.

-/

namespace CategoryTheory

universe u v

open Category Functor Limits Opposite SimplexCategory Simplicial SSet

/-- Via the whiskered counit (or unit) of `nerveAdjunction`, the triple composite
`nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor` is naturally isomorphic to `nerveFunctor`.
As `nerveFunctor` is a right adjoint, this functor preserves binary products.
Note Mathlib does not seem to recognize that `Cat.{v, u}` has binary products. -/
instance nerveHoNerve.binaryProductIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  let iso : nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor ≅ nerveFunctor :=
    (nerveFunctor.associator hoFunctor nerveFunctor).symm ≪≫
      isoWhiskerRight nerveFunctorCompHoFunctorIso nerveFunctor ≪≫ nerveFunctor.leftUnitor
  exact IsIso.of_isIso_fac_right (prodComparison_naturalInNatTrans iso.hom).symm

-- This proof can probably be golfed.
instance hoFunctor.binaryProductNerveIsIso (C D : Type v) [Category.{v} C] [Category.{v} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) := by
      have eq := prodComparison_comp
        nerveFunctor (hoFunctor ⋙ nerveFunctor) (A := Cat.of C) (B := Cat.of D)
      exact IsIso.of_isIso_fac_left eq.symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  apply isIso_of_fully_faithful nerveFunctor

-- Note: `(Δ[n] : SSet.{w})` works, but I'm not sure it's the right thing to do here.
/-- By `simplexIsNerve` this is isomorphic to a map of the form
`hoFunctor.binaryProductNerveIsIso`. -/
instance hoFunctor.binarySimplexProductIsIso.{w} (n m : ℕ) :
    IsIso (prodComparison hoFunctor (Δ[n] : SSet.{w}) Δ[m]) :=
  IsIso.of_isIso_fac_right (prodComparison_natural
    hoFunctor (simplexIsNerveULiftFin.{w} n).hom (simplexIsNerveULiftFin m).hom).symm

noncomputable
def CartesianMonoidalCategory.tensorLeftIsoProd
    {C : Type*} [Category C] [CartesianMonoidalCategory C] (X : C) :
    MonoidalCategory.tensorLeft X ≅ prod.functor.obj X :=
  NatIso.ofComponents fun Y ↦
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

/-- Modulo composing with a symmetry on both ends, the natural transformation
`prodComparisonNatTrans hofunctor Δ[m]` is a natural transformation between cocontinuous
functors whose component at `X : SSet` is `prodComparison hoFunctor X Δ[m]`. This makes use
of cartesian closure of both `SSet.{u}` and `Cat.{u,u}` to establish cocontinuity of the
product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) X` this reduces to
the result proven in `hoFunctor.binarySimplexProductIsIso`.
-/
lemma hoFunctor.binaryProductWithSimplexIsIso (D X : SSet.{u})
    (H : ∀ m, IsIso (prodComparison hoFunctor D Δ[m])) :
    IsIso (prodComparison hoFunctor D X) := by
  have : (prod.functor.obj D).IsLeftAdjoint := by
    have : (MonoidalCategory.tensorLeft D).IsLeftAdjoint :=
      (CategoryTheory.FunctorToTypes.adj D).isLeftAdjoint
    exact Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd _)
  have : (prod.functor.obj (hoFunctor.obj D)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd _)
  have : hoFunctor.IsLeftAdjoint := nerveAdjunction.isLeftAdjoint
  have : IsIso (whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x ↦ H (x.left).len
  exact isIso_of_colimit_of_natIso _ _ _ (prodComparisonNatTrans ..) _
    (Presheaf.isColimitTautologicalCocone' X)

/-- The natural transformation `prodComparisonNatTrans hofunctor X` is a natural
transformation between cocontinuous functors whose component at `Y : SSet` is
`prodComparison hoFunctor X Y`. This makes use of cartesian closure of both `SSet.{u}`
and `Cat.{u,u}` to establish cocontinuity of the product functors on both categories.

Using the colimit `Presheaf.colimitOfRepresentable (C := SimplexCategory) Y` this reduces to
the result proven in `hoFunctor.binaryProductWithSimplexIsIso`.
-/
instance hoFunctor.binaryProductIsIso (X Y : SSet) :
    IsIso (prodComparison hoFunctor X Y) := by
  apply hoFunctor.binaryProductWithSimplexIsIso
  intro m
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  apply hoFunctor.binaryProductWithSimplexIsIso
  exact fun _ ↦ hoFunctor.binarySimplexProductIsIso _ _

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

instance hoFunctor.preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- A product preserving functor between cartesian closed categories is lax monoidal. -/
noncomputable instance hoFunctor.laxMonoidal : LaxMonoidal hoFunctor :=
  (Monoidal.ofChosenFiniteProducts hoFunctor).toLaxMonoidal

end CategoryTheory
