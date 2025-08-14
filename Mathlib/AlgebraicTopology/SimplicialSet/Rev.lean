/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Rev
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The covariant involution of the category of simplicial sets

In this file, we define the covariant involution of the category
of simplicial sets that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

## TODO (@joelriou)

Show that this involution sends `Δ[n]` to itself, and that via
this identification, the horn `horn n i` is sent to `horn n i.rev`.

-/

universe u

open CategoryTheory

namespace SSet

/-- The covariant involution of the category of simplicial sets that
is induced by `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`. -/
@[simps! map]
def revFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.revFunctor

/-- The image of a simplicial set by the involution `revFunctor : SSet ⥤ SSet`. -/
abbrev rev (X : SSet.{u}) : SSet.{u} := revFunctor.obj X

/-- The type of `n`-simplices of `X.rev` identify to type of `n`-simplices of `X`. -/
def revObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.rev.obj n ≃ X.obj n := Equiv.refl _

lemma rev_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.rev.obj n) :
    X.rev.map f x =
      revObjEquiv.symm (X.map (SimplexCategory.rev.map f.unop).op (revObjEquiv x)) := by
  rfl

/-- The functor `revFunctor : SSet ⥤ SSet` is an involution. -/
@[simps!]
def revFunctorCompRevFunctorIso : revFunctor.{u} ⋙ revFunctor ≅ 𝟭 _ :=
  SimplicialObject.revFunctorCompRevFunctorIso

/-- The covariant involution `revFunctor : SSet ⥤ SSet`,
as an equivalence of categories. -/
@[simps!]
def revEquivalence : SSet.{u} ≌ SSet.{u} where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revFunctorCompRevFunctorIso.symm
  counitIso := revFunctorCompRevFunctorIso

end SSet
