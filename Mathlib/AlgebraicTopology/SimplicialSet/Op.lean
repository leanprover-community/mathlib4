/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The covariant involution of the category of simplicial sets

In this file, we define the covariant involution of the category
of simplicial sets that is induced by the
covariant involution `SimplexCategory.op : SimplexCategory ⥤ SimplexCategory`.

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
def opFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.opFunctor

/-- The image of a simplicial set by the involution `opFunctor : SSet ⥤ SSet`. -/
protected abbrev op (X : SSet.{u}) : SSet.{u} := opFunctor.obj X

/-- The type of `n`-simplices of `X.op` identify to type of `n`-simplices of `X`. -/
def opObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.op.obj n ≃ X.obj n := Equiv.refl _

lemma op_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.op.obj n) :
    X.op.map f x =
      opObjEquiv.symm (X.map (SimplexCategory.rev.map f.unop).op (opObjEquiv x)) := by
  rfl

/-- The functor `opFunctor : SSet ⥤ SSet` is an involution. -/
@[simps!]
def opFunctorCompOpFunctorIso : opFunctor.{u} ⋙ opFunctor ≅ 𝟭 _ :=
  SimplicialObject.opFunctorCompOpFunctorIso

/-- The covariant involution `opFunctor : SSet ⥤ SSet`,
as an equivalence of categories. -/
@[simps!]
def opEquivalence : SSet.{u} ≌ SSet.{u} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SSet
