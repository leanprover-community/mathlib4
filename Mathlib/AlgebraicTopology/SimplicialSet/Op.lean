/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The covariant involution of the category of simplicial sets

In this file, we define the covariant involution `opFunctor : SSet ⥤ SSet`
of the category of simplicial sets that is induced by the
covariant involution `SimplexCategory.op : SimplexCategory ⥤ SimplexCategory`.
We use an abbreviation `X.op` for `opFunctor.obj X`.


## TODO

* Show that this involution sends `Δ[n]` to itself, and that via
this identification, the horn `horn n i` is sent to `horn n i.rev` (@joelriou)
* Construct an isomorphism `nerve Cᵒᵖ ≅ (nerve C).op` (@robin-carlier)
* Show that the topological realization of `X.op` identifies to the
topological realization of `X` (@joelriou)

-/

universe u

open CategoryTheory Simplicial

namespace SSet

/-- The covariant involution of the category of simplicial sets that
is induced by `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`. -/
def opFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.opFunctor

/-- The image of a simplicial set by the involution `opFunctor : SSet ⥤ SSet`. -/
protected abbrev op (X : SSet.{u}) : SSet.{u} := opFunctor.obj X

/-- The type of `n`-simplices of `X.op` identify to type of `n`-simplices of `X`. -/
def opObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.op.obj n ≃ X.obj n := Equiv.refl _

lemma opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.op.obj n) :
    (opFunctor.map f).app n x = opObjEquiv.symm (f.app _ (opObjEquiv x)) :=
  rfl

lemma op_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.op.obj n) :
    X.op.map f x =
      opObjEquiv.symm (X.map (SimplexCategory.rev.map f.unop).op (opObjEquiv x)) :=
  rfl

@[simp]
lemma op_δ (X : SSet.{u}) {n : ℕ} (i : Fin (n + 2)) (x : X _⦋n + 1⦌) :
    X.op.δ i x = opObjEquiv.symm (X.δ i.rev (opObjEquiv x)) := by
  simp [SimplicialObject.δ, op_map]

@[simp]
lemma op_σ (X : SSet.{u}) {n : ℕ} (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.op.σ i x = opObjEquiv.symm (X.σ i.rev (opObjEquiv x)) := by
  simp [SimplicialObject.σ, op_map]

attribute [local simp] op_map in
/-- The functor `opFunctor : SSet ⥤ SSet` is an involution. -/
@[simps!]
def opFunctorCompOpFunctorIso : opFunctor.{u} ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun n ↦ Equiv.toIso (opObjEquiv.trans opObjEquiv)))

/-- The covariant involution `opFunctor : SSet ⥤ SSet`,
as an equivalence of categories. -/
@[simps]
def opEquivalence : SSet.{u} ≌ SSet.{u} where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SSet
