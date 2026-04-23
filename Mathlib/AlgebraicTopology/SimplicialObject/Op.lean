/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The covariant involution of the category of simplicial objects

In this file, we define the covariant involution `SimplicialObject.opFunctor`
of the category of simplicial objects that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

-/

@[expose] public section

universe v

open CategoryTheory

namespace SimplicialObject

variable {C : Type*} [Category.{v} C]

/-- The covariant involution of the category of simplicial objects
that is induced by the involution
`SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`. -/
def opFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

/-- The isomorphism `(opFunctor.obj X).obj n ≅ X.obj n` when `X` is a simplicial object. -/
def opObjIso {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _

@[simp]
lemma opFunctor_map_app {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
lemma opFunctor_obj_map (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (opFunctor.obj X).map f =
      opObjIso.hom ≫ X.map (SimplexCategory.rev.map f.unop).op ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
lemma opFunctor_obj_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).δ i = opObjIso.hom ≫ X.δ i.rev ≫ opObjIso.inv := by
  simp [SimplicialObject.δ]

@[simp]
lemma opFunctor_obj_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).σ i = opObjIso.hom ≫ X.σ i.rev ≫ opObjIso.inv := by
  simp [SimplicialObject.σ]

/-- The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
is a covariant involution. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opObjIso.hom := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opObjIso.inv := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

/-- The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
as an equivalence of categories. -/
@[simps]
def opEquivalence : SimplicialObject C ≌ SimplicialObject C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SimplicialObject
