/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Rev
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The covariant involution of the category of simplicial objects

In this file, we define the covariant involution of the category
of simplicial objects that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

-/

universe v u

open CategoryTheory

namespace SimplicialObject

variable {C : Type*} [Category.{v} C]

/-- The covariant involution of the category of simplicial objects
that is induced by the involution
`SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`. -/
@[simps!]
def revFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

/-- The functor `revFunctor : SimplicialObject C ⥤ SimplicialObject C`
is a covariant involution. -/
@[simps!]
def revFunctorCompRevFunctorIso : revFunctor (C := C) ⋙ revFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

/-- The functor `revFunctor : SimplicialObject C ⥤ SimplicialObject C`
as an equivalence of categories. -/
@[simps!]
def revEquivalence : SimplicialObject C ≌ SimplicialObject C where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revFunctorCompRevFunctorIso.symm
  counitIso := revFunctorCompRevFunctorIso

end SimplicialObject
