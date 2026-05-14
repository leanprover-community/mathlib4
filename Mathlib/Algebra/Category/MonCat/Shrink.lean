/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.Algebra.Group.Shrink
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Shrinking a functor to `MonCat`

For a functor `C ⥤ MonCat.{w'}` with `w`-small image, we shrink to a functor `C ⥤ MonCat.{w}`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

instance (F : C ⥤ MonCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    FunctorToTypes.Small.{w} (F ⋙ forget _) :=
  fun X ↦ inferInstanceAs <| Small.{w} (F.obj X)

/-- A functor `F : C ⥤ MonCat.{w'}` factors through `MonCat.{w}` if all the
monoids are `w`-small. -/
@[simps, pp_with_univ]
noncomputable def MonCat.shrinkFunctor (F : C ⥤ MonCat.{w'}) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ MonCat.{w} where
  obj X := MonCat.of (Shrink.{w} (F.obj X))
  map {X Y} f := MonCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (F.map f).hom).comp Shrink.mulEquiv.toMonoidHom

/-- The natural transformation `MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G`
induces by a natural transformation `τ : F ⟶ G` between `w`-small functors to monoids. -/
@[simps]
noncomputable def MonCat.shrinkFunctorMap {F G : C ⥤ MonCat.{w'}} (τ : F ⟶ G)
    [∀ X, Small.{w} (F.obj X)] [∀ X, Small.{w} (G.obj X)] :
    MonCat.shrinkFunctor.{w} F ⟶ MonCat.shrinkFunctor.{w} G where
  app X := MonCat.ofHom <|
    (Shrink.mulEquiv.symm.toMonoidHom.comp (τ.app X).hom).comp Shrink.mulEquiv.toMonoidHom
  naturality X Y f := by
    ext x
    exact
      congr($((FunctorToTypes.shrinkMap.{w} (Functor.whiskerRight τ (forget _))).naturality f) x)
