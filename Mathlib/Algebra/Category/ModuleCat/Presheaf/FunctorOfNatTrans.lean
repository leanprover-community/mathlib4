/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# The endofunctor of presheaves of modules induced by an oplax natural transformation

In this file, we show that any oplax natural transformation from
`ModuleCat.restrictScalarsPseudofunctor` to itself induces
a functor `PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R`
for any presheaf of rings.

TODO: the commutative case seems more useful

-/

universe v v₁ u₁ u

open CategoryTheory Category Limits Opposite

namespace PresheafOfModules

variable (τ : OplaxNatTrans ModuleCat.restrictScalarsPseudofunctor.{v, u}.toOplax
  ModuleCat.restrictScalarsPseudofunctor.{v, u}.toOplax)
  {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- Any oplax natural transformation from `ModuleCat.restrictScalarsPseudofunctor`
to itself induced a functor `PresheafOfModules R ⥤ PresheafOfModules R`. -/
noncomputable def functorOfOplaxNatTrans :
  PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R where
  obj M :=
    { obj := fun X ↦ (τ.app (LocallyDiscrete.mk (op (R.obj X)))).obj (M.obj X)
      map := fun {X Y} f ↦ (τ.app _).map (M.map f) ≫
        (τ.naturality (Quiver.Hom.toLoc (R.map f).op)).app (M.obj Y)
      map_id := fun X ↦ by
        dsimp
        sorry
      map_comp := sorry }
  map {M N} φ :=
    { app := fun X ↦ (τ.app _).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        dsimp only
        rw [assoc, ← Functor.map_comp_assoc, ← φ.naturality,
          Functor.map_comp_assoc]
        erw [← NatTrans.naturality]
        rfl }
  map_id _ := by ext; dsimp; simp
  map_comp _ _ := by ext; dsimp; simp

end PresheafOfModules
