/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.FunctorHom

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, where `u`, `v`, and `w` are arbitrary universes.

## TODO
It should be shown that `C ⥤ Type max w v u` is also cartesian closed.
-/


namespace CategoryTheory

universe w v u

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace Functor

abbrev ihom (F G : C ⥤ Type max w v u) : C ⥤ Type max w v u := functorHom F G

end Functor

namespace FunctorToTypes

/-- Given a morphism `f : G ⟶ H`, and object `(c : C)`, and an element of `(F.ihom G).obj c`,
construct an element of `(F.ihom H).obj c`. -/
def rightAdj_map {F G H : C ⥤ Type (max w v u)} (f : G ⟶ H) (c : C) (a : (F.ihom G).obj c) :
    (F.ihom H).obj c where
      app := fun d b ↦ (a.app d b) ≫ (f.app d)
      naturality g h := by
        have := a.naturality g h
        change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
        aesop

/-- A right adjoint of `tensorLeft F`. -/
def rightAdj (F : C ⥤ Type max w v u) : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := F.ihom G
  map f := { app := rightAdj_map f }

variable {F G H : C ⥤ Type max w v u}

def HomObjEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (F.HomObj H G) where
  toFun a := ⟨fun X y x ↦ a.app X (x, y), fun φ y ↦ by
    ext x
    erw [congr_fun (a.naturality φ) (x, y)]
    rfl ⟩
  invFun a := ⟨fun X ⟨x, y⟩ ↦ a.app X y x, fun X Y f ↦ by
    ext ⟨x, y⟩
    erw [congr_fun (a.naturality f y) x]
    rfl ⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

/-- The bijection between morphisms `F ⊗ G ⟶ H` and morphisms `G ⟶ F.ihom H`. -/
def prodHomEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ F.ihom H) :=
  (HomObjEquiv F G H).trans (Functor.functorHomEquiv F H G).symm

/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj (F : C ⥤ Type max w v u) : tensorLeft F ⊣ rightAdj F where
  homEquiv _ _ := prodHomEquiv F _ _
  unit := {
    app := fun G ↦ prodHomEquiv _ _ _ (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, prodHomEquiv, Functor.functorHomEquiv]
      ext d
      dsimp only [Monoidal.tensorObj_obj, comp, Monoidal.whiskerLeft_app, whiskerLeft_apply]
      rw [Eq.symm (FunctorToTypes.naturality G H f _ y)]
      rfl
  }
  counit := { app := fun G ↦ (prodHomEquiv _ _ _).invFun (𝟙 _) }

instance closed (F : C ⥤ Type max w v u) : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end FunctorToTypes

--open Simplicial SimplicialCategory MonoidalCategory

--namespace SSet

--open SimplicialObject

def HomEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (F ⟶ G.ihom H) := sorry

def HomIso (F G H : C ⥤ Type max w v u) : (F ⊗ G).ihom H ≅ F.ihom (G.ihom H) where
  hom := {
    app := fun X ⟨a, ha⟩ ↦ {
      app := fun Y f x ↦ ⟨fun Z g y ↦ a Z (f ≫ g) (F.map g x, y), by
        intro P Q g h
        ext p
        have := congr_fun (ha g (f ≫ h)) (F.map h x, p)
        aesop ⟩
      naturality := by dsimp [Functor.ihom, Functor.functorHom, Functor.HomObjFunctor]; aesop }
    naturality := by dsimp [Functor.ihom, Functor.functorHom, Functor.HomObjFunctor]; aesop }
  inv := { app := fun X ⟨a, ha⟩ ↦ ⟨fun Y f x ↦ (a Y f x.1).1 Y (𝟙 _) x.2, by
    dsimp [Functor.ihom, Functor.functorHom, Functor.HomObjFunctor] at ha ⊢
    intro Y Z f g
    ext y
    dsimp
    have := Functor.HomObj.congr_app (congr_fun (ha f g) y.1) Z (𝟙 _)
    dsimp at this ⊢
    rw [this]

    sorry
    ⟩ }

/-
namespace SimplicialCategory

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

class SimplicialTensor (K : SSet.{v}) (X : C) where
  obj : C
  iso : (sHomFunctor C).obj (Opposite.op obj) ≅
    (sHomFunctor C).obj (Opposite.op X) ⋙ (sHomFunctor SSet.{v}).obj (Opposite.op K)
  α' : K ⟶ sHom X obj
  fac (Y : C) : (SSet.sHomEquiv _ _ _).symm (iso.hom.app Y) =
    _ ◁ α' ≫ (β_ _ _).hom ≫ sHomComp X obj Y

section

variable (K : SSet.{v}) (X Y : C) [SimplicialTensor K X]

scoped infixr:70 " ⊗ₛ " => SimplicialTensor.obj

def sTensorα : K ⟶ sHom X (K ⊗ₛ X) := SimplicialTensor.α'

noncomputable def sTensorIso : sHom (K ⊗ₛ X) Y ≅ sHom K (sHom X Y) :=
  SimplicialTensor.iso.app Y

noncomputable def sTensorEquiv : (K ⊗ₛ X ⟶ Y) ≃ (K ⟶ sHom X Y) :=
  (homEquiv' _ _).trans (((sTensorIso K X Y).app (Opposite.op [0])).toEquiv.trans
    (homEquiv' _ _).symm)

variable {K X Y} in
noncomputable abbrev sTensorDesc (f : K ⟶ sHom X Y) : K ⊗ₛ X ⟶ Y :=
  (sTensorEquiv _ _ _).symm f

end

section

variable {K L : SSet.{v}} (f : K ⟶ L) {X Y : C} (g : X ⟶ Y)
  [SimplicialTensor K X] [SimplicialTensor L Y]

noncomputable def sTensorMap :
    K ⊗ₛ X ⟶ L ⊗ₛ Y := sTensorDesc (f ≫ sTensorα L Y ≫ sHomWhiskerRight g _)

scoped infixr:70 " ⊗ₛ " => sTensorMap

end

end SimplicialCategory
-/

end CategoryTheory
