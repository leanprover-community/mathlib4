/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, and `w` an arbitrary universe.

## TODO
It should be shown that `C ⥤ Type max w v u` is cartesian closed.
-/


universe w v' v u u'

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace CategoryTheory.Functor

variable (F G : C ⥤ D)

/-- Given functors `F G : C ⥤ D`, `HomObj F G A` is a proxy for the type
  of "morphisms" `F ⊗ A ⟶ G`, where `A : C ⥤ Type w` (`w` an arbitrary universe). -/
@[ext]
structure HomObj (A : C ⥤ Type w) where
  app (c : C) (a : A.obj c) : F.obj c ⟶ G.obj c
  naturality {c d : C} (f : c ⟶ d) (a : A.obj c) :
    F.map f ≫ app d (A.map f a) = app c a ≫ G.map f := by aesop_cat

/-- When `F`, `G`, and `A` are all functors `C ⥤ Type w`, then `HomObj F G A` is in
  bijection with `F ⊗ A ⟶ G`. -/
def HomObjEquiv (F G A : C ⥤ Type w) : (F ⊗ A ⟶ G) ≃ (HomObj F G A) where
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

namespace HomObj

attribute [reassoc (attr := simp)] naturality

variable {F G} {A : C ⥤ Type w}

lemma congr_app {f g : HomObj F G A} (h : f = g) (X : C)
    (a : A.obj X) : f.app X a = g.app X a := by subst h; rfl

/-- Given a natural transformation `F ⟶ G`, get a term of `HomObj F G A` by "ignoring" `A`. -/
@[simps]
def ofNatTrans {A : C ⥤ Type w} (f : F ⟶ G) : HomObj F G A where
  app X _ := f.app X

/-- The identity `HomObj F F A`. -/
abbrev id (A : C ⥤ Type w) : HomObj F F A := ofNatTrans (𝟙 F)

/- Composition of `f : HomObj F G A` with `g : HomObj G M A`. -/
@[simps]
def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
  app X a := f.app X a ≫ g.app X a

/-- Given a morphism `A' ⟶ A`, send a term of `HomObj F G A` to a term of `HomObj F G A'`. -/
@[simps]
def map (x : HomObj F G A) {A' : C ⥤ Type w} (f : A' ⟶ A) : HomObj F G A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    dsimp
    rw [← x.naturality φ (f.app Δ a), FunctorToTypes.naturality _ _ f φ a]

end HomObj

/-- The contravariant functor taking `A : C ⥤ Type w` to `HomObj F G A`. -/
def HomObjFunctor : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := HomObj F G A.unop
  map {A A'} f x :=
    { app := fun X a ↦ x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a ↦ by
        dsimp
        rw [← HomObj.naturality]
        congr 2
        exact congr_fun (f.unop.naturality φ) a }

/-- Composition of `HomObjFunctor` with the co-Yoneda embedding.
  When `F G : C ⥤ Type max v' v u`, this is the internal hom of `F` and `G`. -/
def functorHom (F G : C ⥤ D) : C ⥤ Type max v' v u := coyoneda.rightOp ⋙ HomObjFunctor.{v} F G

variable {F G} in
@[ext]
lemma functorHom_ext {X : C} {x y : (F.functorHom G).obj X}
    (h : ∀ (Y : C) (f : X ⟶ Y), x.app Y f = y.app Y f) : x = y :=
  HomObj.ext (by ext; apply h)

/-- The bijection `HomObj F G A ≃ (A ⟶ F.functorHom G)` which
  prefaces `FunctorToTypes.functorHomEquiv` -/
def functorHomEquiv (A : C ⥤ Type max u v v') : HomObj F G A ≃ (A ⟶ F.functorHom G) where
  toFun x :=
    { app := fun X a ↦ { app := fun Y f => x.app Y (A.map f a) }
      naturality := fun X Y f => by
        ext a Z φ
        dsimp only [types_comp_apply]
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  invFun φ :=
    { app := fun X a ↦ (φ.app X a).app X (𝟙 _)
      naturality := fun {X Y} f a => by
        rw [← (φ.app X a).naturality f (𝟙 _)]
        have := HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)
        dsimp [functorHom, HomObjFunctor] at this
        aesop }
  left_inv x := by aesop
  right_inv φ := by
    ext X a Y f
    exact (HomObj.congr_app (congr_fun (φ.naturality f) a) Y (𝟙 _)).trans
      (congr_arg ((φ.app X a).app Y) (by simp))

variable {F G} in
/-- Morphisms `F ⟶ G` are in bijection with
  morphisms `(𝟙_ (C ⥤ Type max v' v u) ⟶ F.functorHom G)`-/
@[simps]
def natTransEquiv : (F ⟶ G) ≃ (𝟙_ (C ⥤ Type max v' v u) ⟶ F.functorHom G) where
  toFun f := ⟨fun _ _ ↦ HomObj.ofNatTrans f, _⟩
  invFun f := ⟨fun X ↦ (f.app X (PUnit.unit)).app X (𝟙 _), by
    intro X Y φ
    rw [← (f.app X (PUnit.unit)).naturality φ]
    congr 1
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, HomObjFunctor] at this
    aesop ⟩
  left_inv _ := rfl
  right_inv f := by
    ext X a Y φ
    have := HomObj.congr_app (congr_fun (f.naturality φ) PUnit.unit) Y (𝟙 Y)
    dsimp [functorHom, HomObjFunctor] at this
    aesop

end Functor

namespace FunctorToTypes

variable (F : C ⥤ Type max w v u)

open Functor in
/-- When `F G H : C ⥤ Type max w v u`, we have `(F ⊗ G ⟶ H) ≃ (G ⟶ F.functorHom H)`. -/
def functorHomEquiv (G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ F.functorHom H) :=
  (HomObjEquiv F H G).trans (Functor.functorHomEquiv F H G)

/-- Given a morphism `f : G ⟶ H`, an object `c : C`, and an element of `(F.functorHom G).obj c`,
construct an element of `(F.functorHom H).obj c`. -/
def rightAdj_map {F G H : C ⥤ Type max w v u} (f : G ⟶ H) (c : C) (a : (F.functorHom G).obj c) :
    (F.functorHom H).obj c where
      app := fun d b ↦ (a.app d b) ≫ (f.app d)
      naturality g h := by
        have := a.naturality g h
        change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
        aesop

/-- A right adjoint of `tensorLeft F`. -/
def rightAdj : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := F.functorHom G
  map f := { app := rightAdj_map f }

open Functor in
/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj : tensorLeft F ⊣ rightAdj F where
  homEquiv := functorHomEquiv F
  unit := {
    app := fun G ↦ functorHomEquiv F _ _ (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, functorHomEquiv, Functor.functorHomEquiv]
      ext d
      dsimp only [Monoidal.tensorObj_obj, rightOp_obj]
      rw [Eq.symm (FunctorToTypes.naturality G H f _ y)]
      rfl }
  counit := { app := fun G ↦ (functorHomEquiv F _ _).2 (𝟙 _) }

instance closed : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end FunctorToTypes

end CategoryTheory
