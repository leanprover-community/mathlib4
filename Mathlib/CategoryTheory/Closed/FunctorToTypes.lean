/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.ApplyFun

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, where `u`, `v`, and `w` are arbitrary universes.

## TODO
It should be shown that `C ⥤ Type max w v u` is also cartesian closed.
-/


namespace CategoryTheory

universe w v' v u u'

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace Functor

variable {D : Type u'} [Category.{v'} D]

@[ext]
structure Hom₂ (F G : C ⥤ D) (A : C ⥤ Type w) where
  app (c : C) (a : A.obj c) : F.obj c ⟶ G.obj c
  naturality {c d : C} (f : c ⟶ d) (a : A.obj c) :
    F.map f ≫ app d (A.map f a) = app c a ≫ G.map f := by aesop_cat

def hom₂Functor (F G : C ⥤ D) : (C ⥤ Type w)ᵒᵖ ⥤ Type max w v' u where
  obj A := Hom₂ F G A.unop
  map {A A'} f x :=
    { app := fun X a ↦ x.app X (f.unop.app _ a)
      naturality := fun {X Y} φ a ↦ by
        dsimp
        rw [← Hom₂.naturality]
        congr 2
        exact congr_fun (f.unop.naturality φ) a }

def ihom (F G : C ⥤ D) : C ⥤ Type max u v v' := coyoneda.rightOp ⋙ hom₂Functor.{v} F G

end Functor

namespace FunctorToTypes

/-
/-- The ulift functor `(C ⥤ Type v) ⥤ C ⥤ Type max w v u` on functors to Type. -/
def uliftFunctor : (C ⥤ Type v) ⥤ C ⥤ Type max w v u :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{max w v u}

/-- the co-Yoneda embedding ulifted from `Type v` to `Type max w v u` -/
def coyoneda {C : Type u} [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type max w v u :=
    CategoryTheory.coyoneda ⋙ uliftFunctor.{w}

/-- The internal hom of two functors `C ⥤ Type max w v u`. -/
def ihom (F G : C ⥤ Type max w v u) : C ⥤ Type max w v u where
  obj c := coyoneda.obj (.op c) ⊗ F ⟶ G
  map := fun f g ↦ coyoneda.map (.op f) ▷ F ≫ g
-/

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

/-- Given a morphism `F ⊗ G ⟶ H`, an object `(c : C)` and an element of `G.obj c`, construct an
element of `(F.ihom H).obj c`. Used to construct a morphism `G ⟶ F.ihom H`. -/
def homEquiv_toFun_app (f : F ⊗ G ⟶ H) (c : C) (y : G.obj c) :
    (F.ihom H).obj c where
  app d g x := f.app d (x, G.map g y)
  naturality g h := by
    ext x
    have := f.naturality g
    apply_fun (fun f ↦ f (x, G.map h y)) at this
    aesop

@[ext]
lemma homEquiv_toFun_app_ext {c : C} (f g : (F.ihom G).obj c) :
    f.app = g.app → f = g := Functor.Hom₂.ext _ _

/-- Given a morphism `F ⊗ G ⟶ H`, construct a morphism `G ⟶ F.ihom H`. -/
def homEquiv_toFun (f : F ⊗ G ⟶ H) : G ⟶ F.ihom H where
  app := homEquiv_toFun_app f
  naturality _ _ _ := by
    ext _
    dsimp [homEquiv_toFun_app, Functor.ihom, Functor.hom₂Functor]
    aesop

@[ext]
lemma homEquiv_toFun_ext (f g : G ⟶ F.ihom H) :
    f.app = g.app → f = g := NatTrans.ext _ _

/-- Given a morphism `G ⟶ F.ihom H`, construct a morphism `F ⊗ G ⟶ H`. -/
def homEquiv_invFun (f : G ⟶ F.ihom H) : F ⊗ G ⟶ H where
  app c x := (f.app c x.2).app c (𝟙 c) x.1
  naturality c d g := by
    ext ⟨x, y⟩
    have h := f.naturality g
    apply_fun (fun f ↦ (f y).app d (𝟙 d) (F.map g x)) at h
    have h' := (f.app c y).naturality g (𝟙 c)
    apply_fun (fun f ↦ f x) at h'
    dsimp at h h' ⊢
    rw [h, ← h']
    dsimp [Functor.ihom, Functor.hom₂Functor]
    aesop

@[ext]
lemma homEquiv_invFun_ext (f g : F ⊗ G ⟶ H) :
    f.app = g.app → f = g := NatTrans.ext _ _

/-- The bijection between morphisms `F ⊗ G ⟶ H` and morphisms `G ⟶ F.ihom H`. -/
def homEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ F.ihom H) where
  toFun := homEquiv_toFun
  invFun := homEquiv_invFun
  left_inv _ := by ext; dsimp only [homEquiv_invFun, homEquiv_toFun, homEquiv_toFun_app]; aesop
  right_inv f := by
    ext c y d g x
    have b := f.naturality g
    apply_fun (fun f ↦ (f y).app d (𝟙 d) x) at b
    dsimp only [Functor.ihom, Functor.hom₂Functor] at b ⊢
    aesop

/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj (F : C ⥤ Type max w v u) : tensorLeft F ⊣ rightAdj F where
  homEquiv := homEquiv F
  unit := {
    app := fun G ↦ homEquiv_toFun (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, homEquiv_toFun, homEquiv_toFun_app]
      ext d
      dsimp only [Monoidal.tensorObj_obj, comp, Monoidal.whiskerLeft_app, whiskerLeft_apply]
      rw [Eq.symm (FunctorToTypes.naturality G H f _ y)]
      rfl
  }
  counit := { app := fun G ↦ homEquiv_invFun (𝟙 _) }

instance closed (F : C ⥤ Type max w v u) : Closed F where
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where

end FunctorToTypes

end CategoryTheory
