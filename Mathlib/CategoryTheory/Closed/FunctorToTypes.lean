/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.ApplyFun

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is cartesian closed for `C` a category in `Type u` with morphisms in
`Type v`, where `u`, `v`, and `w` are arbitrary universes.
-/


namespace CategoryTheory

universe w v u

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

/-- The ulift functor `(C ⥤ Type v) ⥤ C ⥤ Type max w v u` on functors to Type. -/
def uliftFunctor : (C ⥤ Type v) ⥤ C ⥤ Type max w v u :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{max w v u}

/-- the co-Yoneda embedding ulifted from `Type v` to `Type max w v u` -/
def coyoneda {C : Type u} [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type max w v u :=
    CategoryTheory.coyoneda ⋙ uliftFunctor.{w}

noncomputable section

/-- The internal hom of two functors `C ⥤ Type max w v u`. -/
def ihom (F G : C ⥤ Type max w v u) : C ⥤ Type max w v u where
  obj c := coyoneda.obj (.op c) ⊗ F ⟶ G
  map := fun f g ↦ coyoneda.map (.op f) ▷ F ≫ g

/-- The right adjoint of `tensorLeft F`. -/
def rightAdj (F : C ⥤ Type max w v u) : (C ⥤ Type max w v u) ⥤ C ⥤ Type max w v u where
  obj G := ihom F G
  map f := { app := fun _ h ↦ h ≫ f }

variable {F G H : C ⥤ Type max w v u}

/-- Given a morphism `F ⊗ G ⟶ H`, an object of `(c : C)` and an element of `G.obj c`, construct a
morphism `coyoneda.obj (.op c) ⊗ F ⟶ G`. Used to construct a morphism `G ⟶ ihom F H`. -/
def homEquiv_toFun_app (f : F ⊗ G ⟶ H) (c : C) (y : G.obj c) :
    (ihom F H).obj c where
  app := fun d ⟨g, x⟩ ↦ f.app d (x, G.map g.down y)
  naturality a b h := by
    ext ⟨g, x⟩
    have := f.naturality h
    apply_fun (fun f ↦ f (x, G.map g.down y)) at this
    dsimp only [coyoneda, uliftFunctor]
    aesop

@[ext]
lemma homEquiv_toFun_app_ext {c : C} {f g : (ihom F G).obj c} :
    f.app = g.app → f = g := NatTrans.ext _ _

/-- Given a morphism `F ⊗ G ⟶ H`, construct a morphism `G ⟶ ihom F H`. -/
def homEquiv_toFun (f : F ⊗ G ⟶ H) : G ⟶ ihom F H where
  app := homEquiv_toFun_app f
  naturality c d g := by
    ext
    simp only [ihom, types_comp_apply, coyoneda, uliftFunctor, homEquiv_toFun_app]
    aesop

@[ext]
lemma homEquiv_toFun_ext {f g : G ⟶ ihom F H} :
    f.app = g.app → f = g := NatTrans.ext _ _

/-- Given a morphism `G ⟶ ihom F H`, construct a morphism `F ⊗ G ⟶ H`. -/
def homEquiv_invFun (f : G ⟶ ihom F H) : F ⊗ G ⟶ H where
  app c x := (f.app c x.2).app c (Equiv.ulift.symm (𝟙 c), x.1)
  naturality c d g := by
    ext ⟨x, y⟩
    have h := f.naturality g
    apply_fun (fun f ↦ (f y).app d (Equiv.ulift.symm (𝟙 d), F.map g x)) at h
    have h' := (f.app c y).naturality g
    apply_fun (fun f ↦ f (Equiv.ulift.symm (𝟙 c), x)) at h'
    dsimp only [ihom, coyoneda, uliftFunctor] at h h' ⊢
    aesop

@[ext]
lemma homEquiv_invFun_ext {f g : F ⊗ G ⟶ H} :
    f.app = g.app → f = g := NatTrans.ext _ _

/-- The bijection between morphisms `F ⊗ G ⟶ H` and morphisms `G ⟶ ihom F H`. -/
def homEquiv (F G H : C ⥤ Type max w v u) : (F ⊗ G ⟶ H) ≃ (G ⟶ ihom F H) where
  toFun := homEquiv_toFun
  invFun := homEquiv_invFun
  left_inv _ := by ext; dsimp only [homEquiv_invFun, homEquiv_toFun, homEquiv_toFun_app]; aesop
  right_inv f := by
    ext c y d ⟨g, x⟩
    have b := f.naturality g.down
    apply_fun (fun f ↦ (f y).app d (Equiv.ulift.symm (𝟙 d), x)) at b
    dsimp only [rightAdj, ihom, coyoneda, uliftFunctor] at b ⊢
    aesop

/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
def adj (F : C ⥤ Type max w v u) : tensorLeft F ⊣ rightAdj F where
  homEquiv G H := homEquiv F G H
  unit := {
    app := fun G ↦ homEquiv_toFun (𝟙 _)
    naturality := fun G H f ↦ by
      ext c y
      dsimp [rightAdj, homEquiv_toFun, homEquiv_toFun_app]
      ext d ⟨g, x⟩
      dsimp only [Monoidal.tensorObj_obj, comp, Monoidal.whiskerLeft_app, whiskerLeft_apply]
      rw [Eq.symm (FunctorToTypes.naturality G H f g.down y)]
  }
  counit := { app := fun G ↦ homEquiv_invFun (𝟙 _) }

instance closed (F : C ⥤ Type max w v u) : Closed F where
  rightAdj := rightAdj F
  adj := adj F

instance monoidalClosed : MonoidalClosed (C ⥤ Type max w v u) where
  closed := inferInstance

/-
instance : Limits.HasFiniteProducts (C ⥤ Type max w v u) := sorry

instance cartesianClosed : CartesianClosed (C ⥤ Type max w v u) :=
  {
  closed := _
  }
-/

end
