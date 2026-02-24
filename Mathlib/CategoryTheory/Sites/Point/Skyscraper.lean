/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Skyscraper sheaves

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  [HasProducts.{w} A]

@[simps!]
noncomputable def skyscraperPresheafFunctor : A ⥤ Cᵒᵖ ⥤ A :=
  Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

variable {P Q : Cᵒᵖ ⥤ A} {M N : A}

@[simps -isSimp apply_app symm_apply]
noncomputable def skyscraperPresheafHomEquiv :
    (Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheafFunctor.obj M) where
  toFun f :=
    { app X := Pi.lift (fun x ↦ Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x ↦ g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

@[reassoc (attr := simp)]
lemma toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (g : P ⟶ Φ.skyscraperPresheafFunctor.obj M)
    (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.skyscraperPresheafHomEquiv.symm g =
      g.app (op X) ≫ Pi.π _ x := by
  simp [skyscraperPresheafHomEquiv_symm_apply]

@[reassoc]
lemma skyscraperPresheafHomEquiv_naturality_left_symm
    (f : P ⟶ Q) (g : Q ⟶ Φ.skyscraperPresheafFunctor.obj M) :
    Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) =
      Φ.presheafFiber.map f ≫ Φ.skyscraperPresheafHomEquiv.symm g := by
  cat_disch

@[reassoc (attr := simp)]
lemma skyscraperPresheafHomEquiv_app_π
    (f : Φ.presheafFiber.obj P ⟶ M) (X : C) (x : Φ.fiber.obj X) :
    letI a : P.obj (op X) ⟶ ∏ᶜ (fun (_ : Φ.fiber.obj X) ↦ M) :=
        (Φ.skyscraperPresheafHomEquiv f).app (op X)
    a ≫ Pi.π _ x =
      Φ.toPresheafFiber X x P ≫ f := by
  simp [skyscraperPresheafHomEquiv_apply_app]

@[reassoc]
lemma skyscraperPresheafHomEquiv_naturality_right
    (f : Φ.presheafFiber.obj P ⟶ M) (g : M ⟶ N) :
    Φ.skyscraperPresheafHomEquiv (f ≫ g) =
      Φ.skyscraperPresheafHomEquiv f ≫ Φ.skyscraperPresheafFunctor.map g := by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc, Pi.map_π, skyscraperPresheafHomEquiv_app_π_assoc]

noncomputable def skyscraperPresheafAdjunction :
    Φ.presheafFiber (A := A) ⊣ Φ.skyscraperPresheafFunctor (A := A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _}

end CategoryTheory.GrothendieckTopology.Point
