/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# Cartesian closed structure on `Cat`

The category of small categories is cartesian closed, with the exponential at a category `C`
defined by the functor category mapping out of `C`.

Adjoint transposition is defined by currying and uncurrying.

-/

universe v u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Functor Cat

namespace Cat

variable (C : Type u) [Category.{v} C]

/-- A category `C` induces a functor from `Cat` to itself defined
by forming the category of functors out of `C`. -/
@[simps]
def exp : Cat ⥤ Cat where
  obj D := Cat.of (C ⥤ D)
  map F := (whiskeringRight _ _ _).obj F

end Cat

section

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C] {D : Type u₃}
  [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

/-- The isomorphism of categories of bifunctors given by currying. -/
@[simps!]
def curryingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (C × D ⥤ E) :=
  isoOfEquiv CategoryTheory.currying
    Functor.curry_obj_uncurry_obj (by aesop)
    Functor.uncurry_obj_curry_obj (by aesop)

/-- The isomorphism of categories of bifunctors given by flipping the arguments. -/
@[simps!]
def flippingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E) :=
  isoOfEquiv CategoryTheory.flipping
    Functor.flip_flip (by aesop)
    Functor.flip_flip (by aesop)

/-- The equivalence of types of bifunctors giving by flipping the arguments. -/
@[simps!]
def flippingEquiv : C ⥤ D ⥤ E ≃ D ⥤ C ⥤ E where
  toFun F := F.flip
  invFun F := F.flip
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingEquiv : C ⥤ D ⥤ E ≃ C × D ⥤ E where
  toFun F := uncurry.obj F
  invFun G := curry.obj G
  left_inv := fun F ↦ curry_obj_uncurry_obj F
  right_inv := fun G ↦ uncurry_obj_curry_obj G

/-- The flipped equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingFlipEquiv : D ⥤ C ⥤ E ≃ C × D ⥤ E :=
  flippingEquiv.trans curryingEquiv

/-- Natural isomorphism witnessing `comp_flip_uncurry_eq`. -/
@[simps!]
def compFlipUncurryIso (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip ≅ (𝟭 C).prod F ⋙ uncurry.obj G.flip :=
  .refl _

lemma comp_flip_uncurry_eq (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip = (𝟭 C).prod F ⋙ uncurry.obj G.flip :=
  Functor.ext_of_iso (compFlipUncurryIso F G) (by aesop_cat) (by aesop_cat)

end

section
variable {B C D E : Type u} [Category.{u} B] [Category.{u} C]
  [Category.{u} D] [Category.{u} E]

/-- Natural isomorphism witnessing `comp_flip_curry_eq`. -/
@[simps!]
def compFlipCurryIso (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip ≅ (curry.obj F).flip ⋙ (Cat.exp (Cat.of C)).map G.toCatHom :=
  .refl _

lemma comp_flip_curry_eq (F : C × B ⥤ D) (G : D ⥤ E) :
    (curry.obj (F ⋙ G)).flip =
      (curry.obj F).flip ⋙ (Cat.exp (Cat.of C)).map G.toCatHom :=
  Functor.ext_of_iso (compFlipCurryIso F G) (by aesop_cat) (by aesop_cat)

end

namespace Cat

section
variable (C : Type u) [Category.{u} C]

instance closed : Closed (Cat.of C) where
  rightAdj := exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := curryingFlipEquiv.symm
      homEquiv_naturality_left_symm :=
        comp_flip_uncurry_eq
      homEquiv_naturality_right :=
        comp_flip_curry_eq }

instance cartesianClosed : CartesianClosed Cat.{u, u} where
  closed C := closed C

@[simp]
lemma cartesianClosed_closed_rightAdj_obj {D : Type u} [Category.{u} D] :
    ((Closed.rightAdj (C := Cat.{u,u}) (Cat.of C)).obj (Cat.of D)) = Cat.of (C ⥤ D) := rfl

@[simp]
lemma cartesianClosed_closed_rightAdj_map {D E : Type u}
    [Category.{u} D] [Category.{u} E] {F : D ⥤ E} :
    (CategoryTheory.Closed.rightAdj (C := Cat.{u,u}) (Cat.of C)).map F.toCatHom
      = (whiskeringRight _ _ _).obj F := rfl

end

end Cat

end CategoryTheory
