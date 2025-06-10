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

open Functor

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
@[simps]
def curryingIso : C ⥤ D ⥤ E ≅ C × D ⥤ E where
  hom F := uncurry.obj F
  inv G := curry.obj G
  hom_inv_id := types_ext _ _ (fun F ↦ curry_obj_uncurry_obj F)
  inv_hom_id := types_ext _ _ (fun F ↦ uncurry_obj_curry_obj F)

/-- The isomorphism of categories of bifunctors given by flipping the arguments. -/
@[simps]
def flippingIso : C ⥤ D ⥤ E ≅ D ⥤ C ⥤ E where
  hom F := F.flip
  inv F := F.flip
  hom_inv_id := types_ext _ _ (fun _ ↦ rfl)
  inv_hom_id := types_ext _ _ (fun _ ↦ rfl)

/-- The equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingEquiv : C ⥤ D ⥤ E ≃ C × D ⥤ E :=
  curryingIso.toEquiv

/-- The flipped equivalence of types of bifunctors given by currying. -/
@[simps!]
def curryingFlipEquiv : D ⥤ C ⥤ E ≃ C × D ⥤ E :=
  (flippingIso ≪≫ curryingIso).toEquiv

/-- Natural isomorphism witnessing `comp_flip_uncurry_eq`. -/
@[simps!]
def compFlipUncurryIso (F : B ⥤ D) (G : D ⥤ C ⥤ E) :
    uncurry.obj (F ⋙ G).flip ≅ (𝟭 C).prod F ⋙ (uncurry.obj G.flip) :=
  NatIso.ofComponents (fun _ ↦ eqToIso rfl)

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
  NatIso.ofComponents (fun _ ↦ eqToIso rfl)

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
  adj := Adjunction.mkOfHomEquiv {
    homEquiv _ _ := curryingFlipEquiv.symm
    homEquiv_naturality_left_symm :=
      comp_flip_uncurry_eq
    homEquiv_naturality_right :=
      comp_flip_curry_eq
  }

instance cartesianClosed : CartesianClosed Cat.{u, u} where
  closed C := closed C

end

end Cat

end CategoryTheory
