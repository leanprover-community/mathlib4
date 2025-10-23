/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl
-/
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# Cartesian closed structure on `Cat`

The category of small categories is Cartesian closed, with the exponential at a category `C`
defined by the functor category mapping out of `C`.

Adjoint transposition is defined by currying and uncurrying.

TODO: It would be useful to investigate and formalize further compatibilities along the
lines of `Cat.ihom_obj` and `Cat.ihom_map`, relating currying of functors with currying in
monoidal closed categories and precomposition with left whiskering. These may not be
definitional equalities but may have to be phrased using `eqToIso`.

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
  isoOfEquiv currying Functor.curry_obj_uncurry_obj Functor.uncurry_obj_curry_obj

/-- The isomorphism of categories of bifunctors given by flipping the arguments. -/
@[simps!]
def flippingIso : Cat.of (C ⥤ D ⥤ E) ≅ Cat.of (D ⥤ C ⥤ E) :=
  isoOfEquiv flipping Functor.flip_flip Functor.flip_flip

end

namespace Cat

section
variable (C : Type u) [Category.{u} C]

instance closed : Closed (Cat.of C) where
  rightAdj := exp C
  adj := Adjunction.mkOfHomEquiv
    { homEquiv _ _ := curryingFlipEquiv.symm
      homEquiv_naturality_left_symm := comp_flip_uncurry_eq
      homEquiv_naturality_right := curry_obj_comp_flip }

instance cartesianClosed : CartesianClosed Cat.{u, u} where
  closed C := closed C

@[simp]
lemma ihom_obj (D : Type u) [Category.{u} D] :
    (ihom (Cat.of C)).obj (Cat.of D) = Cat.of (C ⥤ D) := rfl

@[simp]
lemma ihom_map {D E : Type u} [Category.{u} D] [Category.{u} E] (F : D ⥤ E) :
    (ihom (Cat.of C)).map F.toCatHom = (whiskeringRight _ _ _).obj F := rfl

end

end Cat

end CategoryTheory
