/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements

/-!
# The (opposite) Grothendieck construction

Given a functor `F : Cᵒᵖ ⥤ Cat`, the objects of `opGrothendieck F`
consist of dependent pairs `(b, f)`, where `b : Cᵒᵖ ` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b' ⟶ b` in `Cᵒᵖ`, and
`φ : f ⟶ (F.map β).obj f'`

-/


universe u

open Opposite

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

variable (F : Cᵒᵖ ⥤ Cat)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : Cᵒᵖ ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : Cᵒᵖ` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : Y.base ⟶ X.base` in `Cᵒᵖ` and
  `f.fiber : X.fiber ⟶ (F.map base).obj Y.fiber`
-/
-- porting note: no such linter yet
-- @[nolint has_nonempty_instance]
structure opGrothendieck where
  /-- The underlying object in `Cᵒᵖ` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj (op base)

namespace opGrothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : opGrothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : X.fiber ⟶ (F.map base.op).obj Y.fiber

@[ext]
theorem ext' {X Y : opGrothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber ≫ eqToHom (by rw [w_base]) = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  aesop_cat

/-- The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : opGrothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber])

instance (X : opGrothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : opGrothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    f.fiber ≫ (F.map _).map g.fiber ≫ eqToHom (by erw [op_comp, Functor.map_comp, Functor.comp_obj])

attribute [local simp] eqToHom_map

instance : Category (opGrothendieck F) where
  Hom X Y := opGrothendieck.Hom X Y
  id X := opGrothendieck.id X
  comp := @fun X Y Z f g => opGrothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext <;> simp
  id_comp := @fun X Y f => by
    dsimp; ext; swap
    · simp
    · dsimp
      rw [← NatIso.naturality_2 (eqToIso (F.map_id _)) f.fiber]
      simp
  assoc := @fun W X Y Z f g h => by
    dsimp; ext; swap
    · simp
    · dsimp
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) h.fiber]
      simp

@[simp]
theorem id_base' (X : opGrothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  id_base X

@[simp]
theorem id_fiber' (X : opGrothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber]) :=
  id_fiber X

@[simp]
theorem comp_base' {X Y Z : opGrothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp]
theorem comp_fiber' {X Y Z : opGrothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).fiber = f.fiber ≫ (F.map _).map g.fiber ≫
    eqToHom (by erw [op_comp, Functor.map_comp, Functor.comp_obj]) := rfl

@[ext]
theorem ext {X Y : opGrothendieck F} (f g : X ⟶ Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber ≫ eqToHom (by rw [w_base]) = g.fiber) : f = g := ext' f g w_base w_fiber

theorem congr {X Y : opGrothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (by subst h; rfl) := by
  subst h
  dsimp
  simp

section

variable (F)

open Opposite

/-- The forgetful functor from `opGrothendieck F` to the source category. -/
@[simps!]
def forget : opGrothendieck F ⥤ C where
  obj X := X.1
  map := @fun X Y f => f.1

end

end opGrothendieck

end CategoryTheory
