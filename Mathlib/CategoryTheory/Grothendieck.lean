/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.grothendieck
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Elements

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `category_theory.functor.elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe u

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

variable (F : C ⥤ Cat)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
@[nolint has_nonempty_instance]
structure Grothendieck where
  base : C
  fiber : F.obj base
#align category_theory.grothendieck CategoryTheory.Grothendieck

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  base : X.base ⟶ Y.base
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber
#align category_theory.grothendieck.hom CategoryTheory.Grothendieck.Hom

@[ext]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g :=
  by
  cases f <;> cases g
  congr
  dsimp at w_base
  induction w_base
  rfl
  dsimp at w_base
  induction w_base
  simpa using w_fiber
#align category_theory.grothendieck.ext CategoryTheory.Grothendieck.ext

/-- The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, functor.id_obj X.fiber])
#align category_theory.grothendieck.id CategoryTheory.Grothendieck.id

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
    where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [functor.map_comp, functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber
#align category_theory.grothendieck.comp CategoryTheory.Grothendieck.comp

attribute [local simp] eq_to_hom_map

instance : Category (Grothendieck F)
    where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp X Y Z f g := Grothendieck.comp f g
  comp_id' X Y f := by
    ext
    · dsimp
      -- We need to turn `F.map_id` (which is an equation between functors)
      -- into a natural isomorphism.
      rw [← nat_iso.naturality_2 (eq_to_iso (F.map_id Y.base)) f.fiber]
      simp
    · simp
  id_comp' X Y f := by ext <;> simp
  assoc' W X Y Z f g h := by
    ext; swap
    · simp
    · dsimp
      rw [← nat_iso.naturality_2 (eq_to_iso (F.map_comp _ _)) f.fiber]
      simp
      rfl

@[simp]
theorem id_fiber' (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, functor.id_obj X.fiber]) :=
  id_fiber X
#align category_theory.grothendieck.id_fiber' CategoryTheory.Grothendieck.id_fiber'

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h) ≫ g.fiber :=
  by
  subst h
  dsimp
  simp
#align category_theory.grothendieck.congr CategoryTheory.Grothendieck.congr

section

variable (F)

/-- The forgetful functor from `grothendieck F` to the source category. -/
@[simps]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map X Y f := f.1
#align category_theory.grothendieck.forget CategoryTheory.Grothendieck.forget

end

universe w

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements
    where
  obj X := ⟨X.1, X.2.as⟩
  map X Y f := ⟨f.1, f.2.1.1⟩
#align category_theory.grothendieck.grothendieck_Type_to_Cat_functor CategoryTheory.Grothendieck.grothendieckTypeToCatFunctor

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat)
    where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map X Y f := ⟨f.1, ⟨⟨f.2⟩⟩⟩
#align category_theory.grothendieck.grothendieck_Type_to_Cat_inverse CategoryTheory.Grothendieck.grothendieckTypeToCatInverse

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements
    where
  Functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        subst f
        ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        subst e
        ext
        simp)
  functor_unitIso_comp' := by
    rintro ⟨_, ⟨⟩⟩
    dsimp
    simp
    rfl
#align category_theory.grothendieck.grothendieck_Type_to_Cat CategoryTheory.Grothendieck.grothendieckTypeToCat

end Grothendieck

end CategoryTheory

