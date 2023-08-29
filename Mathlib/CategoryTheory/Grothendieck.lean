/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements

#align_import category_theory.grothendieck from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
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

See also `CategoryTheory.Functor.Elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/


universe u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

variable (F : C ⥤ Cat)

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
-- porting note: no such linter yet
-- @[nolint has_nonempty_instance]
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base
#align category_theory.grothendieck CategoryTheory.Grothendieck

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber
#align category_theory.grothendieck.hom CategoryTheory.Grothendieck.Hom

@[ext]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
                           -- 🎉 no goals
  cases f; cases g
  -- ⊢ { base := base✝, fiber := fiber✝ } = g
           -- ⊢ { base := base✝¹, fiber := fiber✝¹ } = { base := base✝, fiber := fiber✝ }
  congr
  -- ⊢ HEq fiber✝¹ fiber✝
  dsimp at w_base
  -- ⊢ HEq fiber✝¹ fiber✝
  aesop_cat
  -- 🎉 no goals
#align category_theory.grothendieck.ext CategoryTheory.Grothendieck.ext

/-- The identity morphism in the Grothendieck category.
-/
@[simps]
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber])
                       -- 🎉 no goals
#align category_theory.grothendieck.id CategoryTheory.Grothendieck.id

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
@[simps]
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber
                -- 🎉 no goals
#align category_theory.grothendieck.comp CategoryTheory.Grothendieck.comp

attribute [local simp] eqToHom_map

instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp := @fun X Y Z f g => Grothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext
    -- ⊢ comp f (id Y) = f
           -- ⊢ (comp f (id Y)).base = f.base
    · simp
      -- 🎉 no goals
    · dsimp
                              -- ⊢ comp (id X) f = f
                                     -- ⊢ (comp (id X) f).base = f.base
                                             -- 🎉 no goals
                                             -- 🎉 no goals
      -- ⊢ eqToHom (_ : (F.map f.base).obj X.fiber = (F.map (f.base ≫ 𝟙 Y.base)).obj X. …
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      -- ⊢ eqToHom (_ : (F.map f.base).obj X.fiber = (F.map (f.base ≫ 𝟙 Y.base)).obj X. …
      simp
      -- 🎉 no goals
  id_comp := @fun X Y f => by dsimp; ext <;> simp
  assoc := @fun W X Y Z f g h => by
    dsimp; ext
    -- ⊢ comp (comp f g) h = comp f (comp g h)
           -- ⊢ (comp (comp f g) h).base = (comp f (comp g h)).base
    · simp
      -- 🎉 no goals
    · dsimp
      -- ⊢ eqToHom (_ : (F.map (f.base ≫ g.base ≫ h.base)).obj W.fiber = (F.map ((f.bas …
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      -- ⊢ eqToHom (_ : (F.map (f.base ≫ g.base ≫ h.base)).obj W.fiber = (F.map ((f.bas …
      simp
      -- 🎉 no goals

@[simp]
theorem id_fiber' (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber]) :=
                                  -- 🎉 no goals
  id_fiber X
#align category_theory.grothendieck.id_fiber' CategoryTheory.Grothendieck.id_fiber'

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
                          -- ⊢ (F.map f.base).obj X.fiber = (F.map f.base).obj X.fiber
                                   -- 🎉 no goals
  subst h
  -- ⊢ f.fiber = eqToHom (_ : (F.map f.base).obj X.fiber = (F.map f.base).obj X.fib …
  dsimp
  -- ⊢ f.fiber = 𝟙 ((F.map f.base).obj X.fiber) ≫ f.fiber
  simp
  -- 🎉 no goals
#align category_theory.grothendieck.congr CategoryTheory.Grothendieck.congr

section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map := @fun X Y f => f.1
#align category_theory.grothendieck.forget CategoryTheory.Grothendieck.forget

end

universe w

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map := @fun X Y f => ⟨f.1, f.2.1.1⟩
set_option linter.uppercaseLean3 false in
#align category_theory.grothendieck.grothendieck_Type_to_Cat_functor CategoryTheory.Grothendieck.grothendieckTypeToCatFunctor

/-- Auxiliary definition for `grothendieck_Type_to_Cat`, to speed up elaboration. -/
-- Porting note:
-- `simps` is incorrectly producing Prop-valued projections here,
-- so we manually specify which ones to produce.
-- See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/!4.233204.20simps.20bug.20.28Grothendieck.20construction.29
@[simps! obj_base obj_fiber_as map_base]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.grothendieck.grothendieck_Type_to_Cat_inverse CategoryTheory.Grothendieck.grothendieckTypeToCatInverse

/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
-- See porting note on grothendieckTypeToCatInverse.
-- We just want to turn off grothendieckTypeToCat_inverse_map_fiber_down_down,
-- so have to list the complement here for `@[simps]`.
@[simps! functor_obj_fst functor_obj_snd functor_map_coe inverse_obj_base inverse_obj_fiber_as
  inverse_map_base unitIso_hom_app_base unitIso_hom_app_fiber unitIso_inv_app_base
  unitIso_inv_app_fiber counitIso_hom_app_coe counitIso_inv_app_coe]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        -- ⊢ (𝟭 (Grothendieck (G ⋙ typeToCat))).obj { base := base✝, fiber := { as := as✝ …
        exact Iso.refl _)
        -- 🎉 no goals
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        -- ⊢ (𝟭 (Grothendieck (G ⋙ typeToCat))).map { base := base, fiber := { down := {  …
        dsimp at *
        -- ⊢ { base := base, fiber := { down := { down := f } } } ≫ 𝟙 { base := base✝, fi …
        simp
        -- ⊢ { base := base, fiber := { down := { down := f } } } = (grothendieckTypeToCa …
        rfl )
        -- 🎉 no goals
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        -- ⊢ (grothendieckTypeToCatInverse G ⋙ grothendieckTypeToCatFunctor G).obj { fst  …
        exact Iso.refl _)
        -- 🎉 no goals
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        -- ⊢ (grothendieckTypeToCatInverse G ⋙ grothendieckTypeToCatFunctor G).map { val  …
        dsimp at *
        -- ⊢ (grothendieckTypeToCatFunctor G).map ((grothendieckTypeToCatInverse G).map { …
        simp
        -- ⊢ (grothendieckTypeToCatFunctor G).map ((grothendieckTypeToCatInverse G).map { …
        rfl)
        -- 🎉 no goals
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    -- ⊢ (grothendieckTypeToCatFunctor G).map (NatTrans.app (NatIso.ofComponents fun  …
    dsimp
    -- ⊢ (grothendieckTypeToCatFunctor G).map (𝟙 { base := base✝, fiber := { as := as …
    simp
    -- ⊢ (Sigma.rec (motive := fun t => (grothendieckTypeToCatFunctor G).obj { base : …
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.grothendieck.grothendieck_Type_to_Cat CategoryTheory.Grothendieck.grothendieckTypeToCat

end Grothendieck

end CategoryTheory
