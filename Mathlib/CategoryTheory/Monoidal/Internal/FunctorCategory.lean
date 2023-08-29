/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

#align_import category_theory.monoidal.internal.functor_category from "leanprover-community/mathlib"@"f153a85a8dc0a96ce9133fed69e34df72f7f191f"

/-!
# `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `monFunctorCategoryEquivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

-- porting note: the `obj` field of `functor : Mon_ (C ⥤ D) ⥤ C ⥤ Mon_ D` defined below
-- had to be defined separately as `Functor.obj` in order to speed up the compilation
/-- A monoid object in a functor category induces a functor to the category of monoid objects. -/
@[simps]
def Functor.obj (A : Mon_ (C ⥤ D)) : C ⥤ Mon_ D where
  obj X :=
    { X := A.X.obj X
      one := A.one.app X
      mul := A.mul.app X
      one_mul := congr_app A.one_mul X
      mul_one := congr_app A.mul_one X
      mul_assoc := congr_app A.mul_assoc X }
  map f :=
    { hom := A.X.map f
      one_hom := by rw [← A.one.naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
                    -- ⊢ 𝟙 (𝟙_ D) ≫ NatTrans.app A.one Y✝ = ((fun X => Mon_.mk (A.X.obj X) (NatTrans. …
                                                             -- ⊢ 𝟙 (𝟙_ D) ≫ NatTrans.app A.one Y✝ = NatTrans.app A.one Y✝
                                                                    -- 🎉 no goals
      mul_hom := by dsimp; rw [← A.mul.naturality, tensorObj_map] }
                    -- ⊢ NatTrans.app A.mul X✝ ≫ A.X.map f = (A.X.map f ⊗ A.X.map f) ≫ NatTrans.app A …
                           -- 🎉 no goals
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
                 -- ⊢ ({ obj := fun X => Mon_.mk (A.X.obj X) (NatTrans.app A.one X) (NatTrans.app  …
                      -- ⊢ A.X.map (𝟙 X) = 𝟙 (A.X.obj X)
                             -- 🎉 no goals
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]
                     -- ⊢ ({ obj := fun X => Mon_.mk (A.X.obj X) (NatTrans.app A.one X) (NatTrans.app  …
                          -- ⊢ A.X.map (f ≫ g) = A.X.map f ≫ A.X.map g
                                 -- 🎉 no goals

/-- Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
def functor : Mon_ (C ⥤ D) ⥤ C ⥤ Mon_ D where
  obj := Functor.obj
  map f :=
    { app := fun X =>
        { hom := f.hom.app X
          one_hom := congr_app f.one_hom X
          mul_hom := congr_app f.mul_hom X } }
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.Mon_functor_category_equivalence.functor CategoryTheory.Monoidal.MonFunctorCategoryEquivalence.functor

-- porting note: the `obj` field of `inverse : (C ⥤ Mon_ D) ⥤ Mon_ (C ⥤ D)` defined below
-- had to be defined separately as `Inverse.obj` in order to speed up the compilation
/-- A functor to the category of monoid objects can be translated as a monoid object
in the functor category. -/
@[simps]
def Inverse.obj (F : C ⥤ Mon_ D) : Mon_ (C ⥤ D) where
  X := F ⋙ Mon_.forget D
  one := { app := fun X => (F.obj X).one }
  mul := { app := fun X => (F.obj X).mul }
  one_mul := by ext X; exact (F.obj X).one_mul
                -- ⊢ NatTrans.app (((NatTrans.mk fun X => (F.obj X).one) ⊗ 𝟙 (F ⋙ Mon_.forget D)) …
                       -- 🎉 no goals
  mul_one := by ext X; exact (F.obj X).mul_one
                -- ⊢ NatTrans.app ((𝟙 (F ⋙ Mon_.forget D) ⊗ NatTrans.mk fun X => (F.obj X).one) ≫ …
                       -- 🎉 no goals
  mul_assoc := by ext X; exact (F.obj X).mul_assoc
                  -- ⊢ NatTrans.app (((NatTrans.mk fun X => (F.obj X).mul) ⊗ 𝟙 (F ⋙ Mon_.forget D)) …
                         -- 🎉 no goals

/-- Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ Mon_ D) ⥤ Mon_ (C ⥤ D) where
  obj := Inverse.obj
  map α :=
    { hom :=
        { app := fun X => (α.app X).hom
          naturality := fun X Y f => congr_arg Mon_.Hom.hom (α.naturality f) }
      one_hom := by ext x; dsimp; rw [(α.app x).one_hom]
                    -- ⊢ NatTrans.app ((Inverse.obj X✝).one ≫ NatTrans.mk fun X => (NatTrans.app α X) …
                           -- ⊢ (X✝.obj x).one ≫ (NatTrans.app α x).hom = (Y✝.obj x).one
                                  -- 🎉 no goals
      mul_hom := by ext x; dsimp; rw [(α.app x).mul_hom] }
                    -- ⊢ NatTrans.app ((Inverse.obj X✝).mul ≫ NatTrans.mk fun X => (NatTrans.app α X) …
                           -- ⊢ (X✝.obj x).mul ≫ (NatTrans.app α x).hom = ((NatTrans.app α x).hom ⊗ (NatTran …
                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.Mon_functor_category_equivalence.inverse CategoryTheory.Monoidal.MonFunctorCategoryEquivalence.inverse

/-- The unit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps!]
def unitIso : 𝟭 (Mon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { hom := { app := fun _ => 𝟙 _ }
            one_hom := by ext X; dsimp; simp only [Category.comp_id]
                          -- ⊢ NatTrans.app (((𝟭 (Mon_ (C ⥤ D))).obj A).one ≫ NatTrans.mk fun x => 𝟙 (((𝟭 ( …
                                 -- ⊢ NatTrans.app A.one X ≫ 𝟙 (A.X.obj X) = NatTrans.app A.one X
                                        -- 🎉 no goals
            mul_hom := by
              ext X; dsimp; simp only [tensor_id, Category.id_comp, Category.comp_id] }
              -- ⊢ NatTrans.app (((𝟭 (Mon_ (C ⥤ D))).obj A).mul ≫ NatTrans.mk fun x => 𝟙 (((𝟭 ( …
                     -- ⊢ NatTrans.app A.mul X ≫ 𝟙 (A.X.obj X) = (𝟙 (A.X.obj X) ⊗ 𝟙 (A.X.obj X)) ≫ Nat …
                            -- 🎉 no goals
        inv :=
          { hom := { app := fun _ => 𝟙 _ }
            one_hom := by ext X; dsimp; simp only [Category.comp_id]
                          -- ⊢ NatTrans.app (((functor ⋙ inverse).obj A).one ≫ NatTrans.mk fun x => 𝟙 (((fu …
                                 -- ⊢ NatTrans.app A.one X ≫ 𝟙 (A.X.obj X) = NatTrans.app A.one X
                                        -- 🎉 no goals
            mul_hom := by
              ext X
              -- ⊢ NatTrans.app (((functor ⋙ inverse).obj A).mul ≫ NatTrans.mk fun x => 𝟙 (((fu …
              dsimp
              -- ⊢ NatTrans.app A.mul X ≫ 𝟙 (A.X.obj X) = (𝟙 (A.X.obj X) ⊗ 𝟙 (A.X.obj X)) ≫ Nat …
              simp only [tensor_id, Category.id_comp, Category.comp_id] } })
              -- 🎉 no goals
    fun f => by
      ext X
      -- ⊢ NatTrans.app ((𝟭 (Mon_ (C ⥤ D))).map f ≫ ((fun A => Iso.mk (Mon_.Hom.mk (Nat …
      simp only [Functor.id_map, Mon_.comp_hom', NatTrans.comp_app, Category.comp_id,
        Functor.comp_map, inverse_map_hom_app, functor_map_app_hom, Category.id_comp]
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.Mon_functor_category_equivalence.unit_iso CategoryTheory.Monoidal.MonFunctorCategoryEquivalence.unitIso

/-- The counit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon_ D) :=
  NatIso.ofComponents
    (fun A =>
      NatIso.ofComponents
        (fun X =>
          { hom := { hom := 𝟙 _ }
            inv := { hom := 𝟙 _ } })
        (by aesop_cat))
            -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.Mon_functor_category_equivalence.counit_iso CategoryTheory.Monoidal.MonFunctorCategoryEquivalence.counitIso

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

/-- When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
def monFunctorCategoryEquivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.Mon_functor_category_equivalence CategoryTheory.Monoidal.monFunctorCategoryEquivalence

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

/-- Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps!]
def functor : CommMon_ (C ⥤ D) ⥤ C ⥤ CommMon_ D where
  obj A :=
    { (monFunctorCategoryEquivalence C D).functor.obj A.toMon_ with
      obj := fun X =>
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon_).obj X with
          mul_comm := congr_app A.mul_comm X } }
  map f := { app := fun X => ((monFunctorCategoryEquivalence C D).functor.map f).app X }
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.CommMon_functor_category_equivalence.functor CategoryTheory.Monoidal.CommMonFunctorCategoryEquivalence.functor

/-- Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps!]
def inverse : (C ⥤ CommMon_ D) ⥤ CommMon_ (C ⥤ D) where
  obj F :=
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon_.forget₂Mon_ D) with
      mul_comm := by ext X; exact (F.obj X).mul_comm }
                     -- ⊢ NatTrans.app ((β_ (Mon_.mk src✝.X src✝.one src✝.mul).X (Mon_.mk src✝.X src✝. …
                            -- 🎉 no goals
  map α := (monFunctorCategoryEquivalence C D).inverse.map (whiskerRight α _)
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.CommMon_functor_category_equivalence.inverse CategoryTheory.Monoidal.CommMonFunctorCategoryEquivalence.inverse

/-- The unit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps!]
def unitIso : 𝟭 (CommMon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { hom := { app := fun _ => 𝟙 _ }
            one_hom := by ext X; dsimp; simp only [Category.comp_id]
                          -- ⊢ NatTrans.app (((𝟭 (CommMon_ (C ⥤ D))).obj A).one ≫ NatTrans.mk fun x => 𝟙 (( …
                                 -- ⊢ NatTrans.app A.one X ≫ 𝟙 (A.X.obj X) = NatTrans.app A.one X
                                        -- 🎉 no goals
            mul_hom := by ext X; dsimp; simp only [tensor_id, Category.id_comp, Category.comp_id] }
                          -- ⊢ NatTrans.app (((𝟭 (CommMon_ (C ⥤ D))).obj A).mul ≫ NatTrans.mk fun x => 𝟙 (( …
                                 -- ⊢ NatTrans.app A.mul X ≫ 𝟙 (A.X.obj X) = (𝟙 (A.X.obj X) ⊗ 𝟙 (A.X.obj X)) ≫ Nat …
                                        -- 🎉 no goals
        inv :=
          { hom := { app := fun _ => 𝟙 _ }
            one_hom := by ext X; dsimp; simp only [Category.comp_id]
                          -- ⊢ NatTrans.app (((functor ⋙ inverse).obj A).one ≫ NatTrans.mk fun x => 𝟙 (((fu …
                                 -- ⊢ NatTrans.app A.one X ≫ 𝟙 ((CommMon_.forget₂Mon_ D).obj ((functor.obj A).obj  …
                                        -- 🎉 no goals
            mul_hom := by
              ext X
              -- ⊢ NatTrans.app (((functor ⋙ inverse).obj A).mul ≫ NatTrans.mk fun x => 𝟙 (((fu …
              dsimp
              -- ⊢ NatTrans.app A.mul X ≫ 𝟙 ((CommMon_.forget₂Mon_ D).obj ((functor.obj A).obj  …
              simp only [tensor_id, Category.id_comp, Category.comp_id] } })
              -- 🎉 no goals
    fun f => by
      ext X
      -- ⊢ NatTrans.app ((𝟭 (CommMon_ (C ⥤ D))).map f ≫ ((fun A => Iso.mk (Mon_.Hom.mk  …
      dsimp
      -- ⊢ NatTrans.app f.hom X ≫ 𝟙 (Y✝.X.obj X) = 𝟙 (X✝.X.obj X) ≫ NatTrans.app f.hom X
      simp only [Category.id_comp, Category.comp_id]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.CommMon_functor_category_equivalence.unit_iso CategoryTheory.Monoidal.CommMonFunctorCategoryEquivalence.unitIso

/-- The counit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon_ D) :=
  NatIso.ofComponents
    (fun A =>
      NatIso.ofComponents
        (fun X =>
          { hom := { hom := 𝟙 _ }
            inv := { hom := 𝟙 _ } })
        (by aesop_cat))
            -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.CommMon_functor_category_equivalence.counit_iso CategoryTheory.Monoidal.CommMonFunctorCategoryEquivalence.counitIso

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

/-- When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
def commMonFunctorCategoryEquivalence : CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal.CommMon_functor_category_equivalence CategoryTheory.Monoidal.commMonFunctorCategoryEquivalence

end CategoryTheory.Monoidal
