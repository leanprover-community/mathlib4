/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric

#align_import category_theory.monoidal.internal.types from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# `Mon_ (Type u) ≌ MonCat.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/


universe v u

open CategoryTheory

namespace MonTypeEquivalenceMon

instance monMonoid (A : Mon_ (Type u)) : Monoid A.X where
  one := A.one PUnit.unit
  mul x y := A.mul (x, y)
  one_mul x := by convert congr_fun A.one_mul (PUnit.unit, x)
                  -- 🎉 no goals
  mul_one x := by convert congr_fun A.mul_one (x, PUnit.unit)
                        -- 🎉 no goals
                  -- 🎉 no goals
  mul_assoc x y z := by convert congr_fun A.mul_assoc ((x, y), z)
set_option linter.uppercaseLean3 false in
#align Mon_Type_equivalence_Mon.Mon_monoid MonTypeEquivalenceMon.monMonoid

/-- Converting a monoid object in `Type` to a bundled monoid.
-/
noncomputable def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f :=
    { toFun := f.hom
      map_one' := congr_fun f.one_hom PUnit.unit
      map_mul' := fun x y => congr_fun f.mul_hom (x, y) }
set_option linter.uppercaseLean3 false in
#align Mon_Type_equivalence_Mon.functor MonTypeEquivalenceMon.functor

/-- Converting a bundled monoid to a monoid object in `Type`.
-/
noncomputable def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A :=
    { X := A
      one := fun _ => 1
      mul := fun p => p.1 * p.2
      one_mul := by ext ⟨_, _⟩; dsimp; simp
                    -- ⊢ (MonoidalCategory.tensorHom (fun x => 1) (𝟙 ↑A) ≫ fun p => p.fst * p.snd) (f …
                                -- ⊢ 1 * snd✝ = snd✝
                                       -- 🎉 no goals
      mul_one := by ext ⟨_, _⟩; dsimp; simp
                    -- ⊢ ((MonoidalCategory.tensorHom (𝟙 ↑A) fun x => 1) ≫ fun p => p.fst * p.snd) (f …
                                -- ⊢ fst✝ * 1 = fst✝
                                       -- 🎉 no goals
      mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [mul_assoc] }
                      -- ⊢ (MonoidalCategory.tensorHom (fun p => p.fst * p.snd) (𝟙 ↑A) ≫ fun p => p.fst …
                                       -- 🎉 no goals
  map f := { hom := f }
set_option linter.uppercaseLean3 false in
#align Mon_Type_equivalence_Mon.inverse MonTypeEquivalenceMon.inverse

end MonTypeEquivalenceMon

open MonTypeEquivalenceMon

/-- The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
noncomputable def monTypeEquivalenceMon : Mon_ (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
          -- 🎉 no goals
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by aesop_cat)
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Mon_Type_equivalence_Mon monTypeEquivalenceMon

/-- The equivalence `Mon_ (Type u) ≌ MonCat.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun A => Iso.refl _) (by aesop_cat)
                                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Mon_Type_equivalence_Mon_forget monTypeEquivalenceMonForget

noncomputable instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩
set_option linter.uppercaseLean3 false in
#align Mon_Type_inhabited monTypeInhabited

namespace CommMonTypeEquivalenceCommMon

instance commMonCommMonoid (A : CommMon_ (Type u)) : CommMonoid A.X :=
  { MonTypeEquivalenceMon.monMonoid A.toMon_ with
    mul_comm := fun x y => by convert congr_fun A.mul_comm (y, x) }
                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommMon_Type_equivalence_CommMon.CommMon_comm_monoid CommMonTypeEquivalenceCommMon.commMonCommMonoid

/-- Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
noncomputable def functor : CommMon_ (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := MonTypeEquivalenceMon.functor.map f
set_option linter.uppercaseLean3 false in
#align CommMon_Type_equivalence_CommMon.functor CommMonTypeEquivalenceCommMon.functor

/-- Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
noncomputable def inverse : CommMonCat.{u} ⥤ CommMon_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      mul_comm := by
        ext ⟨x : A, y : A⟩
        -- ⊢ ((β_ (Mon_.mk src✝.X src✝.one src✝.mul).X (Mon_.mk src✝.X src✝.one src✝.mul) …
        exact CommMonoid.mul_comm y x }
        -- 🎉 no goals
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f)
set_option linter.uppercaseLean3 false in
#align CommMon_Type_equivalence_CommMon.inverse CommMonTypeEquivalenceCommMon.inverse

end CommMonTypeEquivalenceCommMon

open CommMonTypeEquivalenceCommMon

/-- The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
noncomputable def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
          -- 🎉 no goals
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by aesop_cat)
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommMon_Type_equivalence_CommMon commMonTypeEquivalenceCommMon

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `CommMon_ (Type u) ≌ CommMonCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  NatIso.ofComponents (fun A => Iso.refl _) (by aesop_cat)
                                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align CommMon_Type_equivalence_CommMon_forget commMonTypeEquivalenceCommMonForget

noncomputable instance commMonTypeInhabited : Inhabited (CommMon_ (Type u)) :=
  ⟨CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of PUnit)⟩
set_option linter.uppercaseLean3 false in
#align CommMon_Type_inhabited commMonTypeInhabited
