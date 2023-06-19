/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.internal.types
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.Mon.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Types.Symmetric

/-!
# `Mon_ (Type u) ≌ Mon.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/


universe v u

open CategoryTheory

namespace monTypeEquivalenceMon

instance monMonoid (A : Mon_ (Type u)) : Monoid A.pt where
  one := A.one PUnit.unit
  mul x y := A.mul (x, y)
  one_mul x := by convert congr_fun A.one_mul (PUnit.unit, x)
  mul_one x := by convert congr_fun A.mul_one (x, PUnit.unit)
  mul_assoc x y z := by convert congr_fun A.mul_assoc ((x, y), z)
#align Mon_Type_equivalence_Mon.Mon_monoid MonTypeEquivalenceMon.monMonoid

/-- Converting a monoid object in `Type` to a bundled monoid.
-/
def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := ⟨A.pt⟩
  map A B f :=
    { toFun := f.Hom
      map_one' := congr_fun f.OneHom PUnit.unit
      map_mul' := fun x y => congr_fun f.MulHom (x, y) }
#align Mon_Type_equivalence_Mon.functor MonTypeEquivalenceMon.functor

/-- Converting a bundled monoid to a monoid object in `Type`.
-/
def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A :=
    { pt := A
      one := fun _ => 1
      mul := fun p => p.1 * p.2
      one_mul' := by ext ⟨_, _⟩; dsimp; simp
      mul_one' := by ext ⟨_, _⟩; dsimp; simp
      mul_assoc' := by ext ⟨⟨x, y⟩, z⟩; simp [mul_assoc] }
  map A B f := { Hom := f }
#align Mon_Type_equivalence_Mon.inverse MonTypeEquivalenceMon.inverse

end monTypeEquivalenceMon

open monTypeEquivalenceMon

/-- The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def monTypeEquivalenceMon : Mon_ (Type u) ≌ MonCat.{u} where
  Functor := Functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom := { Hom := 𝟙 _ }
          inv := { Hom := 𝟙 _ } })
      (by tidy)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by tidy)
#align Mon_Type_equivalence_Mon monTypeEquivalenceMon

/-- The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun A => Iso.refl _) (by tidy)
#align Mon_Type_equivalence_Mon_forget monTypeEquivalenceMonForget

instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩
#align Mon_Type_inhabited monTypeInhabited

namespace commMonTypeEquivalenceCommMon

instance commMonCommMonoid (A : CommMon_ (Type u)) : CommMonoid A.pt :=
  { MonTypeEquivalenceMon.monMonoid A.toMon_ with
    mul_comm := fun x y => by convert congr_fun A.mul_comm (y, x) }
#align CommMon_Type_equivalence_CommMon.CommMon_comm_monoid CommMonTypeEquivalenceCommMon.commMonCommMonoid

/-- Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
def functor : CommMon_ (Type u) ⥤ CommMonCat.{u} where
  obj A := ⟨A.pt⟩
  map A B f := MonTypeEquivalenceMon.functor.map f
#align CommMon_Type_equivalence_CommMon.functor CommMonTypeEquivalenceCommMon.functor

/-- Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
def inverse : CommMonCat.{u} ⥤ CommMon_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      mul_comm' := by ext ⟨x, y⟩; exact CommMonoid.mul_comm y x }
  map A B f := MonTypeEquivalenceMon.inverse.map f
#align CommMon_Type_equivalence_CommMon.inverse CommMonTypeEquivalenceCommMon.inverse

end commMonTypeEquivalenceCommMon

open commMonTypeEquivalenceCommMon

/-- The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMonCat.{u} where
  Functor := Functor
  inverse := inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom := { Hom := 𝟙 _ }
          inv := { Hom := 𝟙 _ } })
      (by tidy)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { Hom :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl }
          inv :=
            { toFun := id
              map_one' := rfl
              map_mul' := fun x y => rfl } })
      (by tidy)
#align CommMon_Type_equivalence_CommMon commMonTypeEquivalenceCommMon

/-- The equivalences `Mon_ (Type u) ≌ Mon.{u}` and `CommMon_ (Type u) ≌ CommMon.{u}`
are naturally compatible with the forgetful functors to `Mon` and `Mon_ (Type u)`.
-/
def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  NatIso.ofComponents (fun A => Iso.refl _) (by tidy)
#align CommMon_Type_equivalence_CommMon_forget commMonTypeEquivalenceCommMonForget

instance commMonTypeInhabited : Inhabited (CommMon_ (Type u)) :=
  ⟨CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of PUnit)⟩
#align CommMon_Type_inhabited commMonTypeInhabited

