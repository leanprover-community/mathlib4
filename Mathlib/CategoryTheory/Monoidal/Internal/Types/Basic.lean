/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# `Mon_ (Type u) ≌ MonCat.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists MonoidWithZero

universe v u

open CategoryTheory Mon_Class

namespace MonTypeEquivalenceMon

instance monMonoid (A : Type u) [Mon_Class A] : Monoid A where
  one := η[A] PUnit.unit
  mul x y := μ[A] (x, y)
  one_mul x := by convert congr_fun (one_mul A) (PUnit.unit, x)
  mul_one x := by convert congr_fun (mul_one A) (x, PUnit.unit)
  mul_assoc x y z := by convert congr_fun (mul_assoc A) ((x, y), z)

/-- Converting a monoid object in `Type` to a bundled monoid.
-/
noncomputable def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_fun (IsMon_Hom.one_hom f.hom) PUnit.unit
      map_mul' x y := congr_fun (IsMon_Hom.mul_hom f.hom) (x, y) }

/-- Converting a bundled monoid to a monoid object in `Type`.
-/
noncomputable def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A :=
    { X := A
      mon :=
        { one := fun _ => 1
          mul := fun p => p.1 * p.2
          one_mul := by ext ⟨_, _⟩; simp
          mul_one := by ext ⟨_, _⟩; simp
          mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [_root_.mul_assoc] } }
  map f := .mk' f

end MonTypeEquivalenceMon

open MonTypeEquivalenceMon

/-- The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
noncomputable def monTypeEquivalenceMon : Mon_ (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalence `Mon_ (Type u) ≌ MonCat.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

noncomputable instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

namespace CommMonTypeEquivalenceCommMon

instance commMonCommMonoid (A : Type u) [Mon_Class A] [IsCommMon A] : CommMonoid A :=
  { MonTypeEquivalenceMon.monMonoid A with
    mul_comm := fun x y => by convert congr_fun (IsCommMon.mul_comm A) (y, x) }

/-- Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
noncomputable def functor : CommMon_ (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := CommMonCat.ofHom (MonTypeEquivalenceMon.functor.map f).hom

/-- Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
noncomputable def inverse : CommMonCat.{u} ⥤ CommMon_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f)

end CommMonTypeEquivalenceCommMon

open CommMonTypeEquivalenceCommMon

/-- The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
noncomputable def commMonTypeEquivalenceCommMon : CommMon_ (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `CommMon_ (Type u) ≌ CommMonCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
