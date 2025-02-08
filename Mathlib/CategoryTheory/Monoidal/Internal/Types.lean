/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic

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
  mul_one x := by convert congr_fun A.mul_one (x, PUnit.unit)
  mul_assoc x y z := by convert congr_fun A.mul_assoc ((x, y), z)

/-- Converting a monoid object in `Type` to a bundled monoid.
-/
noncomputable def functor : Mon_ (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_fun f.one_hom PUnit.unit
      map_mul' := fun x y => congr_fun f.mul_hom (x, y) }

/-- Converting a bundled monoid to a monoid object in `Type`.
-/
noncomputable def inverse : MonCat.{u} ⥤ Mon_ (Type u) where
  obj A :=
    { X := A
      one := fun _ => 1
      mul := fun p => p.1 * p.2
      one_mul := by ext ⟨_, _⟩; dsimp; simp
      mul_one := by ext ⟨_, _⟩; dsimp; simp
      mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [mul_assoc] }
  map f := { hom := f }

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
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := MonCat.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          inv := MonCat.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl } })
      (by aesop_cat)

/-- The equivalence `Mon_ (Type u) ≌ MonCat.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon_.forget (Type u) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

noncomputable instance monTypeInhabited : Inhabited (Mon_ (Type u)) :=
  ⟨MonTypeEquivalenceMon.inverse.obj (MonCat.of PUnit)⟩

namespace CommMonTypeEquivalenceCommMon

instance commMonCommMonoid (A : CommMon_ (Type u)) : CommMonoid A.X :=
  { MonTypeEquivalenceMon.monMonoid A.toMon_ with
    mul_comm := fun x y => by convert congr_fun A.mul_comm (y, x) }

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
      mul_comm := by
        ext ⟨x : A, y : A⟩
        exact CommMonoid.mul_comm y x }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f)

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
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := CommMonCat.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          inv := CommMonCat.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl } })
      (by aesop_cat)

namespace GrpTypeEquivalenceGrp

instance grpGroup (A : Grp_ (Type u)) : Group A.X :=
  { MonTypeEquivalenceMon.monMonoid A.toMon_ with
    inv := A.inv
    inv_mul_cancel a := congr_fun A.left_inv a }

/-- Converting a group object in `Type u` into a group. -/
noncomputable def functor : Grp_ (Type u) ⥤ Grp.{u} where
  obj A := Grp.of A.X
  map f := Grp.ofHom (MonTypeEquivalenceMon.functor.map f).hom

/-- Converting a group into a group object in `Type u`. -/
noncomputable def inverse : Grp.{u} ⥤ Grp_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ Grp MonCat).obj A) with
      inv := ((·⁻¹) : A → A)
      left_inv := by
        ext x
        exact inv_mul_cancel (G := A) x
      right_inv := by
        ext x
        exact mul_inv_cancel (G := A) x }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ Grp MonCat).map f)

end GrpTypeEquivalenceGrp

/-- The category of group objects in `Type u` is equivalent to the category of groups. -/
noncomputable def grpTypeEquivalenceGrp : Grp_ (Type u) ≌ Grp.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := { hom := 𝟙 _ }
          inv := { hom := 𝟙 _ } })
      (by aesop_cat)
  counitIso :=
    NatIso.ofComponents
      (fun A =>
        { hom := Grp.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          inv := Grp.ofHom
            { toFun := id
              map_one' := rfl
              map_mul' := fun _ _ => rfl } })
      (by aesop_cat)

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `CommMon_ (Type u) ≌ CommMonCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `Grp_ (Type u) ≌ Grp.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ Grp MonCat ≅
      Grp_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
