/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.Algebra.Category.Grp.Basic

/-!
# `Grp_ (Type u) ≌ GrpCat.{u}`

The category of internal group objects in `Type`
is equivalent to the category of "native" bundled groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists Field

universe v u

open CategoryTheory MonObj

namespace GrpTypeEquivalenceGrp

instance grpGroup (A : Type u) [GrpObj A] : Group A :=
  { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := congr_fun (GrpObj.left_inv A) a }

/-- Converting a group object in `Type u` into a group. -/
noncomputable def functor : Grp_ (Type u) ⥤ GrpCat.{u} where
  obj A := GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f).hom

/-- Converting a group into a group object in `Type u`. -/
noncomputable def inverse : GrpCat.{u} ⥤ Grp_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := ((·⁻¹) : A → A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f)

end GrpTypeEquivalenceGrp

/-- The category of group objects in `Type u` is equivalent to the category of groups. -/
noncomputable def grpTypeEquivalenceGrp : Grp_ (Type u) ≌ GrpCat.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Mon (Type u) ≌ MonCat.{u}` and `Grp_ (Type u) ≌ GrpCat.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon (Type u)`.
-/
noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ GrpCat MonCat ≅
      Grp_.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
