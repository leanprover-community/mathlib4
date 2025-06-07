/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.Algebra.Category.Grp.Basic

/-!
# `Grp_ (Type u) ≌ Grp.{u}`

The category of internal group objects in `Type`
is equivalent to the category of "native" bundled groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

universe v u

open CategoryTheory Mon_Class

namespace GrpTypeEquivalenceGrp

instance grpGroup (A : Type u) [Grp_Class A] : Group A :=
  { MonTypeEquivalenceMon.monMonoid A with
    inv := ι[A]
    inv_mul_cancel a := congr_fun (Grp_Class.left_inv A) a }

/-- Converting a group object in `Type u` into a group. -/
noncomputable def functor : Grp_ (Type u) ⥤ Grp.{u} where
  obj A := Grp.of A.X
  map f := Grp.ofHom (MonTypeEquivalenceMon.functor.map f).hom

/-- Converting a group into a group object in `Type u`. -/
noncomputable def inverse : Grp.{u} ⥤ Grp_ (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ Grp MonCat).obj A) with
      grp :=
        { inv := ((·⁻¹) : A → A)
          left_inv' := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv' := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := MonTypeEquivalenceMon.inverse.map ((forget₂ Grp MonCat).map f)

end GrpTypeEquivalenceGrp

/-- The category of group objects in `Type u` is equivalent to the category of groups. -/
noncomputable def grpTypeEquivalenceGrp : Grp_ (Type u) ≌ Grp.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by aesop_cat)

/-- The equivalences `Mon_ (Type u) ≌ MonCat.{u}` and `Grp_ (Type u) ≌ Grp.{u}`
are naturally compatible with the forgetful functors to `MonCat` and `Mon_ (Type u)`.
-/
noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ Grp MonCat ≅
      Grp_.forget₂Mon_ (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
