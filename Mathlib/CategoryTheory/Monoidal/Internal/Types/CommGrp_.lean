/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp_
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# `CommGrp (Type u) ≌ CommGrpCat.{u}`

The category of internal commutative group objects in `Type`
is equivalent to the category of "native" bundled commutative groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists Field

universe v u

open CategoryTheory MonObj

namespace CommGrpTypeEquivalenceCommGrp

instance commGrpCommGroup (A : Type u) [GrpObj A] [IsCommMonObj A] : CommGroup A :=
  { GrpTypeEquivalenceGrp.grpGroup A with
    mul_comm := fun x y => by convert congr_fun (IsCommMonObj.mul_comm A) (y, x) }

/-- Converting a commutative group object in `Type u` into a group. -/
noncomputable def functor : CommGrp (Type u) ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f).hom

/-- Converting a group into a group object in `Type u`. -/
noncomputable def inverse : CommGrpCat.{u} ⥤ CommGrp (Type u) where
  obj A :=
    { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrpCat GrpCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrpCat GrpCat).map f)

@[simp]
theorem inverse_obj_X {A : CommGrpCat.{u}} : (inverse.obj A).X = A := rfl
@[simp]
theorem inverse_obj_one {A : CommGrpCat.{u}} {x} : η[(inverse.obj A).X] x = (1 : A) := rfl
@[simp]
theorem inverse_obj_mul {A : CommGrpCat.{u}} {p} : μ[(inverse.obj A).X] p = (p.1 : A) * p.2 := rfl
@[simp]
theorem inverse_obj_inv {A : CommGrpCat.{u}} {x} : ι[(inverse.obj A).X] x = (x : A)⁻¹ := rfl

end CommGrpTypeEquivalenceCommGrp

/-- The category of commutative group objects in `Type u` is equivalent to the category of
commutative groups. -/
noncomputable def commGrpTypeEquivalenceCommGrp : CommGrp (Type u) ≌ CommGrpCat.{u} where
  functor := CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Grp (Type u) ≌ GrpCat.{u}` and `CommGrp (Type u) ≌ CommGrpCat.{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetGrp :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat GrpCat ≅
      CommGrp.forget₂Grp (Type u) ⋙ GrpTypeEquivalenceGrp.functor :=
  Iso.refl _

/-- The equivalences `CommMon (Type u) ≌ CommMonCat.{u}` and `CommGrp (Type u) ≌ CommGrpCat.{u}`
are naturally compatible with the forgetful functors to `GrpCat` and `Grp (Type u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetCommMon :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrpCat CommMonCat ≅
      CommGrp.forget₂CommMon (Type u) ⋙ CommMonTypeEquivalenceCommMon.functor :=
  Iso.refl _
