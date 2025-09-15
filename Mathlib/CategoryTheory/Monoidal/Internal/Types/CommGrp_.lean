/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp_
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# `CommGrp_ (Type u) ≌ CommGrp.{u}`

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
noncomputable def functor : CommGrp_ (Type u) ⥤ CommGrp.{u} where
  obj A := CommGrp.of A.X
  map f := CommGrp.ofHom (GrpTypeEquivalenceGrp.functor.map f).hom

/-- Converting a group into a group object in `Type u`. -/
noncomputable def inverse : CommGrp.{u} ⥤ CommGrp_ (Type u) where
  obj A :=
    { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrp Grp).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrp Grp).map f)

@[simp]
theorem inverse_obj_X {A : CommGrp.{u}} : (inverse.obj A).X = A := rfl
@[simp]
theorem inverse_obj_one {A : CommGrp.{u}} {x} : η[(inverse.obj A).X] x = (1 : A) := rfl
@[simp]
theorem inverse_obj_mul {A : CommGrp.{u}} {p} : μ[(inverse.obj A).X] p = (p.1 : A) * p.2 := rfl
@[simp]
theorem inverse_obj_inv {A : CommGrp.{u}} {x} : ι[(inverse.obj A).X] x = (x : A)⁻¹ := rfl

end CommGrpTypeEquivalenceCommGrp

/-- The category of commutative group objects in `Type u` is equivalent to the category of
commutative groups. -/
noncomputable def commGrpTypeEquivalenceCommGrp : CommGrp_ (Type u) ≌ CommGrp.{u} where
  functor := CommGrpTypeEquivalenceCommGrp.functor
  inverse := CommGrpTypeEquivalenceCommGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalences `Grp_ (Type u) ≌ Grp.{u}` and `CommGrp_ (Type u) ≌ CommGrp.{u}`
are naturally compatible with the forgetful functors to `Grp` and `Grp_ (Type u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetGrp :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrp Grp ≅
      CommGrp_.forget₂Grp_ (Type u) ⋙ GrpTypeEquivalenceGrp.functor :=
  Iso.refl _

/-- The equivalences `CommMon_ (Type u) ≌ CommMonCat.{u}` and `CommGrp_ (Type u) ≌ CommGrp.{u}`
are naturally compatible with the forgetful functors to `Grp` and `Grp_ (Type u)`.
-/
noncomputable def commGrpTypeEquivalenceCommGrpForgetCommMon :
    CommGrpTypeEquivalenceCommGrp.functor ⋙ forget₂ CommGrp CommMonCat ≅
      CommGrp_.forget₂CommMon_ (Type u) ⋙ CommMonTypeEquivalenceCommMon.functor :=
  Iso.refl _
