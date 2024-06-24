/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.FreeAbelianGroup

#align_import algebra.category.Group.adjunctions from "leanprover-community/mathlib"@"ecef68622cf98f6d42c459e5b5a079aeecdd9842"


/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGrp.free`: constructs the functor associating to a type `X` the free abelian group
  with generators `x : X`.
* `Grp.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGrp.adj`: proves that `AddCommGrp.free` is the left adjoint
  of the forgetful functor from abelian groups to types.
* `Grp.adj`: proves that `Grp.free` is the left adjoint of the forgetful functor
  from groups to types.
* `abelianizeAdj`: proves that `abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

set_option linter.uppercaseLean3 false -- `AddCommGroup`

noncomputable section

universe u

open CategoryTheory

namespace AddCommGrp

open scoped Classical

/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGrp where
  obj α := of (FreeAbelianGroup α)
  map := FreeAbelianGroup.map
  map_id _ := AddMonoidHom.ext FreeAbelianGroup.map_id_apply
  map_comp _ _ := AddMonoidHom.ext FreeAbelianGroup.map_comp_apply
#align AddCommGroup.free AddCommGrp.free

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl
#align AddCommGroup.free_obj_coe AddCommGrp.free_obj_coe

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl
#align AddCommGroup.free_map_coe AddCommGrp.free_map_coe

/-- The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeAbelianGroup.lift.symm
      -- Porting note: used to be just `by intros; ext; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp only [Equiv.symm_symm]
        apply FreeAbelianGroup.lift_comp }
#align AddCommGroup.adj AddCommGrp.adj

instance : (forget AddCommGrp.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGrp.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective (f : G → H)).mp (Functor.map_mono (forget AddCommGrp) f)


end AddCommGrp

namespace Grp

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ Grp where
  obj α := of (FreeGroup α)
  map := FreeGroup.map
  map_id := by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
  map_comp := by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
#align Group.free Grp.free

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeGroup.lift.symm
      -- Porting note: used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext1
        simp only [Equiv.symm_symm]
        apply Eq.symm
        apply FreeGroup.lift.unique
        intros
        apply FreeGroup.lift.of }
#align Group.adj Grp.adj

instance : (forget Grp.{u}).IsRightAdjoint  :=
  ⟨_, ⟨adj⟩⟩

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : Grp.{u} ⥤ CommGrp.{u} where
  obj G := CommGrp.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)
  map_id := by
    intros; simp only [coe_id]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
  map_comp := by
    intros; simp only [coe_comp]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
#align abelianize Grp.abelianize

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`. -/
def abelianizeAdj : abelianize ⊣ forget₂ CommGrp.{u} Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G A => Abelianization.lift.symm
      -- Porting note: used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext1
        simp only [Equiv.symm_symm]
        apply Eq.symm
        apply Abelianization.lift.unique
        intros
        apply Abelianization.lift.of }
#align abelianize_adj Grp.abelianizeAdj

end Abelianization

end Grp

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def MonCat.units : MonCat.{u} ⥤ Grp.{u} where
  obj R := Grp.of Rˣ
  map f := Grp.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align Mon.units MonCat.units

/-- The forgetful-units adjunction between `Grp` and `MonCat`. -/
def Grp.forget₂MonAdj : forget₂ Grp MonCat ⊣ MonCat.units.{u} where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f
      invFun := fun f => (Units.coeHom Y).comp f
      left_inv := fun f => MonoidHom.ext fun _ => rfl
      right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with }
      naturality := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit :=
    { app := fun X => Units.coeHom X
      naturality := by intros; exact MonoidHom.ext fun x => rfl }
  homEquiv_unit := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit := MonoidHom.ext fun _ => rfl
#align Group.forget₂_Mon_adj Grp.forget₂MonAdj

instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨Grp.forget₂MonAdj⟩⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrp.{u} where
  obj R := CommGrp.of Rˣ
  map f := CommGrp.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align CommMon.units CommMonCat.units

/-- The forgetful-units adjunction between `CommGrp` and `CommMonCat`. -/
def CommGrp.forget₂CommMonAdj : forget₂ CommGrp CommMonCat ⊣ CommMonCat.units.{u} where
  homEquiv X Y :=
    { toFun := fun f => MonoidHom.toHomUnits f
      invFun := fun f => (Units.coeHom Y).comp f
      left_inv := fun f => MonoidHom.ext fun _ => rfl
      right_inv := fun f => MonoidHom.ext fun _ => Units.ext rfl }
  unit :=
    { app := fun X => { (@toUnits X _).toMonoidHom with }
      naturality := fun X Y f => MonoidHom.ext fun x => Units.ext rfl }
  counit :=
    { app := fun X => Units.coeHom X
      naturality := by intros; exact MonoidHom.ext fun x => rfl }
  homEquiv_unit := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit := MonoidHom.ext fun _ => rfl
#align CommGroup.forget₂_CommMon_adj CommGrp.forget₂CommMonAdj

instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGrp.forget₂CommMonAdj⟩⟩
