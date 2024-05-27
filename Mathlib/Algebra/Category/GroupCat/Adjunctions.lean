/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.GroupTheory.FreeAbelianGroup

#align_import algebra.category.Group.adjunctions from "leanprover-community/mathlib"@"ecef68622cf98f6d42c459e5b5a079aeecdd9842"


/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGroupCat.free`: constructs the functor associating to a type `X` the free abelian group
  with generators `x : X`.
* `GroupCat.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGroupCat.adj`: proves that `AddCommGroupCat.free` is the left adjoint
  of the forgetful functor from abelian groups to types.
* `GroupCat.adj`: proves that `GroupCat.free` is the left adjoint of the forgetful functor
  from groups to types.
* `abelianizeAdj`: proves that `abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

set_option linter.uppercaseLean3 false -- `AddCommGroup`

noncomputable section

universe u

open CategoryTheory

namespace AddCommGroupCat

open scoped Classical

/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroupCat where
  obj α := of (FreeAbelianGroup α)
  map := FreeAbelianGroup.map
  map_id _ := AddMonoidHom.ext FreeAbelianGroup.map_id_apply
  map_comp _ _ := AddMonoidHom.ext FreeAbelianGroup.map_comp_apply
#align AddCommGroup.free AddCommGroupCat.free

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl
#align AddCommGroup.free_obj_coe AddCommGroupCat.free_obj_coe

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl
#align AddCommGroup.free_map_coe AddCommGroupCat.free_map_coe

/-- The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeAbelianGroup.lift.symm
      -- Porting note: used to be just `by intros; ext; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp only [Equiv.symm_symm]
        apply FreeAbelianGroup.lift_comp }
#align AddCommGroup.adj AddCommGroupCat.adj

instance : (forget AddCommGroupCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGroupCat.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective (f : G → H)).mp (Functor.map_mono (forget AddCommGroupCat) f)


end AddCommGroupCat

namespace GroupCat

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ GroupCat where
  obj α := of (FreeGroup α)
  map := FreeGroup.map
  map_id := by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
  map_comp := by
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    intros; ext1; erw [← FreeGroup.map.unique] <;> intros <;> rfl
#align Group.free GroupCat.free

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget GroupCat.{u} :=
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
#align Group.adj GroupCat.adj

instance : (forget GroupCat.{u}).IsRightAdjoint  :=
  ⟨_, ⟨adj⟩⟩

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G := CommGroupCat.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)
  map_id := by
    intros; simp only [coe_id]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
  map_comp := by
    intros; simp only [coe_comp]
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
#align abelianize GroupCat.abelianize

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`. -/
def abelianizeAdj : abelianize ⊣ forget₂ CommGroupCat.{u} GroupCat.{u} :=
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
#align abelianize_adj GroupCat.abelianizeAdj

end Abelianization

end GroupCat

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def MonCat.units : MonCat.{u} ⥤ GroupCat.{u} where
  obj R := GroupCat.of Rˣ
  map f := GroupCat.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align Mon.units MonCat.units

/-- The forgetful-units adjunction between `GroupCat` and `MonCat`. -/
def GroupCat.forget₂MonAdj : forget₂ GroupCat MonCat ⊣ MonCat.units.{u} where
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
#align Group.forget₂_Mon_adj GroupCat.forget₂MonAdj

instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨GroupCat.forget₂MonAdj⟩⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGroupCat.{u} where
  obj R := CommGroupCat.of Rˣ
  map f := CommGroupCat.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align CommMon.units CommMonCat.units

/-- The forgetful-units adjunction between `CommGroupCat` and `CommMonCat`. -/
def CommGroupCat.forget₂CommMonAdj : forget₂ CommGroupCat CommMonCat ⊣ CommMonCat.units.{u} where
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
#align CommGroup.forget₂_CommMon_adj CommGroupCat.forget₂CommMonAdj

instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGroupCat.forget₂CommMonAdj⟩⟩
