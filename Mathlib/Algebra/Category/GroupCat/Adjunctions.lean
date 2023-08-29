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

* `AddCommGroup.free`: constructs the functor associating to a type `X` the free abelian group with
  generators `x : X`.
* `Group.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGroup.adj`: proves that `AddCommGroup.free` is the left adjoint of the forgetful functor
  from abelian groups to types.
* `Group.adj`: proves that `Group.free` is the left adjoint of the forgetful functor from groups to
  types.
* `abelianize_adj`: proves that `abelianize` is left adjoint to the forgetful functor from
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

@[simp]
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
        -- ⊢ ↑((fun X G => FreeAbelianGroup.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝) = free.map  …
        ext
        -- ⊢ ↑(↑((fun X G => FreeAbelianGroup.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝)) x✝ = ↑(f …
        simp only [Equiv.symm_symm]
        -- ⊢ ↑(↑FreeAbelianGroup.lift (f✝ ≫ g✝)) x✝ = ↑(free.map f✝ ≫ ↑FreeAbelianGroup.l …
        apply FreeAbelianGroup.lift_comp }
        -- 🎉 no goals
#align AddCommGroup.adj AddCommGroupCat.adj

instance : IsRightAdjoint (forget AddCommGroupCat.{u}) :=
  ⟨_, adj⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
-- Porting note: had to elaborate instance of Mono rather than just using `apply_instance`.
example {G H : AddCommGroupCat.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective (FunLike.coe f)).mp (Functor.map_mono (forget AddCommGroupCat) f)


end AddCommGroupCat

namespace GroupCat

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ GroupCat where
  obj α := of (FreeGroup α)
  map := FreeGroup.map
  map_id := by
    intros; ext1; rw [←FreeGroup.map.unique]; intros; rfl
    -- ⊢ { obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map }.map  …
            -- ⊢ ↑({ obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map }.ma …
                  -- ⊢ ∀ (x : X✝), ↑(𝟙 ({ obj := fun α => of (FreeGroup α), map := fun {X Y} => Fre …
                                              -- ⊢ ↑(𝟙 ({ obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map } …
                                                      -- 🎉 no goals
  map_comp := by
    intros; ext1; rw [←FreeGroup.map.unique]; intros; rfl
    -- ⊢ { obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map }.map  …
            -- ⊢ ↑({ obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map }.ma …
                  -- ⊢ ∀ (x : X✝), ↑({ obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGr …
                                              -- ⊢ ↑({ obj := fun α => of (FreeGroup α), map := fun {X Y} => FreeGroup.map }.ma …
                                                      -- 🎉 no goals
#align Group.free GroupCat.free

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget GroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeGroup.lift.symm
      -- Porting note: used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        -- ⊢ ↑((fun X G => FreeGroup.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝) = free.map f✝ ≫ ↑( …
        ext1
        -- ⊢ ↑(↑((fun X G => FreeGroup.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝)) x✝ = ↑(free.map …
        simp only [Equiv.symm_symm]
        -- ⊢ ↑(↑FreeGroup.lift (f✝ ≫ g✝)) x✝ = ↑(free.map f✝ ≫ ↑FreeGroup.lift g✝) x✝
        apply Eq.symm
        -- ⊢ ↑(free.map f✝ ≫ ↑FreeGroup.lift g✝) x✝ = ↑(↑FreeGroup.lift (f✝ ≫ g✝)) x✝
        apply FreeGroup.lift.unique
        -- ⊢ ∀ (x : X'✝), ↑(free.map f✝ ≫ ↑FreeGroup.lift g✝) (FreeGroup.of x) = (f✝ ≫ g✝ …
        intros
        -- ⊢ ↑(free.map f✝ ≫ ↑FreeGroup.lift g✝) (FreeGroup.of x✝) = (f✝ ≫ g✝) x✝
        apply FreeGroup.lift.of }
        -- 🎉 no goals
#align Group.adj GroupCat.adj

instance : IsRightAdjoint (forget GroupCat.{u}) :=
  ⟨_, adj⟩

end GroupCat

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
 -/
def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G :=
    { α := Abelianization G
      str := by infer_instance }
                -- 🎉 no goals
  map f :=
    Abelianization.lift
      { toFun := fun x => Abelianization.of (f x)
        map_one' := by simp
                       -- 🎉 no goals
        map_mul' := by simp }
                       -- 🎉 no goals
  map_id := by
    intros; simp only [MonoidHom.mk_coe, coe_id]
    -- ⊢ { obj := fun G => Bundled.mk (Abelianization ↑G), map := fun {X Y} f => ↑Abe …
            -- ⊢ ↑Abelianization.lift { toOneHom := { toFun := fun x => ↑Abelianization.of (↑ …
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
    -- ⊢ { toOneHom := { toFun := fun x => ↑Abelianization.of (↑(𝟙 X✝) x), map_one' : …
                                                                      -- 🎉 no goals
  map_comp := by
    intros; simp only [coe_comp];
    -- ⊢ { obj := fun G => Bundled.mk (Abelianization ↑G), map := fun {X Y} f => ↑Abe …
            -- ⊢ ↑Abelianization.lift { toOneHom := { toFun := fun x => ↑Abelianization.of (↑ …
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
    -- ⊢ { toOneHom := { toFun := fun x => ↑Abelianization.of (↑(f✝ ≫ g✝) x), map_one …
                                                                      -- 🎉 no goals
#align abelianize abelianize

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`.-/
def abelianizeAdj : abelianize ⊣ forget₂ CommGroupCat.{u} GroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun G A => Abelianization.lift.symm
      -- Porting note: used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        -- ⊢ ↑((fun G A => Abelianization.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝) = abelianize. …
        ext1
        -- ⊢ ↑(↑((fun G A => Abelianization.lift.symm) X'✝ Y✝).symm (f✝ ≫ g✝)) x✝ = ↑(abe …
        simp only [Equiv.symm_symm]
        -- ⊢ ↑(↑Abelianization.lift (f✝ ≫ g✝)) x✝ = ↑(abelianize.map f✝ ≫ ↑Abelianization …
        apply Eq.symm
        -- ⊢ ↑(abelianize.map f✝ ≫ ↑Abelianization.lift g✝) x✝ = ↑(↑Abelianization.lift ( …
        apply Abelianization.lift.unique
        -- ⊢ ∀ (x : ↑X'✝), ↑(abelianize.map f✝ ≫ ↑Abelianization.lift g✝) (↑Abelianizatio …
        intros
        -- ⊢ ↑(abelianize.map f✝ ≫ ↑Abelianization.lift g✝) (↑Abelianization.of x✝) = ↑(f …
        apply Abelianization.lift.of }
        -- 🎉 no goals
#align abelianize_adj abelianizeAdj

end Abelianization

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def MonCat.units : MonCat.{u} ⥤ GroupCat.{u} where
  obj R := GroupCat.of Rˣ
  map f := GroupCat.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align Mon.units MonCat.units

/-- The forgetful-units adjunction between `Group` and `Mon`. -/
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
                       -- ⊢ (MonCat.units ⋙ forget₂ GroupCat MonCat).map f✝ ≫ (fun X => Units.coeHom ↑X) …
                               -- 🎉 no goals
  homEquiv_unit := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit := MonoidHom.ext fun _ => rfl
#align Group.forget₂_Mon_adj GroupCat.forget₂MonAdj

instance : IsRightAdjoint MonCat.units.{u} :=
  ⟨_, GroupCat.forget₂MonAdj⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGroupCat.{u} where
  obj R := CommGroupCat.of Rˣ
  map f := CommGroupCat.ofHom <| Units.map f
  map_id _ := MonoidHom.ext fun _ => Units.ext rfl
  map_comp _ _ := MonoidHom.ext fun _ => Units.ext rfl
#align CommMon.units CommMonCat.units

/-- The forgetful-units adjunction between `CommGroup` and `CommMon`. -/
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
                       -- ⊢ (CommMonCat.units ⋙ forget₂ CommGroupCat CommMonCat).map f✝ ≫ (fun X => Unit …
                               -- 🎉 no goals
  homEquiv_unit := MonoidHom.ext fun _ => Units.ext rfl
  homEquiv_counit := MonoidHom.ext fun _ => rfl
#align CommGroup.forget₂_CommMon_adj CommGroupCat.forget₂CommMonAdj

instance : IsRightAdjoint CommMonCat.units.{u} :=
  ⟨_, CommGroupCat.forget₂CommMonAdj⟩
