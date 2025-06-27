/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Adjunctions regarding the category of (abelian) groups

This file contains construction of basic adjunctions concerning the category of groups and the
category of abelian groups.

## Main definitions

* `AddCommGrp.free`: constructs the functor associating to a type `X` the free abelian group
  with generators `x : X`.
* `Grp.free`: constructs the functor associating to a type `X` the free group with
  generators `x : X`.
* `Grp.abelianize`: constructs the functor which associates to a group `G` its abelianization `Gᵃᵇ`.

## Main statements

* `AddCommGrp.adj`: proves that `AddCommGrp.free` is the left adjoint
  of the forgetful functor from abelian groups to types.
* `Grp.adj`: proves that `Grp.free` is the left adjoint of the forgetful functor
  from groups to types.
* `abelianizeAdj`: proves that `Grp.abelianize` is left adjoint to the forgetful functor from
  abelian groups to groups.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AddCommGrp

/-- The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGrp where
  obj α := of (FreeAbelianGroup α)
  map f := ofHom (FreeAbelianGroup.map f)
  map_id _ := AddCommGrp.ext FreeAbelianGroup.map_id_apply
  map_comp _ _ := AddCommGrp.ext FreeAbelianGroup.map_comp_apply

@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = FreeAbelianGroup α :=
  rfl

-- This currently can't be a `simp` lemma,
-- because `free_obj_coe` will simplify implicit arguments in the LHS.
-- (The `simpNF` linter will, correctly, complain.)
theorem free_map_coe {α β : Type u} {f : α → β} (x : FreeAbelianGroup α) :
    (free.map f) x = f <$> x :=
  rfl

/-- The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ConcreteCategory.homEquiv.trans FreeAbelianGroup.lift.symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): used to be just `by intros; ext; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp
        apply FreeAbelianGroup.lift_comp }

instance : free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩

instance : (forget AddCommGrp.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

instance : AddCommGrp.free.{u}.IsLeftAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGrp.{u}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  (mono_iff_injective (f : G → H)).mp (Functor.map_mono (forget AddCommGrp) f)

instance : (free.{u}).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    by_cases hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj free _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · simp only [not_isEmpty_iff] at hX
      have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsSplitMono f := IsSplitMono.mk' { retraction := g }
      infer_instance

end AddCommGrp

namespace Grp

/-- The free functor `Type u ⥤ Group` sending a type `X` to the free group with generators `x : X`.
-/
def free : Type u ⥤ Grp where
  obj α := of (FreeGroup α)
  map f := ofHom (FreeGroup.map f)

/-- The free-forgetful adjunction for groups.
-/
def adj : free ⊣ forget Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ConcreteCategory.homEquiv.trans FreeGroup.lift.symm
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): `ext` doesn't apply this theorem anymore
        apply FreeGroup.ext_hom
        intros
        rfl }

instance : (forget Grp.{u}).IsRightAdjoint  :=
  ⟨_, ⟨adj⟩⟩

section Abelianization

/-- The abelianization functor `Group ⥤ CommGroup` sending a group `G` to its abelianization `Gᵃᵇ`.
-/
def abelianize : Grp.{u} ⥤ CommGrp.{u} where
  obj G := CommGrp.of (Abelianization G)
  map f := CommGrp.ofHom (Abelianization.lift (Abelianization.of.comp f.hom))
  map_id := by
    intros
    ext : 1
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr
    rfl
  map_comp := by
    intros
    ext : 1
    apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr
    rfl

/-- The abelianization-forgetful adjuction from `Group` to `CommGroup`. -/
def abelianizeAdj : abelianize ⊣ forget₂ CommGrp.{u} Grp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => ((ConcreteCategory.homEquiv (C := CommGrp)).trans
        Abelianization.lift.symm).trans
        (ConcreteCategory.homEquiv (C := Grp)).symm
      -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): used to be just `by intros; ext1; rfl`.
      homEquiv_naturality_left_symm := by
        intros
        ext
        simp only [Equiv.symm_symm]
        apply Eq.symm
        apply Abelianization.lift.unique
        intros
        apply Abelianization.lift.of }

end Abelianization

end Grp

/-- The functor taking a monoid to its subgroup of units. -/
@[simps!]
def MonCat.units : MonCat.{u} ⥤ Grp.{u} where
  obj R := Grp.of Rˣ
  map f := Grp.ofHom <| Units.map f.hom
  map_id _ := Grp.ext fun _ => Units.ext rfl
  map_comp _ _ := Grp.ext fun _ => Units.ext rfl

/-- The forgetful-units adjunction between `Grp` and `MonCat`. -/
def Grp.forget₂MonAdj : forget₂ Grp MonCat ⊣ MonCat.units.{u} := Adjunction.mk' {
  homEquiv _ Y :=
    { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
      invFun f := MonCat.ofHom ((Units.coeHom Y).comp f.hom) }
  unit :=
    { app X := ofHom (@toUnits X _)
      naturality _ _ _ := Grp.ext fun _ => Units.ext rfl }
  counit :=
    { app X := MonCat.ofHom (Units.coeHom X)
      naturality _ _ _ := MonCat.ext fun _ => rfl } }

instance : MonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨Grp.forget₂MonAdj⟩⟩

/-- The functor taking a monoid to its subgroup of units. -/
@[simps!]
def CommMonCat.units : CommMonCat.{u} ⥤ CommGrp.{u} where
  obj R := CommGrp.of Rˣ
  map f := CommGrp.ofHom <| Units.map f.hom
  map_id _ := CommGrp.ext fun _ => Units.ext rfl
  map_comp _ _ := CommGrp.ext fun _ => Units.ext rfl

/-- The forgetful-units adjunction between `CommGrp` and `CommMonCat`. -/
def CommGrp.forget₂CommMonAdj : forget₂ CommGrp CommMonCat ⊣ CommMonCat.units.{u} :=
  Adjunction.mk' {
    homEquiv := fun _ Y ↦
      { toFun f := ofHom (MonoidHom.toHomUnits f.hom)
        invFun f := CommMonCat.ofHom ((Units.coeHom Y).comp f.hom) }
    unit.app X := ofHom toUnits.toMonoidHom
    -- `aesop` can find the following proof but it takes `0.5`s.
    unit.naturality _ _ _ := CommGrp.ext fun _ => Units.ext rfl
    counit.app X := CommMonCat.ofHom (Units.coeHom X)
    -- `aesop` can find the following proof but it takes `0.5`s.
    counit.naturality _ _ _ := CommMonCat.ext fun _ => rfl
    -- `aesop` can find the following proof but it takes `0.2`s.
    homEquiv_unit := by intros; rfl
    -- `aesop` can find the following proof but it takes `0.2`s.
    homEquiv_counit := by intros; rfl }

instance : CommMonCat.units.{u}.IsRightAdjoint :=
  ⟨_, ⟨CommGrp.forget₂CommMonAdj⟩⟩
