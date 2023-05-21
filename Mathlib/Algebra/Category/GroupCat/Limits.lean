/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.limits
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Over
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
-- Porting note : need `CategoryTheory.reflectsIsomorphisms_forget₂`
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

variable {J : Type v} [SmallCategory J]

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `GroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs)
  "An alias for `AddGroupCat.{max u v}`, to deal around unification issues."]
abbrev GroupCatMax.{u1, u2} := GroupCat.{max u1 u2}


namespace GroupCat

@[to_additive]
instance groupObj (F : J ⥤ GroupCatMax.{v, u}) (j) : Group ((F ⋙ forget GroupCat).obj j) := by
  change Group (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align Group.group_obj GroupCat.groupObj
set_option linter.uppercaseLean3 false in
#align AddGroup.add_group_obj AddGroupCat.addGroupObj

/-- The flat sections of a functor into `Group` form a subgroup of all sections.
-/
@[to_additive
      "The flat sections of a functor into `AddGroup` form an additive subgroup of all sections."]
def sectionsSubgroup (F : J ⥤ GroupCat) : Subgroup (∀ j, F.obj j) :=
  {
    MonCat.sectionsSubmonoid
      (F ⋙ forget₂ GroupCat
          MonCat) with
    carrier := (F ⋙ forget GroupCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply, MonoidHom.map_inv, inv_inj]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).map_inv (a j), ah f] }
set_option linter.uppercaseLean3 false in
#align Group.sections_subgroup GroupCat.sectionsSubgroup
set_option linter.uppercaseLean3 false in
#align AddGroup.sections_add_subgroup AddGroupCat.sectionsAddSubgroup

@[to_additive]
instance limitGroup (F : J ⥤ GroupCatMax.{v, u}) :
    Group (Types.limitCone.{v, u} (F ⋙ forget GroupCat)).pt := by
  change Group (sectionsSubgroup.{v, u} F)
  infer_instance
set_option linter.uppercaseLean3 false in
#align Group.limit_group GroupCat.limitGroup
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_add_group AddGroupCat.limitAddGroup

/-- We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available, and then reuse
the existing limit. -/
@[to_additive
      "We show that the forgetful functor `AddGroup ⥤ AddMon` creates limits.\n\nAll we need to do is notice that the limit point has an `add_group` instance available, and then\nreuse the existing limit."]
noncomputable instance Forget₂.createsLimit (F : J ⥤ GroupCatMax.{v, u}) :
    CreatesLimit F (forget₂ GroupCatMax.{v, u} MonCatMax.{v, u}) :=
  -- Porting note: need to add `forget₂ Grp Mon` reflects isomorphism
  letI : ReflectsIsomorphisms (forget₂ GroupCatMax.{v, u} MonCatMax.{v, u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GroupCat.{max v u} MonCat.{max v u}))
    fun c' t =>
    { liftedCone :=
        { pt := GroupCat.of (Types.limitCone (F ⋙ forget GroupCatMax)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ GroupCatMax MonCatMax)
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ GroupCat MonCat.{max v u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ GroupCat MonCat.{max v u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }
set_option linter.uppercaseLean3 false in
#align Group.forget₂.creates_limit GroupCat.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂.creates_limit AddGroupCat.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `Group`.\n(Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone (F : J ⥤ GroupCatMax.{v, u}) : Cone F :=
  -- Porting note: add this instance to help Lean unify universe levels
  letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
    (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
  liftLimit
    (limit.isLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}))
set_option linter.uppercaseLean3 false in
#align Group.limit_cone GroupCat.limitCone
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone AddGroupCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone.\n(Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit (F : J ⥤ GroupCatMax.{v, u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Group.limit_cone_is_limit GroupCat.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone_is_limit AddGroupCat.limitConeIsLimit

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} GroupCatMax.{v, u}
    where has_limits_of_shape J _ :=
    { has_limit :=
        -- Porting note: add this instance to help Lean unify universe levels
        fun F => letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
          (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
        hasLimit_of_created F (forget₂ GroupCatMax.{v, u} MonCat.{max v u}) }
set_option linter.uppercaseLean3 false in
#align Group.has_limits_of_size GroupCat.hasLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.has_limits_of_size AddGroupCat.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits GroupCat.{u} :=
  GroupCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.has_limits GroupCat.hasLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.has_limits AddGroupCat.hasLimits

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGroupCat.forget₂AddMonPreservesLimits
      "The forgetful functor from additive groups\nto additive monoids preserves all limits.\n\nThis means the underlying additive monoid of a limit can be computed as a limit in the category of\nadditive monoids."]
noncomputable instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ GroupCatMax.{v, u} MonCat.{max v u})
    where preservesLimitsOfShape {J _} := { preservesLimit := fun {F} =>
      -- Porting note: add this instance to help Lean unify universe levels
      letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
        (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
      inferInstance }
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits_of_size GroupCat.forget₂MonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_AddMon_preserves_limits AddGroupCat.forget₂AddMonPreservesLimits

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
  PreservesLimits (forget₂ GroupCat.{u} MonCat.{u}) :=
  GroupCat.forget₂MonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits GroupCat.forget₂MonPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_Mon_preserves_limits AddGroupCat.forget₂MonPreservesLimits

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive groups to types preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
noncomputable instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget GroupCatMax.{v, u})
  where preservesLimitsOfShape {J _} :=
  { preservesLimit := fun {F} =>
      -- Porting note: add these instances to help Lean unify universe levels
      letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
        (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
      letI h1 := GroupCat.forget₂MonPreservesLimitsOfSize.{v, u}
      letI h2 := MonCat.forgetPreservesLimitsOfSize.{v, u}
      Limits.compPreservesLimit (K := F)
        (forget₂ GroupCatMax.{v, u} MonCat.{max v u})
        (forget MonCat.{max v u}) }
set_option linter.uppercaseLean3 false in
#align Group.forget_preserves_limits_of_size GroupCat.forgetPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_preserves_limits_of_size AddGroupCat.forgetPreservesLimitsOfSize

@[to_additive]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget GroupCat.{u}) :=
  GroupCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget_preserves_limits GroupCat.forgetPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_preserves_limits AddGroupCat.forgetPreservesLimits

end GroupCat

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommGroupCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs)
  "An alias for `AddCommGroupCat.{max u v}`, to deal around unification issues."]
abbrev CommGroupCatMax.{u1, u2} := CommGroupCat.{max u1 u2}

namespace CommGroupCat

@[to_additive]
instance commGroupObj (F : J ⥤ CommGroupCatMax.{v, u}) (j) :
    CommGroup ((F ⋙ forget CommGroupCatMax).obj j) := by
  change CommGroup (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_obj CommGroupCat.commGroupObj
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_obj AddCommGroupCat.addCommGroupObj

@[to_additive]
noncomputable instance limitCommGroup (F : J ⥤ CommGroupCatMax.{v, u}) :
    CommGroup (Types.limitCone (F ⋙ forget CommGroupCatMax.{v, u})).pt :=
  @Subgroup.toCommGroup (∀ j, F.obj j) _
    (GroupCat.sectionsSubgroup.{v, max v u} (F ⋙ forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}))
#align CommGroup.limit_comm_group CommGroupCat.limitCommGroup
#align AddCommGroup.limit_add_comm_group AddCommGroupCat.limitAddCommGroup

/-- We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
@[to_additive
      "We show that the forgetful functor `AddCommGroup ⥤ AddGroup` creates limits.\n\nAll we need to do is notice that the limit point has an `add_comm_group` instance available, and\nthen reuse the existing limit."]
instance Forget₂.createsLimit (F : J ⥤ CommGroupCat.{max v u}) :
    CreatesLimit F (forget₂ CommGroupCat GroupCat.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommGroupCat.of (Types.limitCone (F ⋙ forget CommGroupCat)).pt
          π :=
            { app :=
                MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGroupCat GroupCat.{max v u} ⋙ forget₂ GroupCat MonCat.{max v u})
              naturality' := (MonCat.HasLimits.limitCone _).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (GroupCat.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ GroupCat.{max v u} ⋙ forget₂ _ MonCat.{max v u})
          (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }
#align CommGroup.forget₂.creates_limit CommGroupCat.Forget₂.createsLimit
#align AddCommGroup.forget₂.creates_limit AddCommGroupCat.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `CommGroup`.\n(Generally, you'll just want to use `limit F`.)"]
def limitCone (F : J ⥤ CommGroupCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGroupCat GroupCat.{max v u}))
#align CommGroup.limit_cone CommGroupCat.limitCone
#align AddCommGroup.limit_cone AddCommGroupCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone.\n(Generally, you'll just wantto use `limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ CommGroupCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommGroup.limit_cone_is_limit CommGroupCat.limitConeIsLimit
#align AddCommGroup.limit_cone_is_limit AddCommGroupCat.limitConeIsLimit

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommGroupCat.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F => has_limit_of_created F (forget₂ CommGroupCat GroupCat.{max v u}) }
#align CommGroup.has_limits_of_size CommGroupCat.hasLimitsOfSize
#align AddCommGroup.has_limits_of_size AddCommGroupCat.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits CommGroupCat.{u} :=
  CommGroupCat.hasLimitsOfSize.{u, u}
#align CommGroup.has_limits CommGroupCat.hasLimits
#align AddCommGroup.has_limits AddCommGroupCat.hasLimits

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive AddCommGroupCat.forget₂AddGroupPreservesLimits
      "The forgetful functor from additive commutative groups to groups preserves all limits.\n(That is, the underlying group could have been computed instead as limits in the category\nof additive groups.)"]
instance forget₂GroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGroupCat GroupCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommGroup.forget₂_Group_preserves_limits_of_size CommGroupCat.forget₂GroupPreservesLimitsOfSize
#align AddCommGroup.forget₂_AddGroup_preserves_limits AddCommGroupCat.forget₂AddGroupPreservesLimits

@[to_additive]
instance forget₂GroupPreservesLimits : PreservesLimits (forget₂ CommGroupCat GroupCat.{u}) :=
  CommGroupCat.forget₂GroupPreservesLimitsOfSize.{u, u}
#align CommGroup.forget₂_Group_preserves_limits CommGroupCat.forget₂GroupPreservesLimits
#align AddCommGroup.forget₂_Group_preserves_limits AddCommGroupCat.forget₂GroupPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimitsAux
      "An auxiliary declaration to speed up typechecking."]
def forget₂CommMonPreservesLimitsAux (F : J ⥤ CommGroupCat.{max v u}) :
    IsLimit ((forget₂ CommGroupCat CommMonCat).mapCone (limitCone F)) :=
  CommMonCat.limitConeIsLimit (F ⋙ forget₂ CommGroupCat CommMonCat)
#align CommGroup.forget₂_CommMon_preserves_limits_aux CommGroupCat.forget₂CommMonPreservesLimitsAux
#align AddCommGroup.forget₂_AddCommMon_preserves_limits_aux AddCommGroupCat.forget₂AddCommMonPreservesLimitsAux

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimits
      "The forgetful functor from additive commutative groups to additive commutative monoids preserves\nall limits. (That is, the underlying additive commutative monoids could have been computed instead\nas limits in the category of additive commutative monoids.)"]
instance forget₂CommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGroupCat CommMonCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_CommMon_preserves_limits_aux F) }
#align CommGroup.forget₂_CommMon_preserves_limits_of_size CommGroupCat.forget₂CommMonPreservesLimitsOfSize
#align AddCommGroup.forget₂_AddCommMon_preserves_limits AddCommGroupCat.forget₂AddCommMonPreservesLimits

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommGroupCat.forgetPreservesLimits
      "The forgetful functor from additive commutative groups to types preserves all limits. (That is,\nthe underlying types could have been computed instead as limits in the category of types.)"]
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommGroupCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommGroupCat GroupCat) (forget GroupCat) }
#align CommGroup.forget_preserves_limits_of_size CommGroupCat.forgetPreservesLimitsOfSize
#align AddCommGroup.forget_preserves_limits AddCommGroupCat.forgetPreservesLimits

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGroupCat) : HasProduct f := by infer_instance

end CommGroupCat

namespace AddCommGroupCat

/-- The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
def kernelIsoKer {G H : AddCommGroupCat.{u}} (f : G ⟶ H) : kernel f ≅ AddCommGroupCat.of f.ker where
  Hom :=
    { toFun := fun g =>
        ⟨kernel.ι f g, by
          -- TODO where is this `has_coe_t_aux.coe` coming from? can we prevent it appearing?
          change (kernel.ι f) g ∈ f.ker
          simp [AddMonoidHom.mem_ker]⟩
      map_zero' := by
        ext
        simp
      map_add' := fun g g' => by
        ext
        simp }
  inv := kernel.lift f (AddSubgroup.subtype f.ker) (by tidy)
  hom_inv_id' := by
    apply equalizer.hom_ext _
    ext
    simp
  inv_hom_id' := by
    apply AddCommGroupCat.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    simp
#align AddCommGroup.kernel_iso_ker AddCommGroupCat.kernelIsoKer

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGroupCat} (f : G ⟶ H) :
    (kernelIsoKer f).Hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by ext <;> rfl
#align AddCommGroup.kernel_iso_ker_hom_comp_subtype AddCommGroupCat.kernelIsoKer_hom_comp_subtype

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGroupCat} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker := by
  ext
  simp [kernel_iso_ker]
#align AddCommGroup.kernel_iso_ker_inv_comp_ι AddCommGroupCat.kernelIsoKer_inv_comp_ι

/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps]
def kernelIsoKerOver {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGroupCat.of f.ker) (AddSubgroup.subtype f.ker) :=
  Over.isoMk (kernelIsoKer f) (by simp)
#align AddCommGroup.kernel_iso_ker_over AddCommGroupCat.kernelIsoKerOver

end AddCommGroupCat
