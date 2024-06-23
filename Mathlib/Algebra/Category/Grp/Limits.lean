/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso

#align_import algebra.category.Group.limits from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/


open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type v} [Category.{w} J]

namespace Grp

variable (F : J ⥤ Grp.{u})

@[to_additive]
instance groupObj (j) : Group ((F ⋙ forget Grp).obj j) :=
  inferInstanceAs <| Group (F.obj j)
set_option linter.uppercaseLean3 false in
#align Group.group_obj Grp.groupObj
set_option linter.uppercaseLean3 false in
#align AddGroup.add_group_obj AddGrp.addGroupObj

/-- The flat sections of a functor into `Grp` form a subgroup of all sections.
-/
@[to_additive
  "The flat sections of a functor into `AddGrp` form an additive subgroup of all sections."]
def sectionsSubgroup : Subgroup (∀ j, F.obj j) :=
  { MonCat.sectionsSubmonoid (F ⋙ forget₂ Grp MonCat) with
    carrier := (F ⋙ forget Grp).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply, MonoidHom.map_inv, inv_inj]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).map_inv (a j), ah f] }
set_option linter.uppercaseLean3 false in
#align Group.sections_subgroup Grp.sectionsSubgroup
set_option linter.uppercaseLean3 false in
#align AddGroup.sections_add_subgroup AddGrp.sectionsAddSubgroup

@[to_additive]
instance sectionsGroup : Group (F ⋙ forget Grp.{u}).sections :=
  (sectionsSubgroup F).toGroup

/-- The projection from `Functor.sections` to a factor as a `MonoidHom`. -/
@[to_additive "The projection from `Functor.sections` to a factor as an `AddMonoidHom`."]
def sectionsπMonoidHom (j : J) : (F ⋙ forget Grp.{u}).sections →* F.obj j where
  toFun x := x.val j
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Small.{u} (Functor.sections (F ⋙ forget Grp))]

@[to_additive]
noncomputable instance limitGroup :
    Group (Types.Small.limitCone.{v, u} (F ⋙ forget Grp.{u})).pt :=
  inferInstanceAs <| Group (Shrink (F ⋙ forget Grp.{u}).sections)
set_option linter.uppercaseLean3 false in
#align Group.limit_group Grp.limitGroup
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_add_group AddGrp.limitAddGroup

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ Grp MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget Grp))

/-- We show that the forgetful functor `Grp ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive "We show that the forgetful functor `AddGrp ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit."]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ Grp.{u} MonCat.{u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : (forget₂ Grp.{u} MonCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ Grp.{u} MonCat.{u}))
    fun c' t =>
    { liftedCone :=
        { pt := Grp.of (Types.Small.limitCone (F ⋙ forget Grp)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ Grp MonCat)
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ Grp MonCat.{u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ Grp MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }
set_option linter.uppercaseLean3 false in
#align Group.forget₂.creates_limit Grp.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂.creates_limit AddGrp.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `Grp`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `Grp`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ Grp.{u} MonCat.{u}))
set_option linter.uppercaseLean3 false in
#align Group.limit_cone Grp.limitCone
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone AddGrp.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Group.limit_cone_is_limit Grp.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone_is_limit AddGrp.limitConeIsLimit

/-- If `(F ⋙ forget Grp).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddGrp).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

end

/-- A functor `F : J ⥤ Grp.{u}` has a limit iff `(F ⋙ forget Grp).sections` is
`u`-small.  -/
@[to_additive "A functor `F : J ⥤ AddGrp.{u}` has a limit iff
`(F ⋙ forget AddGrp).sections` is `u`-small."]
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget Grp).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `Grp.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddGrp.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J Grp.{u} where
  has_limit _ := inferInstance

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} Grp.{u} where
  has_limits_of_shape J _ := { }
set_option linter.uppercaseLean3 false in
#align Group.has_limits_of_size Grp.hasLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.has_limits_of_size AddGrp.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits Grp.{u} :=
  Grp.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.has_limits Grp.hasLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.has_limits AddGrp.hasLimits

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGrp.forget₂AddMonPreservesLimitsOfSize
  "The forgetful functor from additive groups to additive monoids preserves all limits.

  This means the underlying additive monoid of a limit can be computed as a limit in the category of
  additive monoids.",
  to_additive_relevant_arg 2]
noncomputable instance forget₂MonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ Grp.{u} MonCat.{u}) where
  preservesLimitsOfShape {J _} := { }
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits_of_size Grp.forget₂MonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_AddMon_preserves_limits AddGrp.forget₂AddMonPreservesLimitsOfSize

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
  PreservesLimits (forget₂ Grp.{u} MonCat.{u}) :=
  Grp.forget₂MonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits Grp.forget₂MonPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_Mon_preserves_limits AddGrp.forget₂MonPreservesLimits

/-- If `J` is `u`-small, the forgetful functor from `Grp.{u}` preserves limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddGrp.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget Grp.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  "The forgetful functor from additive groups to types preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of types.",
  to_additive_relevant_arg 2]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget Grp.{u}) := inferInstance
set_option linter.uppercaseLean3 false in
#align Group.forget_preserves_limits_of_size Grp.forgetPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_preserves_limits_of_size AddGrp.forgetPreservesLimitsOfSize

@[to_additive]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget Grp.{u}) :=
  Grp.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget_preserves_limits Grp.forgetPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget_preserves_limits AddGrp.forgetPreservesLimits

end Grp

namespace CommGrp

variable (F : J ⥤ CommGrp.{u})

@[to_additive]
instance commGroupObj (j) : CommGroup ((F ⋙ forget CommGrp).obj j) :=
  inferInstanceAs <| CommGroup (F.obj j)
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_obj CommGrp.commGroupObj
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_obj AddCommGrp.addCommGroupObj

@[to_additive]
noncomputable instance limitCommGroup
    [Small.{u} (Functor.sections (F ⋙ forget CommGrp))] :
    CommGroup (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrp.{u})).pt :=
  letI : CommGroup (F ⋙ forget CommGrp.{u}).sections :=
    @Subgroup.toCommGroup (∀ j, F.obj j) _
      (Grp.sectionsSubgroup (F ⋙ forget₂ CommGrp.{u} Grp.{u}))
  inferInstanceAs <| CommGroup (Shrink (F ⋙ forget CommGrp.{u}).sections)
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_comm_group CommGrp.limitCommGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_add_comm_group AddCommGrp.limitAddCommGroup

@[to_additive]
instance : (forget₂ CommGrp.{u} Grp.{u}).ReflectsIsomorphisms :=
    reflectsIsomorphisms_forget₂ _ _

/-- We show that the forgetful functor `CommGrp ⥤ Grp` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive "We show that the forgetful functor `AddCommGrp ⥤ AddGrp` creates limits.

  All we need to do is notice that the limit point has an `AddCommGroup` instance available,
  and then reuse the existing limit."]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ CommGrp Grp.{u}) :=
  createsLimitOfReflectsIso (fun c hc => by
    have : HasLimit _ := ⟨_, hc⟩
    have : Small.{u} (F ⋙ forget CommGrp).sections :=
      Concrete.small_sections_of_hasLimit (F ⋙ forget₂ CommGrp Grp)
    have : Small.{u} ((F ⋙ forget₂ CommGrp Grp ⋙ forget₂ Grp MonCat) ⋙
      forget MonCat).sections := this
    have : Small.{u} ((F ⋙ forget₂ CommGrp Grp) ⋙ forget Grp).sections := this
    exact
      { liftedCone :=
          { pt := CommGrp.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrp)).pt
            π :=
              { app := MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrp Grp.{u} ⋙ forget₂ Grp MonCat.{u})
                naturality := (MonCat.HasLimits.limitCone _).π.naturality } }
        validLift := by apply IsLimit.uniqueUpToIso (Grp.limitConeIsLimit _) hc
        makesLimit :=
          IsLimit.ofFaithful (forget₂ _ Grp.{u} ⋙ forget₂ _ MonCat.{u})
            (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl })
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂.creates_limit CommGrp.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂.creates_limit AddCommGrp.Forget₂.createsLimit

section

variable [Small.{u} (Functor.sections (F ⋙ forget CommGrp))]

/-- A choice of limit cone for a functor into `CommGrp`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
  "A choice of limit cone for a functor into `AddCommGrp`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGrp Grp) ⋙ forget Grp)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGrp))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrp.{u} Grp.{u}))
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_cone CommGrp.limitCone
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_cone AddCommGrp.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
  "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_cone_is_limit CommGrp.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_cone_is_limit AddCommGrp.limitConeIsLimit

/-- If `(F ⋙ forget CommGrp).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddCommGrp).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

end

/-- A functor `F : J ⥤ CommGrp.{u}` has a limit iff `(F ⋙ forget CommGrp).sections` is
`u`-small.  -/
@[to_additive "A functor `F : J ⥤ AddCommGrp.{u}` has a limit iff
`(F ⋙ forget AddCommGrp).sections` is `u`-small."]
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget CommGrp).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `CommGrp.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddCommGrp.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommGrp.{u} where
  has_limit _ := inferInstance

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommGrp.{u}
  where has_limits_of_shape _ _ := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.has_limits_of_size CommGrp.hasLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_limits_of_size AddCommGrp.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits CommGrp.{u} :=
  CommGrp.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommGroup.has_limits CommGrp.hasLimits
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_limits AddCommGrp.hasLimits

@[to_additive]
noncomputable instance forget₂GroupPreservesLimit :
    PreservesLimit F (forget₂ CommGrp.{u} Grp.{u}) where
  preserves {c} hc := by
    have : HasLimit (F ⋙ forget₂ CommGrp Grp) := by
      rw [Grp.hasLimit_iff_small_sections]
      change Small.{u} (F ⋙ forget CommGrp).sections
      rw [← CommGrp.hasLimit_iff_small_sections]
      exact ⟨_, hc⟩
    exact isLimitOfPreserves _ hc

@[to_additive]
noncomputable instance forget₂GroupPreservesLimitsOfShape :
    PreservesLimitsOfShape J (forget₂ CommGrp.{u} Grp.{u}) where

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to additive groups preserves all limits.
  (That is, the underlying group could have been computed instead as limits in the category
    of additive groups.)",
  to_additive_relevant_arg 2]
noncomputable instance forget₂GroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrp.{u} Grp.{u}) where
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_Group_preserves_limits_of_size CommGrp.forget₂GroupPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddGroup_preserves_limits AddCommGrp.forget₂AddGroupPreservesLimitsOfSize

@[to_additive]
noncomputable instance forget₂GroupPreservesLimits :
    PreservesLimits (forget₂ CommGrp Grp.{u}) :=
  CommGrp.forget₂GroupPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_Group_preserves_limits CommGrp.forget₂GroupPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_Group_preserves_limits AddCommGrp.forget₂AddGroupPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimitsAux
  "An auxiliary declaration to speed up typechecking."]
noncomputable def forget₂CommMonPreservesLimitsAux
    [Small.{u} (F ⋙ forget CommGrp).sections] :
    IsLimit ((forget₂ CommGrp.{u} CommMonCat.{u}).mapCone (limitCone.{v, u} F)) :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGrp))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrp.{u} CommMonCat.{u})
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_aux CommGrp.forget₂CommMonPreservesLimitsAux
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits_aux AddCommGrp.forget₂AddCommMonPreservesLimitsAux

/-- If `J` is `u`-small, the forgetful functor from `CommGrp.{u}` to `CommMonCat.{u}`
preserves limits of shape `J`. -/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimitsOfShape
  "If `J` is `u`-small, the forgetful functor from `AddCommGrp.{u}`
  to `AddCommMonCat.{u}` preserves limits of shape `J`."]
noncomputable instance forget₂CommMonPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget₂ CommGrp.{u} CommMonCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
      (forget₂CommMonPreservesLimitsAux.{v, u} F)

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimitsOfSize
  "The forgetful functor from additive commutative groups to additive commutative monoids
  preserves all limits. (That is, the underlying additive commutative monoids could have been
  computed instead as limits in the category of additive commutative monoids.)"]
noncomputable instance forget₂CommMonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrp CommMonCat.{u}) where
  preservesLimitsOfShape := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_of_size CommGrp.forget₂CommMonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits AddCommGrp.forget₂AddCommMonPreservesLimitsOfSize

/-- If `J` is `u`-small, the forgetful functor from `CommGrp.{u}` preserves limits of
shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddCommGrp.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommGrp.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to types preserves all limits.
  (That is, the underlying types could have been computed instead as limits in the category of
  types.)"]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget CommGrp.{u}) := inferInstance
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_preserves_limits_of_size CommGrp.forgetPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_preserves_limits AddCommGrp.forgetPreservesLimitsOfSize

noncomputable instance _root_.AddCommGrp.forgetPreservesLimits :
    PreservesLimits (forget AddCommGrp.{u}) :=
  AddCommGrp.forgetPreservesLimitsOfSize.{u, u}

@[to_additive existing]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget CommGrp.{u}) :=
  CommGrp.forgetPreservesLimitsOfSize.{u, u}

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGrp) : HasProduct f := by infer_instance

end CommGrp

namespace AddCommGrp

/-- The categorical kernel of a morphism in `AddCommGrp`
agrees with the usual group-theoretical kernel.
-/
def kernelIsoKer {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    kernel f ≅ AddCommGrp.of f.ker where
  hom :=
    { toFun := fun g => ⟨kernel.ι f g, DFunLike.congr_fun (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp [(AddSubgroup.coe_zero _).symm]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        change _ = _ + _
        dsimp
        simp }
  inv := kernel.lift f (AddSubgroup.subtype f.ker) <| by
    -- Porting note (#10936): used to be `tidy`, but `aesop` can't do it
    refine DFunLike.ext _ _ ?_
    rintro ⟨x, (hx : f _ = 0)⟩
    exact hx
  hom_inv_id := by
    -- Porting note: it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext x
    dsimp
    apply DFunLike.congr_fun (kernel.lift_ι f _ _)
  inv_hom_id := by
    apply AddCommGrp.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    simp only [ZeroHom.coe_mk, Function.comp_apply, id_eq]
    apply DFunLike.congr_fun (kernel.lift_ι f _ _)
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker AddCommGrp.kernelIsoKer

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by ext; rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_hom_comp_subtype AddCommGrp.kernelIsoKer_hom_comp_subtype

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker := by
  ext
  simp [kernelIsoKer]
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_inv_comp_ι AddCommGrp.kernelIsoKer_inv_comp_ι

-- Porting note: explicitly add what to be synthesized under `simps!`, because other lemmas
-- automatically generated is not in normal form
/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `AddSubgroup.subtype` map.
-/
@[simps! hom_left_apply_coe inv_left_apply]
def kernelIsoKerOver {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGrp.of f.ker) (AddSubgroup.subtype f.ker) :=
  Over.isoMk (kernelIsoKer f)
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_over AddCommGrp.kernelIsoKerOver

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGrp.kernelIsoKerOver_inv_left_apply
  AddCommGrp.kernelIsoKerOver_hom_left_apply_coe

end AddCommGrp
