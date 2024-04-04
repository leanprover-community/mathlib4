/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.GroupTheory.Subgroup.Basic

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

namespace GroupCat

variable (F : J ⥤ GroupCat.{u})

@[to_additive]
instance groupObj (j) : Group ((F ⋙ forget GroupCat).obj j) :=
  inferInstanceAs <| Group (F.obj j)
set_option linter.uppercaseLean3 false in
#align Group.group_obj GroupCat.groupObj
set_option linter.uppercaseLean3 false in
#align AddGroup.add_group_obj AddGroupCat.addGroupObj

/-- The flat sections of a functor into `GroupCat` form a subgroup of all sections.
-/
@[to_additive
  "The flat sections of a functor into `AddGroupCat` form an additive subgroup of all sections."]
def sectionsSubgroup : Subgroup (∀ j, F.obj j) :=
  { MonCat.sectionsSubmonoid (F ⋙ forget₂ GroupCat MonCat) with
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
instance sectionsGroup : Group (F ⋙ forget GroupCat.{u}).sections :=
  (sectionsSubgroup F).toGroup

variable [Small.{u} (Functor.sections (F ⋙ forget GroupCat))]

@[to_additive]
noncomputable instance limitGroup :
    Group (Types.Small.limitCone.{v, u} (F ⋙ forget GroupCat.{u})).pt :=
  inferInstanceAs <| Group (Shrink (F ⋙ forget GroupCat.{u}).sections)
set_option linter.uppercaseLean3 false in
#align Group.limit_group GroupCat.limitGroup
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_add_group AddGroupCat.limitAddGroup

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ GroupCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget GroupCat))

/-- We show that the forgetful functor `GroupCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive "We show that the forgetful functor `AddGroupCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit."]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ GroupCat.{u} MonCat.{u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : ReflectsIsomorphisms (forget₂ GroupCat.{u} MonCat.{u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GroupCat.{u} MonCat.{u}))
    fun c' t =>
    { liftedCone :=
        { pt := GroupCat.of (Types.Small.limitCone (F ⋙ forget GroupCat)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ GroupCat MonCat)
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ GroupCat MonCat.{u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ GroupCat MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }
set_option linter.uppercaseLean3 false in
#align Group.forget₂.creates_limit GroupCat.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂.creates_limit AddGroupCat.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `GroupCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `GroupCat`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ GroupCat.{u} MonCat.{u}))
set_option linter.uppercaseLean3 false in
#align Group.limit_cone GroupCat.limitCone
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone AddGroupCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Group.limit_cone_is_limit GroupCat.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone_is_limit AddGroupCat.limitConeIsLimit

/-- If `(F ⋙ forget GroupCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddGroupCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `GroupCat.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddGroupCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J GroupCat.{u} where
  has_limit _ := inferInstance

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} GroupCat.{u} where
  has_limits_of_shape J _ := { }
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
@[to_additive AddGroupCat.forget₂AddMonPreservesLimitsOfSize
  "The forgetful functor from additive groups to additive monoids preserves all limits.

  This means the underlying additive monoid of a limit can be computed as a limit in the category of
  additive monoids.",
  to_additive_relevant_arg 2]
noncomputable instance forget₂MonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ GroupCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J _} := { }
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits_of_size GroupCat.forget₂MonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_AddMon_preserves_limits AddGroupCat.forget₂AddMonPreservesLimitsOfSize

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
  PreservesLimits (forget₂ GroupCat.{u} MonCat.{u}) :=
  GroupCat.forget₂MonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits GroupCat.forget₂MonPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_Mon_preserves_limits AddGroupCat.forget₂MonPreservesLimits

/-- If `J` is `u`-small, the forgetful functor from `GroupCat.{u}` preserves limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddGroupCat.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget GroupCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  "The forgetful functor from additive groups to types preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of types.",
  to_additive_relevant_arg 2]
noncomputable instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget GroupCat.{u})
  where preservesLimitsOfShape {J _} := { }
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

namespace CommGroupCat

variable (F : J ⥤ CommGroupCat.{u})

@[to_additive]
instance commGroupObj (j) : CommGroup ((F ⋙ forget CommGroupCat).obj j) :=
  inferInstanceAs <| CommGroup (F.obj j)
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_obj CommGroupCat.commGroupObj
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_obj AddCommGroupCat.addCommGroupObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommGroupCat))]

@[to_additive]
noncomputable instance limitCommGroup :
    CommGroup (Types.Small.limitCone.{v, u} (F ⋙ forget CommGroupCat.{u})).pt :=
  letI : CommGroup (F ⋙ forget CommGroupCat.{u}).sections :=
    @Subgroup.toCommGroup (∀ j, F.obj j) _
      (GroupCat.sectionsSubgroup (F ⋙ forget₂ CommGroupCat.{u} GroupCat.{u}))
  inferInstanceAs <| CommGroup (Shrink (F ⋙ forget CommGroupCat.{u}).sections)
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_comm_group CommGroupCat.limitCommGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_add_comm_group AddCommGroupCat.limitAddCommGroup

/-- We show that the forgetful functor `CommGroupCat ⥤ GroupCat` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive "We show that the forgetful functor `AddCommGroupCat ⥤ AddGroupCat` creates limits.

  All we need to do is notice that the limit point has an `AddCommGroup` instance available,
  and then reuse the existing limit."]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ CommGroupCat GroupCat.{u}) :=
  letI : ReflectsIsomorphisms (forget₂ CommGroupCat.{u} GroupCat.{u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  letI : Small.{u}
      (Functor.sections ((F ⋙ forget₂ CommGroupCat GroupCat) ⋙ forget GroupCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGroupCat))
  letI : Small.{u}
      (Functor.sections ((F ⋙ forget₂ _ GroupCat ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGroupCat))
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommGroupCat.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGroupCat)).pt
          π :=
            { app := MonCat.limitπMonoidHom
                (F ⋙ forget₂ CommGroupCat GroupCat.{u} ⋙ forget₂ GroupCat MonCat.{u})
              naturality := (MonCat.HasLimits.limitCone _).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (GroupCat.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ GroupCat.{u} ⋙ forget₂ _ MonCat.{u})
          (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂.creates_limit CommGroupCat.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂.creates_limit AddCommGroupCat.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `CommGroupCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
  "A choice of limit cone for a functor into `AddCommGroupCat`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGroupCat GroupCat) ⋙ forget GroupCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGroupCat))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGroupCat.{u} GroupCat.{u}))
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_cone CommGroupCat.limitCone
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_cone AddCommGroupCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
  "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_cone_is_limit CommGroupCat.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_cone_is_limit AddCommGroupCat.limitConeIsLimit

/-- If `(F ⋙ forget CommGroupCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddCommGroupCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `CommGroupCat.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddCommGroupCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommGroupCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommGroupCat.{u}
  where has_limits_of_shape _ _ := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.has_limits_of_size CommGroupCat.hasLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_limits_of_size AddCommGroupCat.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits CommGroupCat.{u} :=
  CommGroupCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommGroup.has_limits CommGroupCat.hasLimits
set_option linter.uppercaseLean3 false in
#align AddCommGroup.has_limits AddCommGroupCat.hasLimits

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to groups preserves all limits.
  (That is, the underlying group could have been computed instead as limits in the category
    of additive groups.)",
  to_additive_relevant_arg 2]
noncomputable instance forget₂GroupPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGroupCat.{u} GroupCat.{u}) where
  preservesLimitsOfShape {J 𝒥} := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_Group_preserves_limits_of_size CommGroupCat.forget₂GroupPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddGroup_preserves_limits AddCommGroupCat.forget₂AddGroupPreservesLimitsOfSize

@[to_additive]
noncomputable instance forget₂GroupPreservesLimits :
    PreservesLimits (forget₂ CommGroupCat GroupCat.{u}) :=
  CommGroupCat.forget₂GroupPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_Group_preserves_limits CommGroupCat.forget₂GroupPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_Group_preserves_limits AddCommGroupCat.forget₂AddGroupPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimitsAux
  "An auxiliary declaration to speed up typechecking."]
noncomputable def forget₂CommMonPreservesLimitsAux :
    IsLimit ((forget₂ CommGroupCat.{u} CommMonCat.{u}).mapCone (limitCone.{v, u} F)) :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGroupCat))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGroupCat.{u} CommMonCat.{u})
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_aux CommGroupCat.forget₂CommMonPreservesLimitsAux
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits_aux AddCommGroupCat.forget₂AddCommMonPreservesLimitsAux

/-- If `J` is `u`-small, the forgetful functor from `CommGroupCat.{u}` to `CommMonCat.{u}`
preserves limits of shape `J`. -/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimitsOfShape
  "If `J` is `u`-small, the forgetful functor from `AddCommGroupCat.{u}`
  to `AddCommMonCat.{u}` preserves limits of shape `J`."]
noncomputable instance forget₂CommMonPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget₂ CommGroupCat.{u} CommMonCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
      (forget₂CommMonPreservesLimitsAux.{v, u} F)

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimitsOfSize
  "The forgetful functor from additive commutative groups to additive commutative monoids
  preserves all limits. (That is, the underlying additive commutative monoids could have been
  computed instead as limits in the category of additive commutative monoids.)"]
noncomputable instance forget₂CommMonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGroupCat CommMonCat.{u}) where
  preservesLimitsOfShape := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_of_size CommGroupCat.forget₂CommMonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits AddCommGroupCat.forget₂AddCommMonPreservesLimitsOfSize

/-- If `J` is `u`-small, the forgetful functor from `CommGroupCat.{u}` preserves limits of
shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddCommGroupCat.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommGroupCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to types preserves all limits.
  (That is, the underlying types could have been computed instead as limits in the category of
  types.)"]
noncomputable instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommGroupCat.{u}) where
  preservesLimitsOfShape {_ _} := { }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_preserves_limits_of_size CommGroupCat.forgetPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_preserves_limits AddCommGroupCat.forgetPreservesLimitsOfSize

noncomputable instance _root_.AddCommGroupCat.forgetPreservesLimits :
    PreservesLimits (forget AddCommGroupCat.{u}) :=
  AddCommGroupCat.forgetPreservesLimitsOfSize.{u, u}

@[to_additive existing]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget CommGroupCat.{u}) :=
  CommGroupCat.forgetPreservesLimitsOfSize.{u, u}

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGroupCat) : HasProduct f := by infer_instance

end CommGroupCat

namespace AddCommGroupCat

/-- The categorical kernel of a morphism in `AddCommGroupCat`
agrees with the usual group-theoretical kernel.
-/
def kernelIsoKer {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    kernel f ≅ AddCommGroupCat.of f.ker where
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
    generalize_proofs _ h1 h2
    erw [DFunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, h2⟩]
    rfl
  inv_hom_id := by
    apply AddCommGroupCat.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    simp only [ZeroHom.coe_mk, Function.comp_apply, id_eq]
    generalize_proofs _ h1 h2
    erw [DFunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, mem⟩]
    rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker AddCommGroupCat.kernelIsoKer

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by ext; rfl
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_hom_comp_subtype AddCommGroupCat.kernelIsoKer_hom_comp_subtype

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker := by
  ext
  simp [kernelIsoKer]
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_inv_comp_ι AddCommGroupCat.kernelIsoKer_inv_comp_ι

-- Porting note: explicitly add what to be synthesized under `simps!`, because other lemmas
-- automatically generated is not in normal form
/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps! hom_left_apply_coe inv_left_apply]
def kernelIsoKerOver {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGroupCat.of f.ker) (AddSubgroup.subtype f.ker) :=
  Over.isoMk (kernelIsoKer f)
set_option linter.uppercaseLean3 false in
#align AddCommGroup.kernel_iso_ker_over AddCommGroupCat.kernelIsoKerOver

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGroupCat.kernelIsoKerOver_inv_left_apply
  AddCommGroupCat.kernelIsoKerOver_hom_left_apply_coe

end AddCommGroupCat
