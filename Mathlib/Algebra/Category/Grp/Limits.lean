/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.Grp.Preadditive
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

universe v u

noncomputable section

variable {J : Type v} [SmallCategory J]

namespace Grp

@[to_additive]
instance groupObj (F : J ⥤ GrpMax.{v, u}) (j) : Group ((F ⋙ forget Grp).obj j) := by
  change Group (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align Group.group_obj Grp.groupObj
set_option linter.uppercaseLean3 false in
#align AddGroup.add_group_obj AddGrp.addGroupObj

/-- The flat sections of a functor into `Grp` form a subgroup of all sections.
-/
@[to_additive
  "The flat sections of a functor into `AddGrp` form an additive subgroup of all sections."]
def sectionsSubgroup (F : J ⥤ Grp) : Subgroup (∀ j, F.obj j) :=
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
noncomputable instance limitGroup (F : J ⥤ GrpMax.{v, u}) :
    Group (Types.limitCone.{v, u} (F ⋙ forget Grp)).pt := by
  change Group (sectionsSubgroup.{v, u} F)
  infer_instance
set_option linter.uppercaseLean3 false in
#align Group.limit_group Grp.limitGroup
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_add_group AddGrp.limitAddGroup

/-- We show that the forgetful functor `Grp ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive "We show that the forgetful functor `AddGrp ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit."]
noncomputable instance Forget₂.createsLimit (F : J ⥤ GrpMax.{v, u}) :
    CreatesLimit F (forget₂ GrpMax.{v, u} MonCatMax.{v, u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : ReflectsIsomorphisms (forget₂ GrpMax.{v, u} MonCatMax.{v, u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ Grp.{max v u} MonCat.{max v u}))
    fun c' t =>
    { liftedCone :=
        { pt := Grp.of (Types.limitCone (F ⋙ forget GrpMax)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ GrpMax MonCatMax)
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ Grp MonCat.{max v u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ Grp MonCat.{max v u}) (MonCat.HasLimits.limitConeIsLimit _)
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
noncomputable def limitCone (F : J ⥤ GrpMax.{v, u}) : Cone F :=
  -- Porting note: add this instance to help Lean unify universe levels
  letI : HasLimit (F ⋙ forget₂ GrpMax.{v, u} MonCat.{max v u}) :=
    (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
  liftLimit
    (limit.isLimit (F ⋙ forget₂ GrpMax.{v, u} MonCat.{max v u}))
set_option linter.uppercaseLean3 false in
#align Group.limit_cone Grp.limitCone
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone AddGrp.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit (F : J ⥤ GrpMax.{v, u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Group.limit_cone_is_limit Grp.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddGroup.limit_cone_is_limit AddGrp.limitConeIsLimit

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} GrpMax.{v, u} where
  has_limits_of_shape J _ :=
    { has_limit :=
        -- Porting note: add this instance to help Lean unify universe levels
        fun F => letI : HasLimit (F ⋙ forget₂ GrpMax.{v, u} MonCat.{max v u}) :=
          (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
        hasLimit_of_created F (forget₂ GrpMax.{v, u} MonCat.{max v u}) }
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
@[to_additive AddGrp.forget₂AddMonPreservesLimits
  "The forgetful functor from additive groups to additive monoids preserves all limits.

  This means the underlying additive monoid of a limit can be computed as a limit in the category of
  additive monoids."]
noncomputable instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ GrpMax.{v, u} MonCat.{max v u}) where
  preservesLimitsOfShape {J _} := { preservesLimit := fun {F} =>
      -- Porting note: add this instance to help Lean unify universe levels
      letI : HasLimit (F ⋙ forget₂ GrpMax.{v, u} MonCat.{max v u}) :=
        (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
      inferInstance }
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits_of_size Grp.forget₂MonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_AddMon_preserves_limits AddGrp.forget₂AddMonPreservesLimits

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
  PreservesLimits (forget₂ Grp.{u} MonCat.{u}) :=
  Grp.forget₂MonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Group.forget₂_Mon_preserves_limits Grp.forget₂MonPreservesLimits
set_option linter.uppercaseLean3 false in
#align AddGroup.forget₂_Mon_preserves_limits AddGrp.forget₂MonPreservesLimits

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  "The forgetful functor from additive groups to types preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of types."]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget GrpMax.{v, u})
  where preservesLimitsOfShape {J _} :=
  { preservesLimit := fun {F} =>
      -- Porting note: add these instances to help Lean unify universe levels
      letI : HasLimit (F ⋙ forget₂ GrpMax.{v, u} MonCat.{max v u}) :=
        (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
      letI h1 := Grp.forget₂MonPreservesLimitsOfSize.{v, u}
      letI h2 := MonCat.forgetPreservesLimitsOfSize.{v, u}
      Limits.compPreservesLimit (K := F)
        (forget₂ GrpMax.{v, u} MonCat.{max v u})
        (forget MonCat.{max v u}) }
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

@[to_additive]
instance commGroupObj (F : J ⥤ CommGrpMax.{v, u}) (j) :
    CommGroup ((F ⋙ forget CommGrpMax).obj j) := by
  change CommGroup (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommGroup.comm_group_obj CommGrp.commGroupObj
set_option linter.uppercaseLean3 false in
#align AddCommGroup.add_comm_group_obj AddCommGrp.addCommGroupObj

@[to_additive]
noncomputable instance limitCommGroup (F : J ⥤ CommGrp.{max v u}) :
    CommGroup (Types.limitCone.{v, u} (F ⋙ forget CommGrpMax.{v, u})).pt :=
  @Subgroup.toCommGroup (∀ j, F.obj j) _
    (Grp.sectionsSubgroup.{v, max v u}
      (F ⋙ forget₂ CommGrpMax.{v, u} GrpMax.{v, u}))
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_comm_group CommGrp.limitCommGroup
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_add_comm_group AddCommGrp.limitAddCommGroup

/-- We show that the forgetful functor `CommGrp ⥤ Grp` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive "We show that the forgetful functor `AddCommGrp ⥤ AddGrp` creates limits.

  All we need to do is notice that the limit point has an `AddCommGroup` instance available,
  and then reuse the existing limit."]
noncomputable instance Forget₂.createsLimit (F : J ⥤ CommGrpMax.{v, u}) :
    CreatesLimit F (forget₂ CommGrp GrpMax.{v, u}) :=
  letI : ReflectsIsomorphisms (forget₂ CommGrpMax.{v, u} GrpMax.{v, u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommGrp.of (Types.limitCone.{v, u} (F ⋙ forget CommGrp)).pt
          π :=
            { app := MonCat.limitπMonoidHom
                (F ⋙ forget₂ CommGrp Grp.{max v u} ⋙ forget₂ Grp MonCat.{max v u})
              naturality := (MonCat.HasLimits.limitCone _).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (Grp.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ Grp.{max v u} ⋙ forget₂ _ MonCat.{max v u})
          (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂.creates_limit CommGrp.Forget₂.createsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂.creates_limit AddCommGrp.Forget₂.createsLimit

/-- A choice of limit cone for a functor into `CommGrp`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
  "A choice of limit cone for a functor into `AddCommGrp`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone (F : J ⥤ CommGrp.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrpMax.{v, u} GrpMax.{v, u}))
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
noncomputable def limitConeIsLimit (F : J ⥤ CommGrpMax.{v, u}) :
    IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommGroup.limit_cone_is_limit CommGrp.limitConeIsLimit
set_option linter.uppercaseLean3 false in
#align AddCommGroup.limit_cone_is_limit AddCommGrp.limitConeIsLimit

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommGrp.{max v u}
  where has_limits_of_shape _ _ :=
  { has_limit := fun F => hasLimit_of_created F
      (forget₂ CommGrpMax.{v, u} GrpMax.{v, u}) }
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

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to groups preserves all limits.
  (That is, the underlying group could have been computed instead as limits in the category
    of additive groups.)"]
noncomputable instance forget₂GroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGrpMax.{v, u} GrpMax.{v, u}) where
  preservesLimitsOfShape {J 𝒥} := { preservesLimit := fun {F} => by infer_instance }
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
noncomputable def forget₂CommMonPreservesLimitsAux (F : J ⥤ CommGrpMax.{v, u}) :
    IsLimit ((forget₂ CommGrpMax.{v, u} CommMonCat).mapCone (limitCone.{v, u} F)) :=
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrpMax.{v, u} CommMonCat)
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_aux CommGrp.forget₂CommMonPreservesLimitsAux
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits_aux AddCommGrp.forget₂AddCommMonPreservesLimitsAux

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimits
  "The forgetful functor from additive commutative groups to additive commutative monoids
  preserves all limits. (That is, the underlying additive commutative monoids could have been
  computed instead as limits in the category of additive commutative monoids.)"]
noncomputable instance forget₂CommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGrp CommMonCat.{max v u}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂CommMonPreservesLimitsAux.{v, u} F) }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget₂_CommMon_preserves_limits_of_size CommGrp.forget₂CommMonPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget₂_AddCommMon_preserves_limits AddCommGrp.forget₂AddCommMonPreservesLimits

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to types preserves all limits.
  (That is, the underlying types could have been computed instead as limits in the category of
  types.)"]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget CommGrpMax.{v, u}) where
  preservesLimitsOfShape {J _} :=
  { preservesLimit := fun {F} =>
    -- Porting note: add these instance to help Lean unify universe levels
    letI : HasLimit (F ⋙ forget₂ CommGrpMax.{v, u} Grp.{max v u}) :=
      (Grp.hasLimitsOfSize.{v, u}.1 J).1 _
    letI h1 := CommGrp.forget₂CommMonPreservesLimitsOfSize.{v, u}
    letI h2 := Grp.forgetPreservesLimitsOfSize.{v, u}
    Limits.compPreservesLimit (K := F) (forget₂ CommGrpMax.{v, u} Grp) (forget Grp) }
set_option linter.uppercaseLean3 false in
#align CommGroup.forget_preserves_limits_of_size CommGrp.forgetPreservesLimitsOfSize
set_option linter.uppercaseLean3 false in
#align AddCommGroup.forget_preserves_limits AddCommGrp.forgetPreservesLimitsOfSize

@[to_additive]
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
    generalize_proofs _ h1 h2
    erw [DFunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, h2⟩]
    rfl
  inv_hom_id := by
    apply AddCommGrp.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    simp only [ZeroHom.coe_mk, Function.comp_apply, id_eq]
    generalize_proofs _ h1 h2
    erw [DFunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, mem⟩]
    rfl
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
agrees with the `subtype` map.
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
