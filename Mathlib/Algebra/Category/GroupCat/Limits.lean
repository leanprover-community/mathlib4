/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.CategoryTheory.Over
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso

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

namespace GroupCat

@[to_additive]
instance groupObj (F : J ⥤ GroupCatMax.{v, u}) (j) : Group ((F ⋙ forget GroupCat).obj j) := by
  change Group (F.obj j)
  infer_instance

/-- The flat sections of a functor into `GroupCat` form a subgroup of all sections.
-/
@[to_additive
  "The flat sections of a functor into `AddGroupCat` form an additive subgroup of all sections."]
def sectionsSubgroup (F : J ⥤ GroupCat) : Subgroup (∀ j, F.obj j) :=
  { MonCat.sectionsSubmonoid (F ⋙ forget₂ GroupCat MonCat) with
    carrier := (F ⋙ forget GroupCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply, MonoidHom.map_inv, inv_inj]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).map_inv (a j), ah f] }

@[to_additive]
noncomputable instance limitGroup (F : J ⥤ GroupCatMax.{v, u}) :
    Group (Types.limitCone.{v, u} (F ⋙ forget GroupCat)).pt := by
  change Group (sectionsSubgroup.{v, u} F)
  infer_instance

/-- We show that the forgetful functor `GroupCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive "We show that the forgetful functor `AddGroupCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit."]
noncomputable instance Forget₂.createsLimit (F : J ⥤ GroupCatMax.{v, u}) :
    CreatesLimit F (forget₂ GroupCatMax.{v, u} MonCatMax.{v, u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
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

/-- A choice of limit cone for a functor into `GroupCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `GroupCat`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone (F : J ⥤ GroupCatMax.{v, u}) : Cone F :=
  -- Porting note: add this instance to help Lean unify universe levels
  letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
    (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
  liftLimit
    (limit.isLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit (F : J ⥤ GroupCatMax.{v, u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} GroupCatMax.{v, u} where
  has_limits_of_shape J _ :=
    { has_limit :=
        -- Porting note: add this instance to help Lean unify universe levels
        fun F => letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
          (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
        hasLimit_of_created F (forget₂ GroupCatMax.{v, u} MonCat.{max v u}) }

@[to_additive]
instance hasLimits : HasLimits GroupCat.{u} :=
  GroupCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGroupCat.forget₂AddMonPreservesLimits
  "The forgetful functor from additive groups to additive monoids preserves all limits.

  This means the underlying additive monoid of a limit can be computed as a limit in the category of
  additive monoids."]
noncomputable instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ GroupCatMax.{v, u} MonCat.{max v u}) where
  preservesLimitsOfShape {J _} := { preservesLimit := fun {F} =>
      -- Porting note: add this instance to help Lean unify universe levels
      letI : HasLimit (F ⋙ forget₂ GroupCatMax.{v, u} MonCat.{max v u}) :=
        (MonCat.hasLimitsOfSize.{v, u}.1 J).1 _
      inferInstance }

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
  PreservesLimits (forget₂ GroupCat.{u} MonCat.{u}) :=
  GroupCat.forget₂MonPreservesLimitsOfSize.{u, u}

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  "The forgetful functor from additive groups to types preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of types."]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget GroupCatMax.{v, u})
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

@[to_additive]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget GroupCat.{u}) :=
  GroupCat.forgetPreservesLimitsOfSize.{u, u}

end GroupCat

namespace CommGroupCat

@[to_additive]
instance commGroupObj (F : J ⥤ CommGroupCatMax.{v, u}) (j) :
    CommGroup ((F ⋙ forget CommGroupCatMax).obj j) := by
  change CommGroup (F.obj j)
  infer_instance

@[to_additive]
noncomputable instance limitCommGroup (F : J ⥤ CommGroupCat.{max v u}) :
    CommGroup (Types.limitCone.{v, u} (F ⋙ forget CommGroupCatMax.{v, u})).pt :=
  @Subgroup.toCommGroup (∀ j, F.obj j) _
    (GroupCat.sectionsSubgroup.{v, max v u}
      (F ⋙ forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}))

/-- We show that the forgetful functor `CommGroupCat ⥤ GroupCat` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive "We show that the forgetful functor `AddCommGroupCat ⥤ AddGroupCat` creates limits.

  All we need to do is notice that the limit point has an `AddCommGroup` instance available,
  and then reuse the existing limit."]
noncomputable instance Forget₂.createsLimit (F : J ⥤ CommGroupCatMax.{v, u}) :
    CreatesLimit F (forget₂ CommGroupCat GroupCatMax.{v, u}) :=
  letI : ReflectsIsomorphisms (forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommGroupCat.of (Types.limitCone.{v, u} (F ⋙ forget CommGroupCat)).pt
          π :=
            { app := MonCat.limitπMonoidHom
                (F ⋙ forget₂ CommGroupCat GroupCat.{max v u} ⋙ forget₂ GroupCat MonCat.{max v u})
              naturality := (MonCat.HasLimits.limitCone _).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (GroupCat.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ GroupCat.{max v u} ⋙ forget₂ _ MonCat.{max v u})
          (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommGroupCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
  "A choice of limit cone for a functor into `AddCommGroupCat`.
  (Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone (F : J ⥤ CommGroupCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
  "The chosen cone is a limit cone.
  (Generally, you'll just want to use `limit.cone F`.)"]
noncomputable def limitConeIsLimit (F : J ⥤ CommGroupCatMax.{v, u}) :
    IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommGroupCat.{max v u}
  where has_limits_of_shape _ _ :=
  { has_limit := fun F => hasLimit_of_created F
      (forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}) }

@[to_additive]
instance hasLimits : HasLimits CommGroupCat.{u} :=
  CommGroupCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to groups preserves all limits.
  (That is, the underlying group could have been computed instead as limits in the category
    of additive groups.)"]
noncomputable instance forget₂GroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGroupCatMax.{v, u} GroupCatMax.{v, u}) where
  preservesLimitsOfShape {J 𝒥} := { preservesLimit := fun {F} => by infer_instance }

@[to_additive]
noncomputable instance forget₂GroupPreservesLimits :
    PreservesLimits (forget₂ CommGroupCat GroupCat.{u}) :=
  CommGroupCat.forget₂GroupPreservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimitsAux
  "An auxiliary declaration to speed up typechecking."]
noncomputable def forget₂CommMonPreservesLimitsAux (F : J ⥤ CommGroupCatMax.{v, u}) :
    IsLimit ((forget₂ CommGroupCatMax.{v, u} CommMonCat).mapCone (limitCone.{v, u} F)) :=
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGroupCatMax.{v, u} CommMonCat)

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGroupCat.forget₂AddCommMonPreservesLimits
  "The forgetful functor from additive commutative groups to additive commutative monoids
  preserves all limits. (That is, the underlying additive commutative monoids could have been
  computed instead as limits in the category of additive commutative monoids.)"]
noncomputable instance forget₂CommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGroupCat CommMonCat.{max v u}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂CommMonPreservesLimitsAux.{v, u} F) }

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
  "The forgetful functor from additive commutative groups to types preserves all limits.
  (That is, the underlying types could have been computed instead as limits in the category of
  types.)"]
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget CommGroupCatMax.{v, u}) where
  preservesLimitsOfShape {J _} :=
  { preservesLimit := fun {F} =>
    -- Porting note : add these instance to help Lean unify universe levels
    letI : HasLimit (F ⋙ forget₂ CommGroupCatMax.{v, u} GroupCat.{max v u}) :=
      (GroupCat.hasLimitsOfSize.{v, u}.1 J).1 _
    letI h1 := CommGroupCat.forget₂CommMonPreservesLimitsOfSize.{v, u}
    letI h2 := GroupCat.forgetPreservesLimitsOfSize.{v, u}
    Limits.compPreservesLimit (K := F) (forget₂ CommGroupCatMax.{v, u} GroupCat) (forget GroupCat) }

@[to_additive]
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
    { toFun := fun g => ⟨kernel.ι f g, FunLike.congr_fun (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp [(AddSubgroup.coe_zero _).symm]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        change _ = _ + _
        dsimp
        simp }
  inv := kernel.lift f (AddSubgroup.subtype f.ker) <| by
    -- porting note : used to be `tidy`, but `aesop` can't do it
    refine FunLike.ext _ _ ?_
    rintro ⟨x, (hx : f _ = 0)⟩
    exact hx
  hom_inv_id := by
    -- Porting note: it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext x
    dsimp
    generalize_proofs _ h1 h2
    erw [FunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, h2⟩]
    rfl
  inv_hom_id := by
    apply AddCommGroupCat.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    simp only [ZeroHom.coe_mk, Function.comp_apply, id_eq]
    generalize_proofs _ h1 h2
    erw [FunLike.congr_fun (kernel.lift_ι f _ h1) ⟨_, mem⟩]
    rfl

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by ext; rfl

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker := by
  ext
  simp [kernelIsoKer]

-- Porting note : explicitly add what to be synthesized under `simps!`, because other lemmas
-- automatically generated is not in normal form
/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps! hom_left_apply_coe inv_left_apply]
def kernelIsoKerOver {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGroupCat.of f.ker) (AddSubgroup.subtype f.ker) :=
  Over.isoMk (kernelIsoKer f)

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AddCommGroupCat.kernelIsoKerOver_inv_left_apply
  AddCommGroupCat.kernelIsoKerOver_hom_left_apply_coe

end AddCommGroupCat
