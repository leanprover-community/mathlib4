/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Logic.Equiv.TransferInstance

#align_import algebra.category.Mon.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

set_option linter.uppercaseLean3 false

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u w

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `MonCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddMonCatMax
  "An alias for `AddMonCat.{max u v}`, to deal around unification issues."]
abbrev MonCatMax.{u1, u2} := MonCat.{max u1 u2}

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})

@[to_additive]
instance monoidObj (j) : Monoid ((F ⋙ forget MonCat).obj j) :=
  inferInstanceAs <| Monoid (F.obj j)
#align Mon.monoid_obj MonCat.monoidObj
#align AddMon.add_monoid_obj AddMonCat.addMonoidObj

/-- The flat sections of a functor into `MonCat` form a submonoid of all sections.
-/
@[to_additive
      "The flat sections of a functor into `AddMonCat` form an additive submonoid of all sections."]
def sectionsSubmonoid : Submonoid (∀ j, F.obj j) where
  carrier := (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by
    simp only [Functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
    dsimp [Functor.sections] at ah bh
    rw [← ah f, ← bh f, forget_map, map_mul]
#align Mon.sections_submonoid MonCat.sectionsSubmonoid
#align AddMon.sections_add_submonoid AddMonCat.sectionsAddSubmonoid

@[to_additive]
instance sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections :=
  (sectionsSubmonoid F).toMonoid

variable [Small.{u} (Functor.sections (F ⋙ forget MonCat))]

@[to_additive]
noncomputable instance limitMonoid :
    Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt :=
  inferInstanceAs <| Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)
#align Mon.limit_monoid MonCat.limitMonoid
#align AddMon.limit_add_monoid AddMonCat.limitAddMonoid

/-- `limit.π (F ⋙ forget MonCat) j` as a `MonoidHom`. -/
@[to_additive "`limit.π (F ⋙ forget AddMonCat) j` as an `AddMonoidHom`."]
noncomputable def limitπMonoidHom (j : J) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt →*
      ((F ⋙ forget MonCat.{u}).obj j) where
  toFun := (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by
    simp only [Types.Small.limitCone_π_app, ← Equiv.mulEquiv_apply, map_one]
    rfl
  map_mul' _ _ := by
    simp only [Types.Small.limitCone_π_app, ← Equiv.mulEquiv_apply, map_mul]
    rfl
#align Mon.limit_π_monoid_hom MonCat.limitπMonoidHom
#align AddMon.limit_π_add_monoid_hom AddMonCat.limitπAddMonoidHom

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits MonCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `MonCat`.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
noncomputable def limitCone : Cone F :=
  { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app := limitπMonoidHom F
      naturality := fun _ _ f =>
        set_option linter.deprecated false in
        MonoidHom.coe_inj ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
#align Mon.has_limits.limit_cone MonCat.HasLimits.limitCone
#align AddMon.has_limits.limit_cone AddMonCat.HasLimits.limitCone

/-- Witness that the limit cone in `MonCat` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive "(Internal use only; use the limits API.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v,u} _)
    (fun s => { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s => rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [Functor.mapCone_π_app, forget_map, map_mul]
    erw [← map_mul (MulEquiv.symm Shrink.mulEquiv)]
    rfl
#align Mon.has_limits.limit_cone_is_limit MonCat.HasLimits.limitConeIsLimit
#align AddMon.has_limits.limit_cone_is_limit AddMonCat.HasLimits.limitConeIsLimit

/-- If `(F ⋙ forget MonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddMonCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `MonCat.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddMonCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where
  has_limit _ := inferInstance

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive "The category of additive monoids has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where
  has_limits_of_shape _ _ := { }
#align Mon.has_limits_of_size MonCat.hasLimitsOfSize
#align AddMon.has_limits_of_size AddMonCat.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}
#align Mon.has_limits MonCat.hasLimits
#align AddMon.has_limits AddMonCat.hasLimits

/-- If `J` is `u`-small, the forgetful functor from `MonCat.{u}` preserves limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddMonCat.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget MonCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  "The forgetful functor from additive monoids to types preserves all limits.\n\n
  This means the underlying type of a limit can be computed as a limit in the category of types.",
  to_additive_relevant_arg 2]
noncomputable instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  preservesLimitsOfShape := { }
#align Mon.forget_preserves_limits_of_size MonCat.forgetPreservesLimitsOfSize
#align AddMon.forget_preserves_limits_of_size AddMonCat.forgetPreservesLimitsOfSize

@[to_additive]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forgetPreservesLimitsOfSize.{u, u}
#align Mon.forget_preserves_limits MonCat.forgetPreservesLimits
#align AddMon.forget_preserves_limits AddMonCat.forgetPreservesLimits

end MonCat

open MonCat

/-- An alias for `CommMonCat.{max u v}`, to deal around unification issues. -/
@[to_additive (attr := nolint checkUnivs) AddCommMonCatMax
  "An alias for `AddCommMonCat.{max u v}`, to deal around unification issues."]
abbrev CommMonCatMax.{u1, u2} := CommMonCat.{max u1 u2}

namespace CommMonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommMonCat.{u})

@[to_additive]
instance commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j) :=
  inferInstanceAs <| CommMonoid (F.obj j)
#align CommMon.comm_monoid_obj CommMonCat.commMonoidObj
#align AddCommMon.add_comm_monoid_obj AddCommMonCat.addCommMonoidObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommMonCat))]

@[to_additive]
noncomputable instance limitCommMonoid :
    CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat.{u})).pt :=
  letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (∀ j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
  inferInstanceAs <| CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)
#align CommMon.limit_comm_monoid CommMonCat.limitCommMonoid
#align AddCommMon.limit_add_comm_monoid AddCommMonCat.limitAddCommMonoid

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

/-- We show that the forgetful functor `CommMonCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `CommMonoid` instance available,
and then reuse the existing limit. -/
@[to_additive "We show that the forgetful functor `AddCommMonCat ⥤ AddMonCat` creates limits.\n\n
All we need to do is notice that the limit point has an `AddCommMonoid` instance available,\n
and then reuse the existing limit."]
noncomputable instance forget₂CreatesLimit : CreatesLimit F (forget₂ CommMonCat MonCat.{u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u})
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ CommMonCat MonCat.{u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMonCat MonCat.{u})
          (MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommMonCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `AddCommMonCat`.
(Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
#align CommMon.limit_cone CommMonCat.limitCone
#align AddCommMon.limit_cone AddCommMonCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommMon.limit_cone_is_limit CommMonCat.limitConeIsLimit
#align AddCommMon.limit_cone_is_limit AddCommMonCat.limitConeIsLimit

/-- If `(F ⋙ forget CommMonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive "If `(F ⋙ forget AddCommMonCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `CommMonCat.{u}` has limits of shape `J`. -/
@[to_additive "If `J` is `u`-small, `AddCommMonCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative monoids has all limits. -/
@[to_additive "The category of additive commutative monoids has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} where
  has_limits_of_shape _ _ := { }
#align CommMon.has_limits_of_size CommMonCat.hasLimitsOfSize
#align AddCommMon.has_limits_of_size AddCommMonCat.hasLimitsOfSize

@[to_additive]
instance hasLimits : HasLimits CommMonCat.{u} :=
  CommMonCat.hasLimitsOfSize.{u, u}
#align CommMon.has_limits CommMonCat.hasLimits
#align AddCommMon.has_limits AddCommMonCat.hasLimits

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMonCat.forget₂AddMonPreservesLimitsOfSize "The forgetful functor from
  additive commutative monoids to additive monoids preserves all limits.\n\n
  This means the underlying type of a limit can be computed as a limit in the category of additive\n
  monoids.",
  to_additive_relevant_arg 2]
noncomputable instance forget₂MonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommMonCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J} 𝒥 := { }
#align CommMon.forget₂_Mon_preserves_limits_of_size CommMonCat.forget₂MonPreservesLimitsOfSize
#align AddCommMon.forget₂_AddMon_preserves_limits AddCommMonCat.forget₂AddMonPreservesLimitsOfSize

@[to_additive]
noncomputable instance forget₂MonPreservesLimits :
    PreservesLimits (forget₂ CommMonCat.{u} MonCat.{u}) :=
  CommMonCat.forget₂MonPreservesLimitsOfSize.{u, u}
#align CommMon.forget₂_Mon_preserves_limits CommMonCat.forget₂MonPreservesLimits
#align AddCommMon.forget₂_Mon_preserves_limits AddCommMonCat.forget₂MonPreservesLimits

/-- If `J` is `u`-small, the forgetful functor from `CommMonCat.{u}` preserves limits of
shape `J`. -/
@[to_additive "If `J` is `u`-small, the forgetful functor from `AddCommMonCat.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forgetPreservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommMonCat.{u}) where
  preservesLimit {F} := preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive "The forgetful functor from additive commutative monoids to types preserves all\n
limits.\n\n
This means the underlying type of a limit can be computed as a limit in the category of types."]
noncomputable instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget CommMonCat.{u}) where
  preservesLimitsOfShape {_} _ := { }
#align CommMon.forget_preserves_limits_of_size CommMonCat.forgetPreservesLimitsOfSize
#align AddCommMon.forget_preserves_limits_of_size AddCommMonCat.forgetPreservesLimitsOfSize

noncomputable instance _root_.AddCommMonCat.forgetPreservesLimits :
    PreservesLimits (forget AddCommMonCat.{u}) :=
  AddCommMonCat.forgetPreservesLimitsOfSize.{u, u}
#align AddCommMon.forget_preserves_limits AddCommMonCat.forgetPreservesLimits

@[to_additive existing]
noncomputable instance forgetPreservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forgetPreservesLimitsOfSize.{u, u}
#align CommMon.forget_preserves_limits CommMonCat.forgetPreservesLimits

end CommMonCat
