/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

assert_not_exists MonoidWithZero

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u w

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})

@[to_additive]
instance monoidObj (j) : Monoid ((F ⋙ forget MonCat).obj j) :=
  inferInstanceAs <| Monoid (F.obj j)

/-- The flat sections of a functor into `MonCat` form a submonoid of all sections. -/
@[to_additive
/-- The flat sections of a functor into `AddMonCat` form an additive submonoid of all sections. -/]
def sectionsSubmonoid : Submonoid (∀ j, F.obj j) where
  carrier := (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by
    simp only [Functor.comp_map, Pi.mul_apply]
    dsimp [Functor.sections] at ah bh
    rw [← ah f, ← bh f, forget_map, map_mul]

@[to_additive]
instance sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections :=
  (sectionsSubmonoid F).toMonoid

variable [Small.{u} (Functor.sections (F ⋙ forget MonCat))]

@[to_additive]
noncomputable instance limitMonoid :
    Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt :=
  inferInstanceAs <| Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

/-- `limit.π (F ⋙ forget MonCat) j` as a `MonoidHom`. -/
@[to_additive /-- `limit.π (F ⋙ forget AddMonCat) j` as an `AddMonoidHom`. -/]
noncomputable def limitπMonoidHom (j : J) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt →*
      ((F ⋙ forget MonCat.{u}).obj j) where
  toFun := (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by
    simp only [Types.Small.limitCone_pt, Types.Small.limitCone_π_app, equivShrink_symm_one]
    rfl
  map_mul' _ _ := by
    simp only [Types.Small.limitCone_pt, Types.Small.limitCone_π_app, equivShrink_symm_mul]
    rfl

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits MonCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `MonCat`.
(Internal use only; use the limits API.)
-/
@[to_additive /-- (Internal use only; use the limits API.) -/]
noncomputable def limitCone : Cone F :=
  { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app j := ofHom (limitπMonoidHom F j)
      naturality := fun _ _ f ↦ MonCat.ext fun x ↦
        CategoryTheory.congr_hom ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x } }

/-- Witness that the limit cone in `MonCat` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive /-- (Internal use only; use the limits API.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v,u} _)
    (fun s ↦ ofHom { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s ↦ rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [EquivLike.coe_apply, Functor.mapCone_π_app, forget_map, map_mul]
    rw [← equivShrink_mul]
    rfl

/-- If `(F ⋙ forget MonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddMonCat).sections` is `u`-small, `F` has a limit. -/]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `MonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddMonCat.{u}` has limits of shape `J`. -/]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where
  has_limit _ := inferInstance

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive /-- The category of additive monoids has all limits. -/,
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
instance hasLimits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `MonCat.{u}` preserves limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddMonCat.{u}` preserves limits
of shape `J`. -/]
noncomputable instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget MonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
  /-- The forgetful functor from additive monoids to types preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of types. -/,
  to_additive_relevant_arg 2]
noncomputable instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  preservesLimitsOfShape := { }

@[to_additive]
noncomputable instance forget_preservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget MonCat.{u}) := by
  apply createsLimitOfReflectsIso
  intro c t
  have : Small.{u} (Functor.sections (F ⋙ forget MonCat)) :=
    (Types.hasLimit_iff_small_sections _).mp (HasLimit.mk {cone := c, isLimit := t})
  refine LiftsToLimit.mk (LiftableCone.mk
    { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget MonCat)).pt,
      π := NatTrans.mk
        (fun j ↦ ofHom (limitπMonoidHom F j))
        (MonCat.HasLimits.limitCone F).π.naturality }
    (Cones.ext
      ((Types.isLimitEquivSections t).trans (equivShrink _)).symm.toIso
      (fun _ ↦ funext (fun _ ↦ by simp; rfl)))) ?_
  refine IsLimit.ofFaithful (forget MonCat.{u}) (Types.Small.limitConeIsLimit.{v,u} _) ?_ ?_
  · intro _
    refine ofHom
      { toFun := (Types.Small.limitConeIsLimit.{v,u} _).lift ((forget MonCat).mapCone _),
        map_one' := by simp; rfl, map_mul' := ?_ }
    · intro x y
      simp only [Types.Small.limitConeIsLimit_lift, Functor.comp_obj, Functor.mapCone_pt,
          Functor.mapCone_π_app, forget_map, map_mul]
      congr
      simp only [Functor.comp_obj, Equiv.symm_apply_apply]
      rfl
  · exact fun _ ↦ rfl

@[to_additive]
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
      CreatesLimit := inferInstance

/-- The forgetful functor from monoids to types preserves all limits. -/
@[to_additive /-- The forgetful functor from additive monoids to types preserves all limits. -/]
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w,v} (forget MonCat.{u}) where
      CreatesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance forget_createsLimits :
    CreatesLimits (forget MonCat.{u}) := MonCat.forget_createsLimitsOfSize.{u,u}

end MonCat

open MonCat

namespace CommMonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommMonCat.{u})

@[to_additive]
instance commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j) :=
  inferInstanceAs <| CommMonoid (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommMonCat))]

@[to_additive]
noncomputable instance limitCommMonoid :
    CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat.{u})).pt :=
  letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (∀ j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
  inferInstanceAs <| CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

/-- We show that the forgetful functor `CommMonCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `CommMonoid` instance available,
and then reuse the existing limit. -/
@[to_additive /-- We show that the forgetful functor `AddCommMonCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddCommMonoid` instance available,
and then reuse the existing limit. -/]
noncomputable instance forget₂CreatesLimit : CreatesLimit F (forget₂ CommMonCat MonCat.{u}) :=
  createsLimitOfReflectsIso fun c' t ↦
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app j := ofHom (MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}) j)
              naturality _ _ j := ext <| fun x ↦ congr_hom
                ((MonCat.HasLimits.limitCone
                  (F ⋙ forget₂ CommMonCat MonCat.{u})).π.naturality j) x } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMonCat MonCat.{u})
          (MonCat.HasLimits.limitConeIsLimit _) (fun _ ↦ _) fun _ ↦ rfl }

/-- A choice of limit cone for a functor into `CommMonCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive /-- A choice of limit cone for a functor into `AddCommMonCat`.
(Generally, you'll just want to use `limit F`.) -/]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      /-- The chosen cone is a limit cone. (Generally, you'll just want to use
`limit.cone F`.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommMonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddCommMonCat).sections` is `u`-small, `F` has a limit. -/]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `CommMonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddCommMonCat.{u}` has limits of shape `J`. -/]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative monoids has all limits. -/
@[to_additive /-- The category of additive commutative monoids has all limits. -/,
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
instance hasLimits : HasLimits CommMonCat.{u} :=
  CommMonCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMonCat.forget₂AddMonPreservesLimitsOfSize /-- The forgetful functor from
  additive commutative monoids to additive monoids preserves all limits.

  This means the underlying type of a limit can be computed as a limit in the category of additive
  monoids. -/,
  to_additive_relevant_arg 2]
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommMonCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J} 𝒥 := { }

@[to_additive]
instance forget₂Mon_preservesLimits :
    PreservesLimits (forget₂ CommMonCat.{u} MonCat.{u}) :=
  CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `CommMonCat.{u}` preserves limits of
shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddCommMonCat.{u}`
preserves limits of shape `J`. -/]
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommMonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive /-- The forgetful functor from additive commutative monoids to types preserves all
limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/]
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget CommMonCat.{u}) where
  preservesLimitsOfShape {_} _ := { }

instance _root_.AddCommMonCat.forget_preservesLimits :
    PreservesLimits (forget AddCommMonCat.{u}) :=
  AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
instance forget_preservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget CommMonCat.{u}) := by
  set e : forget CommMonCat.{u} ≅ forget₂ CommMonCat.{u} MonCat.{u} ⋙ forget MonCat.{u} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  exact createsLimitOfNatIso e.symm

@[to_additive]
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
      CreatesLimit := inferInstance

/-- The forgetful functor from commutative monoids to types preserves all limits. -/
@[to_additive
/-- The forgetful functor from commutative additive monoids to types preserves all limits. -/]
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w,v} (forget MonCat.{u}) where
      CreatesLimitsOfShape := inferInstance

@[to_additive]
noncomputable instance forget_createsLimits :
    CreatesLimits (forget MonCat.{u}) := CommMonCat.forget_createsLimitsOfSize.{u,u}

end CommMonCat
