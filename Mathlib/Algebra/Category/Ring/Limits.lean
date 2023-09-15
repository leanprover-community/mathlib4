/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.RingTheory.Subring.Basic

#align_import algebra.category.Ring.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


-- We use the following trick a lot of times in this file.
library_note "change elaboration strategy with `by apply`"/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

namespace SemiRingCat

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ SemiRingCatMax.{v, u}) (j) :
    Semiring ((F ⋙ forget SemiRingCat).obj j) := by
  change Semiring (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align SemiRing.semiring_obj SemiRingCat.semiringObj

/-- The flat sections of a functor into `SemiRingCat` form a subsemiring of all sections.
-/
def sectionsSubsemiring (F : J ⥤ SemiRingCatMax.{v, u}) : Subsemiring.{max v u} (∀ j, F.obj j) :=
  -- Porting note : if `f` and `g` were inlined, it does not compile
  letI f : J ⥤ AddMonCat.{max v u} := F ⋙ forget₂ SemiRingCatMax.{v, u} AddCommMonCat.{max v u} ⋙
    forget₂ AddCommMonCat AddMonCat
  letI g : J ⥤ MonCat.{max v u} := F ⋙ forget₂ SemiRingCatMax.{v, u} MonCat.{max v u}
  { (MonCat.sectionsSubmonoid.{v, u} (J := J) g),
    (AddMonCat.sectionsAddSubmonoid.{v, u} (J := J) f) with
    carrier := (F ⋙ forget SemiRingCat).sections }
set_option linter.uppercaseLean3 false in
#align SemiRing.sections_subsemiring SemiRingCat.sectionsSubsemiring

instance limitSemiring (F : J ⥤ SemiRingCatMax.{v, u}) :
    Semiring (Types.limitCone.{v, u} (F ⋙ forget SemiRingCat.{max v u})).pt :=
  (sectionsSubsemiring F).toSemiring
set_option linter.uppercaseLean3 false in
#align SemiRing.limit_semiring SemiRingCat.limitSemiring

/-- `limit.π (F ⋙ forget SemiRingCat) j` as a `RingHom`. -/
def limitπRingHom (F : J ⥤ SemiRingCatMax.{v, u}) (j) :
    (Types.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  -- Porting note : if `f` and `g` were inlined, it does not compile
  letI f : J ⥤ AddMonCat.{max v u} := F ⋙ forget₂ SemiRingCatMax.{v, u} AddCommMonCat.{max v u} ⋙
    forget₂ AddCommMonCat AddMonCat
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{max v u}) j with
    toFun := (Types.limitCone (F ⋙ forget SemiRingCat)).π.app j }
set_option linter.uppercaseLean3 false in
#align SemiRing.limit_π_ring_hom SemiRingCat.limitπRingHom

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits SemiRingCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `SemiRingCat`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ SemiRingCatMax.{v, u}) : Cone F where
  pt := SemiRingCat.of (Types.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπRingHom.{v, u} F
      naturality := fun {_ _} f => RingHom.coe_inj
        ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits.limit_cone SemiRingCat.HasLimits.limitCone

/-- Witness that the limit cone in `SemiRingCat` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ SemiRingCatMax.{v, u}) : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCatMax.{v, u}) (Types.limitConeIsLimit.{v, u} _)
    (fun s : Cone F => ofHom
      { toFun := _
        map_one' := Subtype.ext <| funext fun j => by exact (s.π.app j).map_one
        map_mul' := fun x y => Subtype.ext <| funext fun j => by exact (s.π.app j).map_mul x y
        map_zero' := Subtype.ext <| funext fun j => by exact (s.π.app j).map_zero
        map_add' := fun x y => Subtype.ext <| funext fun j => by exact (s.π.app j).map_add x y })
    fun s => rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits.limit_cone_is_limit SemiRingCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
instance hasLimitsOfSize : HasLimitsOfSize.{v} SemiRingCatMax.{v, u} :=
  { has_limits_of_shape := fun _ _ =>
      { has_limit := fun F => ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩ } }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits_of_size SemiRingCat.hasLimitsOfSize

instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits SemiRingCat.hasLimits

/--
Auxiliary lemma to prove the cone induced by `limitCone` is a limit cone.
-/
def forget₂AddCommMonPreservesLimitsAux (F : J ⥤ SemiRingCatMax.{v, u}) :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  apply AddCommMonCat.limitConeIsLimit.{v, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_AddCommMon_preserves_limits_aux SemiRingCat.forget₂AddCommMonPreservesLimitsAux

/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRingCat AddCommMonCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_AddCommMon_preserves_limits_of_size SemiRingCat.forget₂AddCommMonPreservesLimitsOfSize

instance forget₂AddCommMonPreservesLimits :
    PreservesLimits (forget₂ SemiRingCat AddCommMonCat.{u}) :=
  SemiRingCat.forget₂AddCommMonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_AddCommMon_preserves_limits SemiRingCat.forget₂AddCommMonPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂MonPreservesLimitsAux (F : J ⥤ SemiRingCatMax.{v, u}) :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{max v u})
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_Mon_preserves_limits_aux SemiRingCat.forget₂MonPreservesLimitsAux

/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRingCat MonCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_Mon_preserves_limits_of_size SemiRingCat.forget₂MonPreservesLimitsOfSize

instance forget₂MonPreservesLimits : PreservesLimits (forget₂ SemiRingCat MonCat.{u}) :=
  SemiRingCat.forget₂MonPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_Mon_preserves_limits SemiRingCat.forget₂MonPreservesLimits

/-- The forgetful functor from semirings to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget SemiRingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (Types.limitConeIsLimit.{v, u} (F ⋙ forget _)) }
set_option linter.uppercaseLean3 false in
#align SemiRing.forget_preserves_limits_of_size SemiRingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget SemiRingCat.{u}) :=
  SemiRingCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.forget_preserves_limits SemiRingCat.forgetPreservesLimits

end SemiRingCat

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommSemiring.{max u v}`, to deal with unification issues. -/
@[nolint checkUnivs]
abbrev CommSemiRingCatMax.{u1, u2} := CommSemiRingCat.{max u1 u2}

namespace CommSemiRingCat

variable {J : Type v} [SmallCategory J]

instance commSemiringObj (F : J ⥤ CommSemiRingCatMax.{v, u}) (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) := by
  change CommSemiring (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommSemiRing.comm_semiring_obj CommSemiRingCat.commSemiringObj

instance limitCommSemiring (F : J ⥤ CommSemiRingCatMax.{v, u}) :
    CommSemiring (Types.limitCone.{v, u} (F ⋙ forget CommSemiRingCat.{max v u})).pt :=
  @Subsemiring.toCommSemiring (∀ j, F.obj j) _
    (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u}))
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_comm_semiring CommSemiRingCat.limitCommSemiring

/-- We show that the forgetful functor `CommSemiRingCat ⥤ SemiRingCat` creates limits.

All we need to do is notice that the limit point has a `CommSemiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRingCatMax.{v, u}) :
    CreatesLimit F (forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u}) :=
  -- Porting note : `CommSemiRingCat ⥤ Type` reflecting isomorphism is needed to make Lean see that
  -- `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism. `CommSemiRingCat ⥤ Type` reflecting
  -- isomorphism is added manually since Lean can't see it, but even with this addition Lean can not
  -- see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this instance is also added.
  letI : ReflectsIsomorphisms (forget CommSemiRingCatMax.{v, u}) :=
    CommSemiRingCat.forgetReflectIsos.{max v u}
  letI : ReflectsIsomorphisms
    (forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u}) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u}
  let c : Cone F :=
    { pt := CommSemiRingCat.of (Types.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun j => CommSemiRingCat.ofHom <| SemiRingCat.limitπRingHom.{v, u} (J := J)
            (F ⋙ forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u}) j
          naturality := (SemiRingCat.HasLimits.limitCone.{v, u}
            (F ⋙ forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u})).π.naturality } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit := by
        refine IsLimit.ofFaithful (forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u})
          (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _)
          (fun s : Cone F => CommSemiRingCat.ofHom
            { toFun := _
              map_one' := Subtype.ext <| funext fun j => by exact (s.π.app j).map_one
              map_mul' := fun x y => Subtype.ext <| funext fun j => by exact (s.π.app j).map_mul x y
              map_zero' := Subtype.ext <| funext fun j => by exact (s.π.app j).map_zero
              map_add' := fun x y => Subtype.ext <| funext fun j => by exact (s.π.app j).map_add x y
              })
          fun s => rfl }

/-- A choice of limit cone for a functor into `CommSemiRingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommSemiRingCatMax.{v, u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCatMax.{v, u} SemiRingCatMax.{v, u}))
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_cone CommSemiRingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommSemiRingCatMax.{v, u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_cone_is_limit CommSemiRingCat.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommSemiRingCatMax.{v, u} :=
  { has_limits_of_shape := fun _ _ =>
      { has_limit := fun F =>
          hasLimit_of_created F (forget₂ CommSemiRingCat SemiRingCatMax.{v, u}) } }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_limits_of_size CommSemiRingCat.hasLimitsOfSize

instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_limits CommSemiRingCat.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommSemiRingCat SemiRingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit _) }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.forget₂_SemiRing_preserves_limits_of_size CommSemiRingCat.forget₂SemiRingPreservesLimitsOfSize

instance forget₂SemiRingPreservesLimits :
    PreservesLimits (forget₂ CommSemiRingCat SemiRingCat.{u}) :=
  CommSemiRingCat.forget₂SemiRingPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommSemiRing.forget₂_SemiRing_preserves_limits CommSemiRingCat.forget₂SemiRingPreservesLimits

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget CommSemiRingCatMax.{v, u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (Types.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.forget_preserves_limits_of_size CommSemiRingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget CommSemiRingCat.{u}) :=
  CommSemiRingCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommSemiRing.forget_preserves_limits CommSemiRingCat.forgetPreservesLimits

end CommSemiRingCat

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `RingCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev RingCatMax.{u1, u2} := RingCat.{max u1 u2}

namespace RingCat

variable {J : Type v} [SmallCategory J]

instance ringObj (F : J ⥤ RingCatMax.{v, u}) (j) : Ring ((F ⋙ forget RingCat).obj j) := by
  change Ring (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align Ring.ring_obj RingCat.ringObj

/-- The flat sections of a functor into `RingCat` form a subring of all sections.
-/
def sectionsSubring (F : J ⥤ RingCatMax.{v, u}) : Subring.{max v u} (∀ j, F.obj j) :=
  letI f : J ⥤ AddGroupCat.{max v u} :=
    F ⋙ forget₂ RingCatMax.{v, u} AddCommGroupCat.{max v u} ⋙
    forget₂ AddCommGroupCat.{max v u} AddGroupCat.{max v u}
  letI g : J ⥤ SemiRingCatMax.{v, u} := F ⋙ forget₂ RingCatMax.{v, u} SemiRingCat.{max v u}
  { AddGroupCat.sectionsAddSubgroup.{v, u} (J := J) f,
    SemiRingCat.sectionsSubsemiring.{v, u} (J := J) g with
    carrier := (F ⋙ forget RingCatMax.{v, u}).sections }
set_option linter.uppercaseLean3 false in
#align Ring.sections_subring RingCat.sectionsSubring

instance limitRing (F : J ⥤ RingCatMax.{v, u}) :
    Ring.{max v u} (Types.limitCone.{v, u} (F ⋙ forget RingCatMax.{v, u})).pt :=
  (sectionsSubring F).toRing
set_option linter.uppercaseLean3 false in
#align Ring.limit_ring RingCat.limitRing

/-- We show that the forgetful functor `CommRingCat ⥤ RingCat` creates limits.

All we need to do is notice that the limit point has a `Ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ RingCatMax.{v, u}) :
    CreatesLimit F (forget₂ RingCatMax.{v, u} SemiRingCatMax.{v, u}) :=
  letI : ReflectsIsomorphisms (forget₂ RingCatMax SemiRingCatMax) :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  letI c : Cone F :=
  { pt := RingCat.of (Types.limitCone (F ⋙ forget _)).pt
    π :=
      { app := fun x => SemiRingCat.ofHom _
        naturality := (SemiRingCat.HasLimits.limitCone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).π.naturality } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := by apply IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{max v u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `RingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ RingCatMax.{v, u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCatMax.{v, u} SemiRingCatMax.{v, u}))
set_option linter.uppercaseLean3 false in
#align Ring.limit_cone RingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ RingCatMax.{v, u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Ring.limit_cone_is_limit RingCat.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- The category of rings has all limits. -/
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} RingCat.{max v u} :=
  { has_limits_of_shape := fun {_ _} =>
      { has_limit := fun {F} => hasLimit_of_created F
          (forget₂ RingCatMax.{v, u} SemiRingCatMax.{v, u}) } }
set_option linter.uppercaseLean3 false in
#align Ring.has_limits_of_size RingCat.hasLimitsOfSize

instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.has_limits RingCat.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat SemiRingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
      { preservesLimit := fun {F} =>
          preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_SemiRing_preserves_limits_of_size RingCat.forget₂SemiRingPreservesLimitsOfSize

instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ RingCat SemiRingCat.{u}) :=
  RingCat.forget₂SemiRingPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_SemiRing_preserves_limits RingCat.forget₂SemiRingPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ RingCatMax.{v, u}) :
    IsLimit ((forget₂ RingCatMax.{v, u} AddCommGroupCat).mapCone (limitCone.{v, u} F)) := by
  -- Porting note : inline `f` would not compile
  letI f := (F ⋙ forget₂ RingCatMax.{v, u} AddCommGroupCat.{max v u})
  apply AddCommGroupCat.limitConeIsLimit.{v, u} f
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits_aux RingCat.forget₂AddCommGroupPreservesLimitsAux

/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCatMax.{v, u} AddCommGroupCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits_of_size RingCat.forget₂AddCommGroupPreservesLimitsOfSize

instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGroupCat.{u}) :=
  RingCat.forget₂AddCommGroupPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits RingCat.forget₂AddCommGroupPreservesLimits

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget RingCatMax.{v, u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (Types.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align Ring.forget_preserves_limits_of_size RingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.forget_preserves_limits RingCat.forgetPreservesLimits

end RingCat

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommRingCat.{max u v}`, to deal around unification issues. -/
@[nolint checkUnivs]
abbrev CommRingCatMax.{u1, u2} := CommRingCat.{max u1 u2}

namespace CommRingCat

variable {J : Type v} [SmallCategory J]

instance commRingObj (F : J ⥤ CommRingCatMax.{v, u}) (j) :
    CommRing ((F ⋙ forget CommRingCat).obj j) := by
  change CommRing (F.obj j)
  infer_instance
set_option linter.uppercaseLean3 false in
#align CommRing.comm_ring_obj CommRingCat.commRingObj

instance limitCommRing (F : J ⥤ CommRingCatMax.{v, u}) :
    CommRing.{max v u} (Types.limitCone.{v, u} (F ⋙ forget CommRingCatMax.{v, u})).pt :=
  @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
set_option linter.uppercaseLean3 false in
#align CommRing.limit_comm_ring CommRingCat.limitCommRing

/-- We show that the forgetful functor `CommRingCat ⥤ RingCat` creates limits.

All we need to do is notice that the limit point has a `CommRing` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRingCatMax.{v, u}) :
   CreatesLimit F (forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u}) :=
  /-
    A terse solution here would be
    ```
    createsLimitOfFullyFaithfulOfIso (CommRingCat.of (limit (F ⋙ forget _))) (Iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    -- Porting note : need to add these instances manually
    letI : ReflectsIsomorphisms (forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u}) :=
      CategoryTheory.reflectsIsomorphisms_forget₂ _ _
    letI c : Cone F :=
    { pt := CommRingCat.of (Types.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun x => ofHom <|
              SemiRingCat.limitπRingHom.{v, u}
                (F ⋙ forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u} ⋙
                  forget₂ RingCatMax.{v, u} SemiRingCatMax.{v, u}) x
          naturality :=
            (SemiRingCat.HasLimits.limitCone.{v, u}
                  (F ⋙
                    forget₂ _ RingCat.{max v u} ⋙
                      forget₂ _ SemiRingCat.{max v u})).π.naturality } }
    createsLimitOfReflectsIso
    fun _ t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (RingCat.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCatMax.{v, u})
          (RingCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u}))
          (fun s : Cone F => ofHom <|
              (RingCat.limitConeIsLimit.{v, u}
                (F ⋙ forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u})).lift
                ((forget₂ _ RingCatMax.{v, u}).mapCone s)) fun _ => rfl }

/-- A choice of limit cone for a functor into `CommRingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommRingCatMax.{v, u}) : Cone F :=
  -- Porting note : add this manually to get `liftLimit`
  letI : HasLimitsOfSize RingCatMax.{v, u} := RingCat.hasLimitsOfSize.{v, u}
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u}))
set_option linter.uppercaseLean3 false in
#align CommRing.limit_cone CommRingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommRingCatMax.{v, u}) : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommRing.limit_cone_is_limit CommRingCat.limitConeIsLimit

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
/-- The category of commutative rings has all limits. -/
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommRingCatMax.{v, u} :=
  -- Porting note : add this manually to get `liftLimit`
  letI : HasLimitsOfSize RingCatMax.{v, u} := RingCat.hasLimitsOfSize.{v, u}
  { has_limits_of_shape := fun {_ _} =>
      { has_limit := fun F => hasLimit_of_created F
          (forget₂ CommRingCatMax.{v, u} RingCatMax.{v, u}) } }
set_option linter.uppercaseLean3 false in
#align CommRing.has_limits_of_size CommRingCat.hasLimitsOfSize

instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.has_limits CommRingCat.hasLimits

/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat RingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone.{v, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_Ring_preserves_limits_of_size CommRingCat.forget₂RingPreservesLimitsOfSize

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂RingPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_Ring_preserves_limits CommRingCat.forget₂RingPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux (F : J ⥤ CommRingCatMax.{v, u}) :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u})
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_CommSemiRing_preserves_limits_aux CommRingCat.forget₂CommSemiRingPreservesLimitsAux

/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat CommSemiRingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_CommSemiRing_preserves_limits_of_size CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize

instance forget₂CommSemiRingPreservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRingCat.{u}) :=
  CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_CommSemiRing_preserves_limits CommRingCat.forget₂CommSemiRingPreservesLimits

/-- The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget CommRingCat.{max v u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone.{v, v} (limitConeIsLimit.{v, u} F)
          (Types.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align CommRing.forget_preserves_limits_of_size CommRingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.forget_preserves_limits CommRingCat.forgetPreservesLimits

end CommRingCat
