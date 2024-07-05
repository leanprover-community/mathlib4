/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Ring.Subring.Basic

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

universe v u w

noncomputable section

namespace SemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u})

instance semiringObj (j) : Semiring ((F ⋙ forget SemiRingCat).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
set_option linter.uppercaseLean3 false in
#align SemiRing.semiring_obj SemiRingCat.semiringObj

/-- The flat sections of a functor into `SemiRingCat` form a subsemiring of all sections.
-/
def sectionsSubsemiring : Subsemiring (∀ j, F.obj j) :=
  -- Porting note: if `f` and `g` were inlined, it does not compile
  letI f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  letI g : J ⥤ MonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} MonCat.{u}
  { (MonCat.sectionsSubmonoid (J := J) g),
    (AddMonCat.sectionsAddSubmonoid (J := J) f) with
    carrier := (F ⋙ forget SemiRingCat).sections }
set_option linter.uppercaseLean3 false in
#align SemiRing.sections_subsemiring SemiRingCat.sectionsSubsemiring

instance sectionsSemiring : Semiring (F ⋙ forget SemiRingCat.{u}).sections :=
  (sectionsSubsemiring F).toSemiring

variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]

instance limitSemiring :
    Semiring (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat.{u})).pt :=
  letI : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
  inferInstanceAs <| Semiring (Shrink (F ⋙ forget SemiRingCat).sections)
set_option linter.uppercaseLean3 false in
#align SemiRing.limit_semiring SemiRingCat.limitSemiring

/-- `limit.π (F ⋙ forget SemiRingCat) j` as a `RingHom`. -/
def limitπRingHom (j) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  -- Porting note: if `f` and `g` were inlined, it does not compile
  letI f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  letI : Small.{u} (Functor.sections (f ⋙ forget AddMonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{u}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget SemiRingCat)).π.app j }
set_option linter.uppercaseLean3 false in
#align SemiRing.limit_π_ring_hom SemiRingCat.limitπRingHom

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits SemiRingCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `SemiRingCat`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπRingHom.{v, u} F
      naturality := fun {_ _} f => RingHom.coe_inj
        ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits.limit_cone SemiRingCat.HasLimits.limitCone

/-- Witness that the limit cone in `SemiRingCat` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_})
    (fun s => rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [Functor.mapCone_π_app, forget_map, map_mul]
    erw [← map_mul (MulEquiv.symm Shrink.mulEquiv)]
    rfl
  · simp only [Functor.mapCone_π_app, forget_map, map_zero]
    rfl
  · intro x y
    simp only [Functor.mapCone_π_app, forget_map, map_add]
    erw [← map_add (AddEquiv.symm Shrink.addEquiv)]
    rfl
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits.limit_cone_is_limit SemiRingCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

/-- If `(F ⋙ forget SemiRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/-- If `J` is `u`-small, `SemiRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J SemiRingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} SemiRingCat.{u} where
  has_limits_of_shape _ _ := { }
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits_of_size SemiRingCat.hasLimitsOfSize

instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.has_limits SemiRingCat.hasLimits

/--
Auxiliary lemma to prove the cone induced by `limitCone` is a limit cone.
-/
def forget₂AddCommMonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_AddCommMon_preserves_limits_aux SemiRingCat.forget₂AddCommMonPreservesLimitsAux

/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat AddCommMonCat.{u}) where
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
def forget₂MonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})
set_option linter.uppercaseLean3 false in
#align SemiRing.forget₂_Mon_preserves_limits_aux SemiRingCat.forget₂MonPreservesLimitsAux

/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂MonPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat MonCat.{u}) where
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
instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }
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

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommSemiRingCat.{u})

instance commSemiringObj (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) :=
  inferInstanceAs <| CommSemiring (F.obj j)
set_option linter.uppercaseLean3 false in
#align CommSemiRing.comm_semiring_obj CommSemiRingCat.commSemiringObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))]

instance limitCommSemiring :
    CommSemiring (Types.Small.limitCone.{v, u} (F ⋙ forget CommSemiRingCat.{u})).pt :=
  letI : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (∀ j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
  inferInstanceAs <| CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_comm_semiring CommSemiRingCat.limitCommSemiring

/-- We show that the forgetful functor `CommSemiRingCat ⥤ SemiRingCat` creates limits.

All we need to do is notice that the limit point has a `CommSemiring` instance available,
and then reuse the existing limit.
-/
instance :
    CreatesLimit F (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) :=
  -- Porting note: `CommSemiRingCat ⥤ Type` reflecting isomorphism is needed to make Lean see that
  -- `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism. `CommSemiRingCat ⥤ Type` reflecting
  -- isomorphism is added manually since Lean can't see it, but even with this addition Lean can not
  -- see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this instance is also added.
  letI : (forget CommSemiRingCat.{u}).ReflectsIsomorphisms :=
    CommSemiRingCat.forgetReflectIsos.{u}
  letI : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))
  let c : Cone F :=
    { pt := CommSemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun j => CommSemiRingCat.ofHom <| SemiRingCat.limitπRingHom.{v, u} (J := J)
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) j
          naturality := (SemiRingCat.HasLimits.limitCone.{v, u}
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u})).π.naturality } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit := by
        refine IsLimit.ofFaithful (forget₂ CommSemiRingCat.{u} SemiRingCat.{u})
          (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `CommSemiRingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_cone CommSemiRingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommSemiRing.limit_cone_is_limit CommSemiRingCat.limitConeIsLimit

/-- If `(F ⋙ forget CommSemiRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/-- If `J` is `u`-small, `CommSemiRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommSemiRingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommSemiRingCat.{u} where
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_limits_of_size CommSemiRingCat.hasLimitsOfSize

instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommSemiRing.has_limits CommSemiRingCat.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }
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
instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
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

variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})

instance ringObj (j) : Ring ((F ⋙ forget RingCat).obj j) :=
  inferInstanceAs <| Ring (F.obj j)
set_option linter.uppercaseLean3 false in
#align Ring.ring_obj RingCat.ringObj

/-- The flat sections of a functor into `RingCat` form a subring of all sections.
-/
def sectionsSubring : Subring (∀ j, F.obj j) :=
  letI f : J ⥤ AddGrp.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrp.{u} ⋙
    forget₂ AddCommGrp.{u} AddGrp.{u}
  letI g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrp.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carrier := (F ⋙ forget RingCat.{u}).sections }
set_option linter.uppercaseLean3 false in
#align Ring.sections_subring RingCat.sectionsSubring

variable [Small.{u} (Functor.sections (F ⋙ forget RingCat.{u}))]

instance limitRing : Ring.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget RingCat.{u})).pt :=
  letI : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
  inferInstanceAs <| Ring (Shrink _)
set_option linter.uppercaseLean3 false in
#align Ring.limit_ring RingCat.limitRing

/-- We show that the forgetful functor `CommRingCat ⥤ RingCat` creates limits.

All we need to do is notice that the limit point has a `Ring` instance available,
and then reuse the existing limit.
-/
instance : CreatesLimit F (forget₂ RingCat.{u} SemiRingCat.{u}) :=
  have : (forget₂ RingCat SemiRingCat).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  let c : Cone F :=
  { pt := RingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
      { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} (F ⋙ forget₂ _ SemiRingCat) x
        naturality := fun _ _ f => RingHom.coe_inj
          ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := by apply IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- A choice of limit cone for a functor into `RingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))
set_option linter.uppercaseLean3 false in
#align Ring.limit_cone RingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align Ring.limit_cone_is_limit RingCat.limitConeIsLimit

/-- If `(F ⋙ forget RingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})

/-- If `J` is `u`-small, `RingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J RingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} RingCat.{u} where
set_option linter.uppercaseLean3 false in
#align Ring.has_limits_of_size RingCat.hasLimitsOfSize

instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.has_limits RingCat.hasLimits

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ RingCat SemiRingCat.{u}) where
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
def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ RingCat.{u} AddCommGrp).mapCone (limitCone.{v, u} F)) := by
  -- Porting note: inline `f` would not compile
  letI f := F ⋙ forget₂ RingCat.{u} AddCommGrp.{u}
  letI : Small.{u} (Functor.sections (f ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrp.limitConeIsLimit.{v, u} f
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits_aux RingCat.forget₂AddCommGroupPreservesLimitsAux

/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat.{u} AddCommGrp.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits_of_size RingCat.forget₂AddCommGroupPreservesLimitsOfSize

instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGrp.{u}) :=
  RingCat.forget₂AddCommGroupPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align Ring.forget₂_AddCommGroup_preserves_limits RingCat.forget₂AddCommGroupPreservesLimits

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
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

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})

instance commRingObj (j) : CommRing ((F ⋙ forget CommRingCat).obj j) :=
  inferInstanceAs <| CommRing (F.obj j)
set_option linter.uppercaseLean3 false in
#align CommRing.comm_ring_obj CommRingCat.commRingObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommRingCat))]

instance limitCommRing :
    CommRing.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget CommRingCat.{u})).pt :=
  letI : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
  inferInstanceAs <| CommRing (Shrink _)
set_option linter.uppercaseLean3 false in
#align CommRing.limit_comm_ring CommRingCat.limitCommRing

/-- We show that the forgetful functor `CommRingCat ⥤ RingCat` creates limits.

All we need to do is notice that the limit point has a `CommRing` instance available,
and then reuse the existing limit.
-/
instance :
   CreatesLimit F (forget₂ CommRingCat.{u} RingCat.{u}) :=
  /-
    A terse solution here would be
    ```
    createsLimitOfFullyFaithfulOfIso (CommRingCat.of (limit (F ⋙ forget _))) (Iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    -- Porting note: need to add these instances manually
    have : (forget₂ CommRingCat.{u} RingCat.{u}).ReflectsIsomorphisms :=
      CategoryTheory.reflectsIsomorphisms_forget₂ _ _
    have : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
      inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
    let F' := F ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
    have : Small.{u} (Functor.sections (F' ⋙ forget _)) :=
      inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
    let c : Cone F :=
    { pt := CommRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} F' x
          naturality :=
            fun _ _ f => RingHom.coe_inj
              ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
    createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (RingCat.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{u})
          (RingCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (fun s : Cone F => ofHom <|
              (RingCat.limitConeIsLimit.{v, u}
                (F ⋙ forget₂ CommRingCat.{u} RingCat.{u})).lift
                ((forget₂ _ RingCat.{u}).mapCone s)) fun _ => rfl }

/-- A choice of limit cone for a functor into `CommRingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
set_option linter.uppercaseLean3 false in
#align CommRing.limit_cone CommRingCat.limitCone

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _
set_option linter.uppercaseLean3 false in
#align CommRing.limit_cone_is_limit CommRingCat.limitConeIsLimit

/-- If `(F ⋙ forget CommRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})

/-- If `J` is `u`-small, `CommRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommRingCat.{u} where

/-- The category of commutative rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommRingCat.{u} where
set_option linter.uppercaseLean3 false in
#align CommRing.has_limits_of_size CommRingCat.hasLimitsOfSize

instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.has_limits CommRingCat.hasLimits

/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂RingPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_Ring_preserves_limits_of_size CommRingCat.forget₂RingPreservesLimitsOfSize

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂RingPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_Ring_preserves_limits CommRingCat.forget₂RingPreservesLimits

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  letI : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
    inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})
set_option linter.uppercaseLean3 false in
#align CommRing.forget₂_CommSemiRing_preserves_limits_aux CommRingCat.forget₂CommSemiRingPreservesLimitsAux

/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRingPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat CommSemiRingCat.{u}) where
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
instance forgetPreservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }
set_option linter.uppercaseLean3 false in
#align CommRing.forget_preserves_limits_of_size CommRingCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forgetPreservesLimitsOfSize.{u, u}
set_option linter.uppercaseLean3 false in
#align CommRing.forget_preserves_limits CommRingCat.forgetPreservesLimits

end CommRingCat
