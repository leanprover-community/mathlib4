/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Algebra.Ring.Subring.Defs

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

/-- The flat sections of a functor into `SemiRingCat` form a subsemiring of all sections. -/
def sectionsSubsemiring : Subsemiring (∀ j, F.obj j) :=
  { (MonCat.sectionsSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} MonCat.{u})),
    (AddMonCat.sectionsAddSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
      forget₂ AddCommMonCat AddMonCat)) with
    carrier := (F ⋙ forget SemiRingCat).sections }

instance sectionsSemiring : Semiring (F ⋙ forget SemiRingCat.{u}).sections :=
  (sectionsSubsemiring F).toSemiring

variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]

instance limitSemiring :
    Semiring (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat.{u})).pt :=
  let _ : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
  inferInstanceAs <| Semiring (Shrink (F ⋙ forget SemiRingCat).sections)

/-- `limit.π (F ⋙ forget SemiRingCat) j` as a `RingHom`. -/
def limitπRingHom (j) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  let f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  let _ : Small.{u} (Functor.sections (f ⋙ forget AddMonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{u}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget SemiRingCat)).π.app j }

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
    { app := fun j ↦ SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality := fun {_ _} f ↦ hom_ext <| RingHom.coe_inj
        ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `SemiRingCat` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_})
    (fun s => rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
      forget_map, map_mul, EquivLike.coe_apply]
    rw [← equivShrink_mul]
    rfl
  · simp only [Functor.mapCone_π_app, forget_map, map_zero]
    rfl
  · intro x y
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
      forget_map, map_add, EquivLike.coe_apply]
    rw [← equivShrink_add]
    rfl

end HasLimits

open HasLimits

/-- If `(F ⋙ forget SemiRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/-- If `J` is `u`-small, `SemiRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J SemiRingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} SemiRingCat.{u} where
  has_limits_of_shape _ _ := { }

instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}

/--
Auxiliary lemma to prove the cone induced by `limitCone` is a limit cone.
-/
def forget₂AddCommMonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}

/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat AddCommMonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }

instance forget₂AddCommMon_preservesLimits :
    PreservesLimits (forget₂ SemiRingCat AddCommMonCat.{u}) :=
  SemiRingCat.forget₂AddCommMon_preservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂MonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})

/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat MonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }

instance forget₂Mon_preservesLimits : PreservesLimits (forget₂ SemiRingCat MonCat.{u}) :=
  SemiRingCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- The forgetful functor from semirings to types preserves all limits.
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }

instance forget_preservesLimits : PreservesLimits (forget SemiRingCat.{u}) :=
  SemiRingCat.forget_preservesLimitsOfSize.{u, u}

end SemiRingCat

namespace CommSemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommSemiRingCat.{u})

instance commSemiringObj (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) :=
  inferInstanceAs <| CommSemiring (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))]

instance limitCommSemiring :
    CommSemiring (Types.Small.limitCone.{v, u} (F ⋙ forget CommSemiRingCat.{u})).pt :=
  let _ : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (∀ j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
  inferInstanceAs <| CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)

/-- We show that the forgetful functor `CommSemiRingCat ⥤ SemiRingCat` creates limits.

All we need to do is notice that the limit point has a `CommSemiring` instance available,
and then reuse the existing limit.
-/
instance :
    CreatesLimit F (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) :=
  -- Porting note: Lean can not see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this
  -- instance is added.
  let _ : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))
  let c : Cone F :=
    { pt := CommSemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun j => CommSemiRingCat.ofHom <| SemiRingCat.limitπRingHom.{v, u} (J := J)
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) j
          naturality := fun _ _ f ↦ hom_ext <| congrArg SemiRingCat.Hom.hom <|
            (SemiRingCat.HasLimits.limitCone.{v, u}
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u})).π.naturality f } }
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
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommSemiRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/-- If `J` is `u`-small, `CommSemiRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommSemiRingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommSemiRingCat.{u} where

instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }

instance forget₂SemiRing_preservesLimits :
    PreservesLimits (forget₂ CommSemiRingCat SemiRingCat.{u}) :=
  CommSemiRingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

instance forget_preservesLimits : PreservesLimits (forget CommSemiRingCat.{u}) :=
  CommSemiRingCat.forget_preservesLimitsOfSize.{u, u}

end CommSemiRingCat

namespace RingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})

instance ringObj (j) : Ring ((F ⋙ forget RingCat).obj j) :=
  inferInstanceAs <| Ring (F.obj j)

/-- The flat sections of a functor into `RingCat` form a subring of all sections.
-/
def sectionsSubring : Subring (∀ j, F.obj j) :=
  let f : J ⥤ AddGrp.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrp.{u} ⋙
    forget₂ AddCommGrp.{u} AddGrp.{u}
  let g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrp.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carrier := (F ⋙ forget RingCat.{u}).sections }

variable [Small.{u} (Functor.sections (F ⋙ forget RingCat.{u}))]

instance limitRing : Ring.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget RingCat.{u})).pt :=
  let _ : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
  inferInstanceAs <| Ring (Shrink _)

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
        naturality := fun _ _ f => hom_ext <| RingHom.coe_inj
          ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := by apply IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun _ => _) fun _ => rfl }

/-- A choice of limit cone for a functor into `RingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget RingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})

/-- If `J` is `u`-small, `RingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J RingCat.{u} where

/-- The category of rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} RingCat.{u} where

instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ RingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
      { preservesLimit := fun {F} =>
          preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }

instance forget₂SemiRing_preservesLimits : PreservesLimits (forget₂ RingCat SemiRingCat.{u}) :=
  RingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ RingCat.{u} AddCommGrp).mapCone (limitCone.{v, u} F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ RingCat.{u} AddCommGrp.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrp.limitConeIsLimit.{v, u} _

/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat.{u} AddCommGrp.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }

instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGrp.{u}) :=
  RingCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u}

/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

instance forget_preservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forget_preservesLimitsOfSize.{u, u}

end RingCat

namespace CommRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})

instance commRingObj (j) : CommRing ((F ⋙ forget CommRingCat).obj j) :=
  inferInstanceAs <| CommRing (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommRingCat))]

instance limitCommRing :
    CommRing.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget CommRingCat.{u})).pt :=
  let _ : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
  inferInstanceAs <| CommRing (Shrink _)

/-- We show that the forgetful functor `CommRingCat ⥤ RingCat` creates limits.

All we need to do is notice that the limit point has a `CommRing` instance available,
and then reuse the existing limit.
-/
instance : CreatesLimit F (forget₂ CommRingCat.{u} RingCat.{u}) :=
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
            fun _ _ f => hom_ext <| RingHom.coe_inj
              ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }
    createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (RingCat.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{u})
          (RingCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (fun s : Cone F => CommRingCat.ofHom <|
              (RingCat.limitConeIsLimit.{v, u}
                (F ⋙ forget₂ CommRingCat.{u} RingCat.{u})).lift
                ((forget₂ _ RingCat.{u}).mapCone s) |>.hom) fun _ => rfl }

/-- A choice of limit cone for a functor into `CommRingCat`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- The chosen cone is a limit cone. (Generally, you'll just want to use `limit.cone F`.) -/
def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommRingCat).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})

/-- If `J` is `u`-small, `CommRingCat.{u}` has limits of shape `J`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommRingCat.{u} where

/-- The category of commutative rings has all limits. -/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommRingCat.{u} where

instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }

instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂Ring_preservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  let _ : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
    inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})

/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }

instance forget₂CommSemiRing_preservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRingCat.{u}) :=
  CommRingCat.forget₂CommSemiRing_preservesLimitsOfSize.{u, u}

/-- The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

instance forget_preservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forget_preservesLimitsOfSize.{u, u}

end CommRingCat
