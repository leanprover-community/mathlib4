/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.creates from "leanprover-community/mathlib"@"fe5e4ce6c72d96d77ad40ac832a6e7f8040990bc"

/-!
# Creating (co)limits

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/


open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section Creates

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  /-- a cone in the source category of the functor -/
  liftedCone : Cone K
  /-- the isomorphism expressing that `liftedCone` lifts the given cone -/
  validLift : F.mapCone liftedCone ≅ c
#align category_theory.liftable_cone CategoryTheory.LiftableCone

/-- Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  /-- a cocone in the source category of the functor -/
  liftedCocone : Cocone K
  /-- the isomorphism expressing that `liftedCocone` lifts the given cocone -/
  validLift : F.mapCocone liftedCocone ≅ c
#align category_theory.liftable_cocone CategoryTheory.LiftableCocone

/-- Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `createsLimitOfReflectsIso`.
-/
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  /-- any limit cone can be lifted to a cone above -/
  lifts : ∀ c, IsLimit c → LiftableCone K F c
#align category_theory.creates_limit CategoryTheory.CreatesLimit

/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance
#align category_theory.creates_limits_of_shape CategoryTheory.CreatesLimitsOfShape

-- This should be used with explicit universe variables.
/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
@[nolint checkUnivs, pp_with_univ]
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance
#align category_theory.creates_limits_of_size CategoryTheory.CreatesLimitsOfSize

/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F
#align category_theory.creates_limits CategoryTheory.CreatesLimits

/-- Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `createsColimitOfReflectsIso`.
-/
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  /-- any limit cocone can be lifted to a cocone above -/
  lifts : ∀ c, IsColimit c → LiftableCocone K F c
#align category_theory.creates_colimit CategoryTheory.CreatesColimit

/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by infer_instance
#align category_theory.creates_colimits_of_shape CategoryTheory.CreatesColimitsOfShape

-- This should be used with explicit universe variables.
/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[nolint checkUnivs, pp_with_univ]
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance
#align category_theory.creates_colimits_of_size CategoryTheory.CreatesColimitsOfSize

/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F
#align category_theory.creates_colimits CategoryTheory.CreatesColimits

-- see Note [lower instance priority]
attribute [instance 100] CreatesLimitsOfShape.CreatesLimit CreatesLimitsOfSize.CreatesLimitsOfShape
  CreatesColimitsOfShape.CreatesColimit CreatesColimitsOfSize.CreatesColimitsOfShape

-- see Note [lower instance priority]
-- Interface to the `CreatesLimit` class.
/-- `liftLimit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone
#align category_theory.lift_limit CategoryTheory.liftLimit

/-- The lifted cone has an image isomorphic to the original cone. -/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift
#align category_theory.lifted_limit_maps_to_original CategoryTheory.liftedLimitMapsToOriginal

/-- The lifted cone is a limit. -/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  ReflectsLimit.reflects (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)
#align category_theory.lifted_limit_is_limit CategoryTheory.liftedLimitIsLimit

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }
#align category_theory.has_limit_of_created CategoryTheory.hasLimit_of_created

/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => hasLimit_of_created G F⟩
#align category_theory.has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩
#align category_theory.has_limits_of_has_limits_creates_limits CategoryTheory.hasLimits_of_hasLimits_createsLimits

-- Interface to the `CreatesColimit` class.
/-- `liftColimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone
#align category_theory.lift_colimit CategoryTheory.liftColimit

/-- The lifted cocone has an image isomorphic to the original cocone. -/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift
#align category_theory.lifted_colimit_maps_to_original CategoryTheory.liftedColimitMapsToOriginal

/-- The lifted cocone is a colimit. -/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  ReflectsColimit.reflects (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)
#align category_theory.lifted_colimit_is_colimit CategoryTheory.liftedColimitIsColimit

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }
#align category_theory.has_colimit_of_created CategoryTheory.hasColimit_of_created

/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => hasColimit_of_created G F⟩
#align category_theory.has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun _ _ => hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩
#align category_theory.has_colimits_of_has_colimits_creates_colimits CategoryTheory.hasColimits_of_hasColimits_createsColimits

instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where
#align category_theory.reflects_limits_of_shape_of_creates_limits_of_shape CategoryTheory.reflectsLimitsOfShapeOfCreatesLimitsOfShape

instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where
#align category_theory.reflects_limits_of_creates_limits CategoryTheory.reflectsLimitsOfCreatesLimits

instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where
#align category_theory.reflects_colimits_of_shape_of_creates_colimits_of_shape CategoryTheory.reflectsColimitsOfShapeOfCreatesColimitsOfShape

instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where
#align category_theory.reflects_colimits_of_creates_colimits CategoryTheory.reflectsColimitsOfCreatesColimits

/-- A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends
  LiftableCone K F c where
  /-- the lifted cone is limit -/
  makesLimit : IsLimit liftedCone
#align category_theory.lifts_to_limit CategoryTheory.LiftsToLimit

/-- A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure LiftsToColimit (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c) extends
  LiftableCocone K F c where
  /-- the lifted cocone is colimit -/
  makesColimit : IsColimit liftedCocone
#align category_theory.lifts_to_colimit CategoryTheory.LiftsToColimit

/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F]
    (h : ∀ c t, LiftsToLimit K F c t) : CreatesLimit K F
    where
  lifts c t := (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd => by
        let d' : Cone K := (h (F.mapCone d) hd).toLiftableCone.liftedCone
        let i : F.mapCone d' ≅ F.mapCone d :=
          (h (F.mapCone d) hd).toLiftableCone.validLift
        let hd' : IsLimit d' := (h (F.mapCone d) hd).makesLimit
        let f : d ⟶ d' := hd'.liftConeMorphism d
        have : (Cones.functoriality K F).map f = i.inv :=
          (hd.ofIsoLimit i.symm).uniq_cone_morphism
        haveI : IsIso ((Cones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI : IsIso f := isIso_of_reflects_iso f (Cones.functoriality K F)
        exact IsLimit.ofIsoLimit hd' (asIso f).symm }
#align category_theory.creates_limit_of_reflects_iso CategoryTheory.createsLimitOfReflectsIso

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to exhibit a lift
of a limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) :
    CreatesLimit K F :=
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := i ≪≫ IsLimit.uniqueUpToIso hl t
      makesLimit :=
        IsLimit.ofFaithful F (IsLimit.ofIsoLimit hl i.symm) _ fun _ => F.image_preimage _ }
#align category_theory.creates_limit_of_fully_faithful_of_lift' CategoryTheory.createsLimitOfFullyFaithfulOfLift'

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) :
    CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i
#align category_theory.creates_limit_of_fully_faithful_of_lift CategoryTheory.createsLimitOfFullyFaithfulOfLift

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to show that a
limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j => F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa using (l.w f).symm } }
    (Cones.ext i fun j => by simp only [Functor.image_preimage, Functor.mapCone_π_app])
#align category_theory.creates_limit_of_fully_faithful_of_iso' CategoryTheory.createsLimitOfFullyFaithfulOfIso'

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i
#align category_theory.creates_limit_of_fully_faithful_of_iso CategoryTheory.createsLimitOfFullyFaithfulOfIso

-- see Note [lower instance priority]
/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
instance (priority := 100) preservesLimitOfCreatesLimitAndHasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves t := IsLimit.ofIsoLimit (limit.isLimit _)
    ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
      (Cones.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))
#align category_theory.preserves_limit_of_creates_limit_and_has_limit CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit

-- see Note [lower instance priority]
/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
instance (priority := 100) preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where
#align category_theory.preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape CategoryTheory.preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesLimitsOfCreatesLimitsAndHasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] : PreservesLimitsOfSize.{w, w'} F
    where
#align category_theory.preserves_limits_of_creates_limits_and_has_limits CategoryTheory.preservesLimitsOfCreatesLimitsAndHasLimits

/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F]
    (h : ∀ c t, LiftsToColimit K F c t) : CreatesColimit K F
    where
  lifts c t := (h c t).toLiftableCocone
  toReflectsColimit :=
    {
      reflects := fun {d} hd => by
        let d' : Cocone K := (h (F.mapCocone d) hd).toLiftableCocone.liftedCocone
        let i : F.mapCocone d' ≅ F.mapCocone d :=
          (h (F.mapCocone d) hd).toLiftableCocone.validLift
        let hd' : IsColimit d' := (h (F.mapCocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.descCoconeMorphism d
        have : (Cocones.functoriality K F).map f = i.hom :=
          (hd.ofIsoColimit i.symm).uniq_cocone_morphism
        haveI : IsIso ((Cocones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        haveI := isIso_of_reflects_iso f (Cocones.functoriality K F)
        exact IsColimit.ofIsoColimit hd' (asIso f) }
#align category_theory.creates_colimit_of_reflects_iso CategoryTheory.createsColimitOfReflectsIso

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to exhibit a
lift of a colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone c ≅ l) :
    CreatesColimit K F :=
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := c
      validLift := i ≪≫ IsColimit.uniqueUpToIso hl t
      makesColimit :=
        IsColimit.ofFaithful F (IsColimit.ofIsoColimit hl i.symm) _ fun _ => F.image_preimage _ }
#align category_theory.creates_colimit_of_fully_faithful_of_lift' CategoryTheory.createsColimitOfFullyFaithfulOfLift'

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)) :
    CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i
#align category_theory.creates_colimit_of_fully_faithful_of_lift CategoryTheory.createsColimitOfFullyFaithfulOfLift

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to show that
a colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocones.ext i fun j => by simp)
#align category_theory.creates_colimit_of_fully_faithful_of_iso' CategoryTheory.createsColimitOfFullyFaithfulOfIso'

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i
#align category_theory.creates_colimit_of_fully_faithful_of_iso CategoryTheory.createsColimitOfFullyFaithfulOfIso

-- see Note [lower instance priority]
/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
instance (priority := 100) preservesColimitOfCreatesColimitAndHasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F where
  preserves t :=
    IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocones.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))
#align category_theory.preserves_colimit_of_creates_colimit_and_has_colimit CategoryTheory.preservesColimitOfCreatesColimitAndHasColimit

-- see Note [lower instance priority]
/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
instance (priority := 100) preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] : PreservesColimitsOfShape J F
    where
#align category_theory.preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape CategoryTheory.preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesColimitsOfCreatesColimitsAndHasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where
#align category_theory.preserves_colimits_of_creates_colimits_and_has_colimits CategoryTheory.preservesColimitsOfCreatesColimitsAndHasColimits

/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] :
    CreatesLimit K₂ F :=
  { reflectsLimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCone := (Cones.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cones.postcompose (isoWhiskerRight h F).hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cones.ext (Iso.refl _) fun j => by
                dsimp
                rw [Category.assoc, ← F.map_comp]
                simp } }
#align category_theory.creates_limit_of_iso_diagram CategoryTheory.createsLimitOfIsoDiagram

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G
    where
  lifts c t :=
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine' (IsLimit.mapConeEquiv h _).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  toReflectsLimit := reflectsLimitOfNatIso _ h
#align category_theory.creates_limit_of_nat_iso CategoryTheory.createsLimitOfNatIso

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := createsLimitOfNatIso h
#align category_theory.creates_limits_of_shape_of_nat_iso CategoryTheory.createsLimitsOfShapeOfNatIso

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfNatIso h
#align category_theory.creates_limits_of_nat_iso CategoryTheory.createsLimitsOfNatIso

/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] :
    CreatesColimit K₂ F :=
  { reflectsColimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCocone := (Cocones.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocones.precompose (isoWhiskerRight h F).inv).mapIso
                (liftedColimitMapsToOriginal t') ≪≫
              Cocones.ext (Iso.refl _) fun j => by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }
#align category_theory.creates_colimit_of_iso_diagram CategoryTheory.createsColimitOfIsoDiagram

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G
    where
  lifts c t :=
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine' (IsColimit.mapCoconeEquiv h _).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv _ _).symm t }
  toReflectsColimit := reflectsColimitOfNatIso _ h
#align category_theory.creates_colimit_of_nat_iso CategoryTheory.createsColimitOfNatIso

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := createsColimitOfNatIso h
#align category_theory.creates_colimits_of_shape_of_nat_iso CategoryTheory.createsColimitsOfShapeOfNatIso

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfNatIso h
#align category_theory.creates_colimits_of_nat_iso CategoryTheory.createsColimitsOfNatIso

-- For the inhabited linter later.
/-- If F creates the limit of K, any cone lifts to a limit. -/
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t
    where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t
#align category_theory.lifts_to_limit_of_creates CategoryTheory.liftsToLimitOfCreates

-- For the inhabited linter later.
/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t
    where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t
#align category_theory.lifts_to_colimit_of_creates CategoryTheory.liftsToColimitOfCreates

/-- Any cone lifts through the identity functor. -/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c
    where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cones.ext (Iso.refl _)
#align category_theory.id_lifts_cone CategoryTheory.idLiftsCone

/-- The identity functor creates all limits. -/
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape :=
    { CreatesLimit := { lifts := fun c _ => idLiftsCone c } }
#align category_theory.id_creates_limits CategoryTheory.idCreatesLimits

/-- Any cocone lifts through the identity functor. -/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c
    where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocones.ext (Iso.refl _)
#align category_theory.id_lifts_cocone CategoryTheory.idLiftsCocone

/-- The identity functor creates all colimits. -/
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape :=
    { CreatesColimit := { lifts := fun c _ => idLiftsCocone c } }
#align category_theory.id_creates_colimits CategoryTheory.idCreatesColimits

/-- Satisfy the inhabited linter -/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩
#align category_theory.inhabited_liftable_cone CategoryTheory.inhabitedLiftableCone

instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩
#align category_theory.inhabited_liftable_cocone CategoryTheory.inhabitedLiftableCocone

/-- Satisfy the inhabited linter -/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩
#align category_theory.inhabited_lifts_to_limit CategoryTheory.inhabitedLiftsToLimit

instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩
#align category_theory.inhabited_lifts_to_colimit CategoryTheory.inhabitedLiftsToColimit

section Comp

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

instance compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] :
    CreatesLimit K (F ⋙ G) where
  lifts c t := by
    let c' : Cone ((K ⋙ F) ⋙ G) := c
    let t' : IsLimit c' := t
    exact
      { liftedCone := liftLimit (liftedLimitIsLimit t')
        validLift := (Cones.functoriality (K ⋙ F) G).mapIso
            (liftedLimitMapsToOriginal (liftedLimitIsLimit t')) ≪≫
          liftedLimitMapsToOriginal t' }
#align category_theory.comp_creates_limit CategoryTheory.compCreatesLimit

instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance
#align category_theory.comp_creates_limits_of_shape CategoryTheory.compCreatesLimitsOfShape

instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance
#align category_theory.comp_creates_limits CategoryTheory.compCreatesLimits

instance compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] :
    CreatesColimit K (F ⋙ G) where
  lifts c t :=
    let c' : Cocone ((K ⋙ F) ⋙ G) := c
    let t' : IsColimit c' := t
    { liftedCocone := liftColimit (liftedColimitIsColimit t')
      validLift :=
        (Cocones.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t')) ≪≫
          liftedColimitMapsToOriginal t' }
#align category_theory.comp_creates_colimit CategoryTheory.compCreatesColimit

instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance
#align category_theory.comp_creates_colimits_of_shape CategoryTheory.compCreatesColimitsOfShape

instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance
#align category_theory.comp_creates_colimits CategoryTheory.compCreatesColimits

end Comp

end Creates

end CategoryTheory
