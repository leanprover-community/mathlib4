/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Creating (co)limits

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

namespace CategoryTheory

universe w' w'₁ w w₁ v₁ v₂ v₃ u₁ u₂ u₃

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

/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
@[nolint checkUnivs, pp_with_univ]
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance

/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F

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

/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[nolint checkUnivs, pp_with_univ]
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance

/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance 100] CreatesLimitsOfShape.CreatesLimit CreatesLimitsOfSize.CreatesLimitsOfShape
  CreatesColimitsOfShape.CreatesColimit CreatesColimitsOfSize.CreatesColimitsOfShape

-- see Note [lower instance priority]
-- Interface to the `CreatesLimit` class.
/-- `liftLimit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone

/-- The lifted cone has an image isomorphic to the original cone. -/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift

lemma liftedLimitMapsToOriginal_inv_map_π
    {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (j : J) :
      (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app j) = c.π.app j := by
  rw [show F.map ((liftLimit t).π.app j) = (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app j
    from (by simp), ← Category.assoc, ← Cone.category_comp_hom]
  simp

/-- The lifted cone is a limit. -/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  isLimitOfReflects _ (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { cone := liftLimit (limit.isLimit (K ⋙ F))
      isLimit := liftedLimitIsLimit _ }

/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G ↦ hasLimit_of_created G F⟩

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem hasLimits_of_hasLimits_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun _ _ ↦ hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F⟩

-- Interface to the `CreatesColimit` class.
/-- `liftColimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone

/-- The lifted cocone has an image isomorphic to the original cocone. -/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift

/-- The lifted cocone is a colimit. -/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  isColimitOfReflects _ (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { cocone := liftColimit (colimit.isColimit (K ⋙ F))
      isColimit := liftedColimitIsColimit _ }

/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G ↦ hasColimit_of_created G F⟩

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem hasColimits_of_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun _ _ ↦ hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F⟩

instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where

instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where

instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where

instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where

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

/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToLimit K F c t) : CreatesLimit K F where
  lifts c t := (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun {d} hd ↦ ⟨by
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
        exact IsLimit.ofIsoLimit hd' (asIso f).symm⟩ }

/-- If `F` reflects isomorphisms and we can lift a single limit cone to a limit cone, then `F`
creates limits. Note that unlike `createsLimitOfReflectsIso`, to apply this result it is
necessary to know that `K ⋙ F` actually has a limit. -/
def createsLimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cone (K ⋙ F)} (hc : IsLimit c) (h : LiftsToLimit K F c hc) : CreatesLimit K F :=
  createsLimitOfReflectsIso fun _ t ↦
    { liftedCone := h.liftedCone
      validLift := h.validLift ≪≫ IsLimit.uniqueUpToIso hc t
      makesLimit := h.makesLimit }

/-- If `F` reflects isomorphisms, and we already know that the limit exists in the source and `F`
preserves it, then `F` creates that limit. -/
def createsLimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfReflectsIso' (isLimitOfPreserves F (limit.isLimit _))
    ⟨⟨_, Iso.refl _⟩, limit.isLimit _⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to exhibit a lift
of a limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) :
    CreatesLimit K F :=
  createsLimitOfReflectsIso' hl ⟨⟨c, i⟩, isLimitOfReflects F (IsLimit.ofIsoLimit hl i.symm)⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) :
    CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to show that a
limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt := X
      π :=
        { app := fun j ↦ F.preimage (i.hom ≫ l.π.app j)
          naturality := fun Y Z f ↦
            F.map_injective <| by
              simpa using (l.w f).symm } }
    (Cones.ext i fun j ↦ by simp only [Functor.map_preimage, Functor.mapCone_π_app])

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `HasLimit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i

/-- A fully faithful functor that preserves a limit that exists also creates the limit. -/
def createsLimitOfFullyFaithfulOfPreserves {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasLimit K] [PreservesLimit K F] : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (isLimitOfPreserves _ (limit.isLimit K)) _ (Iso.refl _)

-- see Note [lower instance priority]
/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
instance (priority := 100) preservesLimit_of_createsLimit_and_hasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves t := ⟨IsLimit.ofIsoLimit (limit.isLimit _)
    ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
      (Cones.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
instance (priority := 100) preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesLimits_of_createsLimits_and_hasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] :
    PreservesLimitsOfSize.{w, w'} F where

/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    (h : ∀ c t, LiftsToColimit K F c t) : CreatesColimit K F where
  lifts c t := (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun {d} hd ↦ ⟨by
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
        exact IsColimit.ofIsoColimit hd' (asIso f)⟩ }

/-- If `F` reflects isomorphisms and we can lift a single colimit cocone to a colimit cocone, then
`F` creates limits. Note that unlike `createsColimitOfReflectsIso`, to apply this result it is
necessary to know that `K ⋙ F` actually has a colimit. -/
def createsColimitOfReflectsIso' {K : J ⥤ C} {F : C ⥤ D} [F.ReflectsIsomorphisms]
    {c : Cocone (K ⋙ F)} (hc : IsColimit c) (h : LiftsToColimit K F c hc) : CreatesColimit K F :=
  createsColimitOfReflectsIso fun _ t ↦
    { liftedCocone := h.liftedCocone
      validLift := h.validLift ≪≫ IsColimit.uniqueUpToIso hc t
      makesColimit := h.makesColimit }

/-- If `F` reflects isomorphisms, and we already know that the colimit exists in the source and `F`
preserves it, then `F` creates that colimit. -/
def createsColimitOfReflectsIsomorphismsOfPreserves {K : J ⥤ C} {F : C ⥤ D}
    [F.ReflectsIsomorphisms] [HasColimit K] [PreservesColimit K F] : CreatesColimit K F :=
  createsColimitOfReflectsIso' (isColimitOfPreserves F (colimit.isColimit _))
    ⟨⟨_, Iso.refl _⟩, colimit.isColimit _⟩

@[deprecated (since := "2025-02-01")]
noncomputable alias createsColimitOfFullyFaithfulOfPreserves :=
  createsColimitOfReflectsIsomorphismsOfPreserves

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to exhibit a
lift of a colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone c ≅ l) :
    CreatesColimit K F :=
  createsColimitOfReflectsIso' hl ⟨⟨c, i⟩, isColimitOfReflects F (IsColimit.ofIsoColimit hl i.symm)⟩

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)) :
    CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to show that
a colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt := X
      ι :=
        { app := fun j ↦ F.preimage (l.ι.app j ≫ i.inv)
          naturality := fun Y Z f ↦
            F.map_injective <| by
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocones.ext i fun j ↦ by simp)

-- Notice however that even if the isomorphism is `Iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `HasColimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [F.Full] [F.Faithful]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i

-- see Note [lower instance priority]
/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
instance (priority := 100) preservesColimit_of_createsColimit_and_hasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F where
  preserves t :=
    ⟨IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocones.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))⟩

-- see Note [lower instance priority]
/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
instance (priority := 100) preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] :
    PreservesColimitsOfShape J F where

-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesColimits_of_createsColimits_and_hasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where

/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] :
    CreatesLimit K₂ F :=
  { reflectsLimit_of_iso_diagram F h with
    lifts := fun c t ↦
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCone := (Cones.postcompose h.hom).obj (liftLimit t')
        validLift :=
          Functor.mapConePostcompose F ≪≫
            (Cones.postcompose (isoWhiskerRight h F).hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cones.ext (Iso.refl _) fun j ↦ by
                dsimp
                rw [Category.assoc, ← F.map_comp]
                simp } }

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G where
  lifts c t :=
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsLimit.mapConeEquiv h ?_).uniqueUpToIso t
        apply IsLimit.ofIsoLimit _ (liftedLimitMapsToOriginal _).symm
        apply (IsLimit.postcomposeInvEquiv _ _).symm t }
  toReflectsLimit := reflectsLimit_of_natIso _ h

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit := createsLimitOfNatIso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfNatIso h

/-- If `F` creates limits of shape `J` and `J ≌ J'`, then `F` creates limits of shape `J'`. -/
def createsLimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : CreatesLimitsOfShape J' F where
  CreatesLimit {K} :=
    { lifts c hc := by
        refine ⟨(Cones.whiskeringEquivalence e).inverse.obj
          (liftLimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cones.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedLimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
        refine ?_ ≪≫ inner ≪≫ ((Cones.whiskeringEquivalence e).unitIso.app c).symm
        exact Cones.ext (Iso.refl _)
      toReflectsLimit := have := reflectsLimitsOfShape_of_equiv e F; inferInstance }

/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] :
    CreatesColimit K₂ F :=
  { reflectsColimit_of_iso_diagram F h with
    lifts := fun c t ↦
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F :) c).symm t
      { liftedCocone := (Cocones.precompose h.inv).obj (liftColimit t')
        validLift :=
          Functor.mapCoconePrecompose F ≪≫
            (Cocones.precompose (isoWhiskerRight h F).inv).mapIso
                (liftedColimitMapsToOriginal t') ≪≫
              Cocones.ext (Iso.refl _) fun j ↦ by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G where
  lifts c t :=
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h :) c).symm t)
      validLift := by
        refine (IsColimit.mapCoconeEquiv h ?_).uniqueUpToIso t
        apply IsColimit.ofIsoColimit _ (liftedColimitMapsToOriginal _).symm
        apply (IsColimit.precomposeHomEquiv _ _).symm t }
  toReflectsColimit := reflectsColimit_of_natIso _ h

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit := createsColimitOfNatIso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfNatIso h

/-- If `F` creates colimits of shape `J` and `J ≌ J'`, then `F` creates colimits of shape `J'`. -/
def createsColimitsOfShapeOfEquiv {J' : Type w₁} [Category.{w'₁} J'] (e : J ≌ J') (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : CreatesColimitsOfShape J' F where
  CreatesColimit {K} :=
    { lifts c hc := by
        refine ⟨(Cocones.whiskeringEquivalence e).inverse.obj
          (liftColimit (hc.whiskerEquivalence e)), ?_⟩
        letI inner := (Cocones.whiskeringEquivalence (F := K ⋙ F) e).inverse.mapIso
          (liftedColimitMapsToOriginal (K := e.functor ⋙ K) (hc.whiskerEquivalence e))
        refine ?_ ≪≫ inner ≪≫ ((Cocones.whiskeringEquivalence e).unitIso.app c).symm
        exact Cocones.ext (Iso.refl _)
      toReflectsColimit := have := reflectsColimitsOfShape_of_equiv e F; inferInstance }

-- For the inhabited linter later.
/-- If F creates the limit of K, any cone lifts to a limit. -/
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t

-- For the inhabited linter later.
/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t

/-- Any cone lifts through the identity functor. -/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.hom }
  validLift := Cones.ext (Iso.refl _)

/-- The identity functor creates all limits. -/
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape :=
    { CreatesLimit := { lifts := fun c _ ↦ idLiftsCone c } }

/-- Any cocone lifts through the identity functor. -/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocones.ext (Iso.refl _)

/-- The identity functor creates all colimits. -/
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape :=
    { CreatesColimit := { lifts := fun c _ ↦ idLiftsCocone c } }

/-- Satisfy the inhabited linter -/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩

instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩

/-- Satisfy the inhabited linter -/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩

instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩

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

instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance

instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance

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

instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance

instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance

end Comp

end Creates

end CategoryTheory
