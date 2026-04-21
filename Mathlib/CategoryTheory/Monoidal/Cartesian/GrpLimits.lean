/-
Copyright (c) 2026 Thomas Browning, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.ShrinkYoneda
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Limits in `Grp C`

We show that `Grp C` has limits.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Functor Grp Limits MonObj

universe w v

variable {C : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  {J : Type w} [Category J] [HasLimitsOfShape J C]

instance : PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C)) :=
  have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))

/-- An auxiliary construction in order to prove that `Grp.forget₂Mon` creates limits. -/
noncomputable def Grp.limitAux (F : J ⥤ Grp C) : Grp C where
  X := (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f ↦
    letI e := Shrink.mulEquiv.symm.trans <| Iso.monCatIsoToMulEquiv <|
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).symm
    letI := (limit (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).str
    ((invertibleOfGroup (e f)).map e.symm).copy f (e.symm_apply_apply f).symm

noncomputable instance : CreatesLimitsOfShape J (forget₂Mon C) where
  CreatesLimit {F} := createsLimitOfFullyFaithfulOfIso (limitAux F) (.refl (limitAux F).toMon)

noncomputable instance : CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs <| CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)

instance : HasLimitsOfShape J (Grp C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)

end CategoryTheory
