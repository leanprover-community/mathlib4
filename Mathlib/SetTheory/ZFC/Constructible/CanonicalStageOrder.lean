/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageOrder

/-!
# Canonical external orders on constructible stages

The order on a birth layer must use the already constructed order on the
preceding stage, rather than an unrelated application of external Choice.
This file performs that well-founded recursion on the birth ordinal.

The resulting relations are still external Lean predicates.  Their
Kuratowski-pair graphs must subsequently be shown constructible; no such
internalization claim is made here.
-/

@[expose] public section

open Set

universe u

namespace Constructible

/-! ## Adding the distinguished stage generator -/

/-- Identify `Option A` with a singleton placed before `A`. -/
def optionSumEquiv (A : Type u) : Option A ≃ Unit ⊕ A where
  toFun
    | none => Sum.inl ()
    | some x => Sum.inr x
  invFun
    | Sum.inl _ => none
    | Sum.inr x => some x
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- Put the distinguished `none` generator before all ordinary generators. -/
def optionPrependRel {A : Type u} (r : A -> A -> Prop) :
    Option A -> Option A -> Prop :=
  InvImage (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r)
    (optionSumEquiv A)

theorem optionPrependRel_isWellOrder {A : Type u}
    (r : A -> A -> Prop) [IsWellOrder A r] :
    IsWellOrder (Option A) (optionPrependRel r) := by
  letI : IsWellOrder (Unit ⊕ A)
      (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r) := by
    infer_instance
  exact
    { wf := InvImage.wf (optionSumEquiv A)
        (IsWellFounded.wf :
          WellFounded
            (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r))
      trichotomous :=
        (InvImage.trichotomous
          (r := Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r)
          (optionSumEquiv A).injective).trichotomous }

/-! ## Simultaneous stage/layer recursion -/

/-- The mutually dependent canonical orders at one ordinal. -/
structure CanonicalOrderData (alpha : Ordinal.{u}) where
  stageRel : LStageCarrier alpha -> LStageCarrier alpha -> Prop
  stage_isWellOrder : IsWellOrder (LStageCarrier alpha) stageRel
  layerRel : BornAt alpha -> BornAt alpha -> Prop
  layer_isWellOrder : IsWellOrder (BornAt alpha) layerRel

/--
Recursively order `L_alpha` by its earlier birth layers, then order the new
birth layer by least rudimentary terms whose generators use that stage order.
-/
noncomputable def canonicalOrderData (alpha : Ordinal.{u}) :
    CanonicalOrderData alpha :=
  let earlierLayerRel : forall beta : Set.Iio alpha,
      BornAt beta.1 -> BornAt beta.1 -> Prop :=
    fun beta => (canonicalOrderData beta.1).layerRel
  have hEarlier : forall beta : Set.Iio alpha,
      IsWellOrder (BornAt beta.1) (earlierLayerRel beta) :=
    fun beta => (canonicalOrderData beta.1).layer_isWellOrder
  let stageRel := lStageBirthRel alpha earlierLayerRel
  have hStage : IsWellOrder (LStageCarrier alpha) stageRel :=
    lStageBirthRel_isWellOrder alpha earlierLayerRel hEarlier
  let generatorRel := optionPrependRel stageRel
  letI : IsWellOrder (Option (ZFCarrier (LStageZF alpha))) generatorRel :=
    @optionPrependRel_isWellOrder
      (ZFCarrier (LStageZF alpha)) stageRel hStage
  let layerRel := bornAtRel alpha generatorRel
  have hLayer : IsWellOrder (BornAt alpha) layerRel :=
    bornAtRel_isWellOrder alpha generatorRel
  { stageRel := stageRel
    stage_isWellOrder := hStage
    layerRel := layerRel
    layer_isWellOrder := hLayer }
termination_by alpha
decreasing_by
  all_goals exact beta.2

/-- The canonical external relation on `L_alpha`. -/
noncomputable def canonicalStageRel (alpha : Ordinal.{u}) :
    LStageCarrier alpha -> LStageCarrier alpha -> Prop :=
  (canonicalOrderData alpha).stageRel

/-- The canonical external relation on the sets born at `alpha`. -/
noncomputable def canonicalBornAtRel (alpha : Ordinal.{u}) :
    BornAt alpha -> BornAt alpha -> Prop :=
  (canonicalOrderData alpha).layerRel

theorem canonicalStageRel_isWellOrder (alpha : Ordinal.{u}) :
    IsWellOrder (LStageCarrier alpha) (canonicalStageRel alpha) :=
  (canonicalOrderData alpha).stage_isWellOrder

theorem canonicalBornAtRel_isWellOrder (alpha : Ordinal.{u}) :
    IsWellOrder (BornAt alpha) (canonicalBornAtRel alpha) :=
  (canonicalOrderData alpha).layer_isWellOrder

end Constructible
