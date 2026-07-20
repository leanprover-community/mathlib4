/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.DefinableRelationGraph
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryLeastProgramAbsolute
public import Mathlib.SetTheory.ZFC.Constructible.StageInternalOrder

/-!
# Internally represented well-orders of successor stages

Assume an actual constructible graph internally well-orders `L_alpha`.
The fixed least-successful-program formula then well-orders
`L_(alpha+1) = Def(L_alpha)`.  Full Separation turns that formula-defined
relation into an actual Kuratowski graph belonging to `L`.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

noncomputable section

/-- A constructible stage packaged as an element of `LCarrier`. -/
def stageLCarrier (alpha : Ordinal.{u}) : LCarrier.{u} :=
  ⟨LStageZF alpha, LStageZF_mem_L alpha⟩

@[simp]
theorem stageLCarrier_val (alpha : Ordinal.{u}) :
    (stageLCarrier alpha).1 = LStageZF alpha := rfl

/-- The internal carrier of the successor stage is the corresponding
Gödel-definability carrier. -/
def successorDefCarrierEquiv (alpha : Ordinal.{u}) :
    InternalCarrier (stageLCarrier (Order.succ alpha)) ≃
      Godel.DefCarrier (LStageZF alpha) where
  toFun x :=
    ⟨x.1.1, by
      simpa only [stageLCarrier, LStageZF_succ,
        Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)] using x.2⟩
  invFun x :=
    let hx : x.1 ∈ LStageZF (Order.succ alpha) := by
      simpa only [LStageZF_succ,
        Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)] using x.2
    ⟨⟨x.1, LStageZF_subset_constructibleUniverse
        (Order.succ alpha) hx⟩, hx⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp]
theorem successorDefCarrierEquiv_val (alpha : Ordinal.{u})
    (x : InternalCarrier (stageLCarrier (Order.succ alpha))) :
    (successorDefCarrierEquiv alpha x).1 = x.1.1 := rfl

/-- The formula parameters induced by a represented order on `L_alpha`. -/
def successorProgramOrderParameters (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
    (stageLCarrier alpha) relation

/-- Formula satisfaction on the successor carrier is exactly the pullback of
the successful-program order. -/
theorem successorFormulaRel_eq_invImage
    (alpha : Ordinal.{u}) (relation : LCarrier.{u}) :
    formulaRelOn
        Godel.RudimentaryTerm.leastProgramValueLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha)) =
      InvImage
        (Godel.RudimentaryTerm.successfulProgramValueRel
          (LStageZF alpha) relation.1)
        (successorDefCarrierEquiv alpha) := by
  funext x y
  apply propext
  let U := stageLCarrier alpha
  let xL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha x)
  let yL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha y)
  have hxL : x.1 = xL := by
    apply Subtype.ext
    rfl
  have hyL : y.1 = yL := by
    apply Subtype.ext
    rfl
  change
    FOFormula.Satisfies
        (fun z w : LCarrier.{u} => z.1 ∈ w.1)
        Godel.RudimentaryTerm.leastProgramValueLtFormula
        (snoc (snoc
          (successorProgramOrderParameters alpha relation) x.1) y.1) ↔
      Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1
        (successorDefCarrierEquiv alpha x)
        (successorDefCarrierEquiv alpha y)
  rw [hxL, hyL]
  exact
    Godel.RudimentaryTerm.satisfies_leastProgramValueLtFormula_lCarrier_iff_successful
        U relation (successorDefCarrierEquiv alpha x)
          (successorDefCarrierEquiv alpha y)

/-- A represented well-order on `L_alpha` makes the fixed formula a
well-order on the entire successor stage. -/
theorem successorFormulaRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (formulaRelOn
        Godel.RudimentaryTerm.leastProgramValueLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha))) := by
  rw [successorFormulaRel_eq_invImage]
  letI : IsWellOrder
      (Godel.DefCarrier (LStageZF alpha))
      (Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1) :=
    Godel.RudimentaryTerm.successfulProgramValueRel_isWellOrder_of_internal
        (stageLCarrier alpha) relation hwell
  exact
    { wf := InvImage.wf (successorDefCarrierEquiv alpha)
        (IsWellFounded.wf : WellFounded
          (Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1))
      trichotomous :=
        (InvImage.trichotomous
          (r := Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1)
          (successorDefCarrierEquiv alpha).injective).trichotomous }

/-- A well-order graph for one stage yields an actual constructible
well-order graph for its successor. -/
theorem exists_internalWellOrder_successorStage
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    ∃ nextRelation : LCarrier.{u},
      InternallyWellOrders nextRelation
        (stageLCarrier (Order.succ alpha)) := by
  exact exists_internalWellOrder_of_formula
    Godel.RudimentaryTerm.leastProgramValueLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha))
    (successorFormulaRel_isWellOrder alpha relation hwell)

/-- Conditional successor closure of internally well-ordered stages. -/
theorem stageSuccInternallyWellOrdered (alpha : Ordinal.{u})
    (hstage : StageInternallyWellOrdered alpha) :
    StageInternallyWellOrdered (Order.succ alpha) := by
  rcases hstage with ⟨relation, hrelation⟩
  have hinternal :
      InternallyWellOrders relation (stageLCarrier alpha) := by
    apply internallyWellOrders_of_stage
      (alpha := alpha) (r := relation)
    · intro x hx
      exact hx
    · exact hrelation
  rcases exists_internalWellOrder_successorStage
      alpha relation hinternal with
    ⟨nextRelation, hnext⟩
  refine ⟨nextRelation, ?_⟩
  let stageEquiv :
      LStageCarrier (Order.succ alpha) ≃
        InternalCarrier (stageLCarrier (Order.succ alpha)) :=
    Godel.RudimentaryTerm.zfCarrierInternalEquiv
      (stageLCarrier (Order.succ alpha))
  change IsWellOrder (LStageCarrier (Order.succ alpha))
    (InvImage
      (graphRelOn nextRelation (stageLCarrier (Order.succ alpha)))
      stageEquiv)
  letI : IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (graphRelOn nextRelation (stageLCarrier (Order.succ alpha))) := hnext
  exact
    { wf := InvImage.wf stageEquiv
        (IsWellFounded.wf : WellFounded
          (graphRelOn nextRelation
            (stageLCarrier (Order.succ alpha))))
      trichotomous :=
        (InvImage.trichotomous
          (r := graphRelOn nextRelation
            (stageLCarrier (Order.succ alpha)))
          stageEquiv.injective).trichotomous }

end

end Model

end Constructible
