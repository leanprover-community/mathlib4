/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph
public import Mathlib.SetTheory.ZFC.Constructible.RudimentarySuccessorExtensionOrder

/-!
# The canonical coherent successor-stage order

The successor extension formula determines an exact graph by Separation in
the constructible Cartesian square.  Unlike an existential graph witness,
this graph is a genuine function of the preceding stage and relation, which
is the form used by the transfinite recursion.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- The canonical constructible graph extending the order on `L_alpha`. -/
def canonicalSuccessorRelation (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) : LCarrier.{u} :=
  canonicalDefinableRelationGraph successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha))

/-- Object-language specification of the exact coherent successor graph.
Its layout is `(fifteen program parameters, successor domain, output)`. -/
def canonicalSuccessorOutputFormula : FOFormula 17 :=
  canonicalGraphOutputFormula successorExtensionLtFormula

theorem satisfies_canonicalSuccessorOutputFormula_iff_eq
    (alpha : Ordinal.{u}) (relation nextRelation : LCarrier.{u}) :
    FOFormula.Satisfies LMem canonicalSuccessorOutputFormula
        (snoc
          (snoc (successorProgramOrderParameters alpha relation)
            (stageLCarrier (Order.succ alpha)))
          nextRelation) ↔
      nextRelation = canonicalSuccessorRelation alpha relation := by
  simpa only [canonicalSuccessorOutputFormula,
    canonicalSuccessorRelation] using
    (satisfies_canonicalGraphOutputFormula_iff_eq
      successorExtensionLtFormula
      (successorProgramOrderParameters alpha relation)
      (stageLCarrier (Order.succ alpha)) nextRelation)

/-- For fixed predecessor data, the successor-output formula is functional. -/
theorem existsUnique_canonicalSuccessorOutputFormula
    (alpha : Ordinal.{u}) (relation : LCarrier.{u}) :
    ∃! nextRelation : LCarrier.{u},
      FOFormula.Satisfies LMem canonicalSuccessorOutputFormula
        (snoc
          (snoc (successorProgramOrderParameters alpha relation)
            (stageLCarrier (Order.succ alpha)))
          nextRelation) := by
  simpa only [canonicalSuccessorOutputFormula] using
    (existsUnique_canonicalGraphOutputFormula
      successorExtensionLtFormula
      (successorProgramOrderParameters alpha relation)
      (stageLCarrier (Order.succ alpha)))

@[simp]
theorem graphRel_canonicalSuccessorRelation_iff
    (alpha : Ordinal.{u}) (relation x y : LCarrier.{u}) :
    GraphRel (canonicalSuccessorRelation alpha relation) x y ↔
      x.1 ∈ LStageZF (Order.succ alpha) ∧
        y.1 ∈ LStageZF (Order.succ alpha) ∧
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x y) := by
  have h := graphRel_canonicalDefinableRelationGraph_iff
    successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha)) x y
  change
    GraphRel (canonicalSuccessorRelation alpha relation) x y ↔
      x.1 ∈ LStageZF (Order.succ alpha) ∧
        y.1 ∈ LStageZF (Order.succ alpha) ∧
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x y) at h
  exact h

/-- The canonical graph has no members other than the intended ordered
pairs, a stronger specification than merely agreeing through `GraphRel`. -/
@[simp]
theorem mem_canonicalSuccessorRelation_iff
    (alpha : Ordinal.{u}) (relation q : LCarrier.{u}) :
    q.1 ∈ (canonicalSuccessorRelation alpha relation).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ LStageZF (Order.succ alpha) ∧
          y.1 ∈ LStageZF (Order.succ alpha) ∧
            q.1 = ZFSet.pair x.1 y.1 ∧
              FOFormula.Satisfies LMem successorExtensionLtFormula
                (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
                  (stageLCarrier alpha) relation x y) := by
  have h := mem_canonicalDefinableRelationGraph_iff
    successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha)) q
  change
    q.1 ∈ (canonicalSuccessorRelation alpha relation).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ LStageZF (Order.succ alpha) ∧
          y.1 ∈ LStageZF (Order.succ alpha) ∧
            q.1 = ZFSet.pair x.1 y.1 ∧
              FOFormula.Satisfies LMem successorExtensionLtFormula
                (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
                  (stageLCarrier alpha) relation x y) at h
  exact h

/-- If the old graph well-orders `L_alpha`, the canonical successor graph is
the coherent extension constructed by the successor formula. -/
def canonicalSuccessorOrderExtension
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    SuccessorOrderExtension alpha relation where
  nextRelation := canonicalSuccessorRelation alpha relation
  wellOrders := by
    have heq :
        graphRelOn (canonicalSuccessorRelation alpha relation)
            (stageLCarrier (Order.succ alpha)) =
          formulaRelOn successorExtensionLtFormula
            (successorProgramOrderParameters alpha relation)
            (stageLCarrier (Order.succ alpha)) := by
      funext x y
      apply propext
      change
        GraphRel (canonicalSuccessorRelation alpha relation) x.1 y.1 ↔
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x.1 y.1)
      have hx : x.1.1 ∈ LStageZF (Order.succ alpha) := x.2
      have hy : y.1.1 ∈ LStageZF (Order.succ alpha) := y.2
      simpa only [hx, hy, true_and] using
        (graphRel_canonicalSuccessorRelation_iff
          alpha relation x.1 y.1)
    rw [InternallyWellOrders, heq]
    exact successorExtensionFormulaRel_isWellOrder alpha relation hwell
  supported := by
    intro x y hxy
    have hsupported := (graphRel_canonicalSuccessorRelation_iff
      alpha relation x y).mp hxy
    exact ⟨hsupported.1, hsupported.2.1⟩
  agreesOnOld := by
    intro x y hx hy
    have hxSucc : x.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hx
    have hySucc : y.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hy
    rw [graphRel_canonicalSuccessorRelation_iff]
    simp only [hxSucc, hySucc, true_and]
    change
      FOFormula.Satisfies LMem successorExtensionLtFormula
          (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
            (stageLCarrier alpha) relation x y) ↔
        GraphRel relation x y
    rw [satisfies_successorExtensionLtFormula]
    simp only [stageLCarrier_val, hx, hy, true_and, not_true,
      and_false, false_and, or_false]
  oldIsInitial := by
    intro x y hx hySucc hyx
    have hformula :=
      (graphRel_canonicalSuccessorRelation_iff
        alpha relation y x).mp hyx |>.2.2
    rcases (satisfies_successorExtensionLtFormula
        (stageLCarrier alpha) relation y x).mp hformula with
      hold | hold | hnew
    · exact hold.1
    · exact hold.1
    · exact (hnew.2.1 hx).elim

@[simp]
theorem canonicalSuccessorOrderExtension_nextRelation
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    (canonicalSuccessorOrderExtension alpha relation hwell).nextRelation =
      canonicalSuccessorRelation alpha relation :=
  rfl

end

end Constructible.Model
