/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryParameters
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryEntry
public import Mathlib.SetTheory.ZFC.Constructible.SuccessorStageStateFormula
public import Mathlib.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula

/-!
# The successor-state clause for constructible-stage histories

The outer layout is `(fixed13, history, index, stage, relation)`.  Three
existential witnesses append `(predecessorIndex, predecessorStage,
predecessorRelation)`.  The existing deterministic successor-state formula
is then renamed into this combined context.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- Select
`(predecessorStage, fixed13, predecessorRelation, stage, relation)`
from the twenty-coordinate successor-history witness layout. -/
def historySuccessorStepRename : Fin 17 → Fin 20 :=
  Fin.lastCases
    (16 : Fin 20)
    (fun i15 => Fin.lastCases
      (15 : Fin 20)
      (fun i14 => Fin.lastCases
        (19 : Fin 20)
        (fun i13 => Fin.cases
          (18 : Fin 20)
          (fun j => Fin.castLE (by decide) j)
          i13)
        i14)
      i15)

/-- Assignment after adjoining the three predecessor witnesses. -/
def historySuccessorWitnessAssignment
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    Tuple LCarrier.{u} 20 :=
  snoc
    (snoc
      (snoc (stageHistoryStateLAssignment history index stage relation)
        predecessorIndex)
      predecessorStage)
    predecessorRelation

private lemma historySuccessorWitnessAssignment_expanded_eq
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    snoc
        (snoc
          (snoc (stageHistoryStateLAssignment history index stage relation)
            predecessorIndex)
          predecessorStage)
        predecessorRelation =
      historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation := by
  rfl

@[simp] private lemma historySuccessorWitness_history
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (13 : Fin 20) =
      history := by
  rw [show (13 : Fin 20) =
      (13 : Fin 17).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc,
    stageHistoryStateLAssignment_history]

@[simp] private lemma historySuccessorWitness_index
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (14 : Fin 20) =
      index := by
  rw [show (14 : Fin 20) =
      (14 : Fin 17).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc,
    stageHistoryStateLAssignment_index]

@[simp] private lemma historySuccessorWitness_predecessorIndex
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (17 : Fin 20) =
      predecessorIndex := by
  rw [show (17 : Fin 20) = (Fin.last 17).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc, snoc_last]

@[simp] private lemma historySuccessorWitness_predecessorStageProjection
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (18 : Fin 20) =
      predecessorStage := by
  rw [show (18 : Fin 20) = (Fin.last 18).castSucc by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_castSucc, snoc_last]

@[simp] private lemma historySuccessorWitness_predecessorRelation
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment history index stage relation
        predecessorIndex predecessorStage predecessorRelation (19 : Fin 20) =
      predecessorRelation := by
  rw [show (19 : Fin 20) = Fin.last 19 by
    apply Fin.ext
    rfl]
  simp only [historySuccessorWitnessAssignment, snoc_last]

private lemma insert_self_eq_union_singleton (x : ZFSet.{u}) :
    insert x x = x ∪ {x} := by
  rw [ZFSet.insert_eq]
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_union, or_comm]

private lemma historySuccessorWitness_fixed
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation
          i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [historySuccessorWitnessAssignment,
    stageHistoryStateLAssignment, snoc_castSucc]

private lemma historySuccessorWitness_fixed_castLE
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact historySuccessorWitness_fixed history index stage relation
    predecessorIndex predecessorStage predecessorRelation i

private lemma successorStageState_fixedParameters
    (predecessorStage predecessorRelation stage relation : LCarrier.{u})
    (i : Fin 13) :
    successorStageStateLAssignment
        predecessorStage predecessorRelation stage relation
          i.succ.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      snoc_castSucc, stageHistoryFixedParameters_last,
      Fin.succ_last, snoc_last]
  · rw [stageHistoryFixedParameters_init predecessorStage k]
    simp only [successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      snoc_castSucc, Fin.succ_castSucc]

private lemma historySuccessor_relation_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (16 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (16 : Fin 17) := by
  rfl

private lemma historySuccessor_stage_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (15 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (15 : Fin 17) := by
  rfl

private lemma historySuccessor_predecessorRelation_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (19 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (14 : Fin 17) := by
  rfl

private lemma historySuccessorWitness_predecessorStage
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (18 : Fin 20) = predecessorStage := by
  rfl

private lemma successorStageState_to_parameters
    (predecessorStage predecessorRelation stage relation : LCarrier.{u})
    (i : Fin 15) :
    successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation i.castSucc.castSucc =
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        predecessorStage predecessorRelation i := by
  simp only [successorStageStateLAssignment, snoc_castSucc]

private lemma leastParameters_to_stackPrefix
    (predecessorStage predecessorRelation : LCarrier.{u}) (i : Fin 13) :
    Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        predecessorStage predecessorRelation i.castSucc.castSucc =
      Godel.RudimentaryTerm.stackStepPrefixLAssignment
        predecessorStage.1 predecessorStage.2 i := by
  simp only [Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
    snoc_castSucc]

private lemma stackStepPrefix_zero (predecessorStage : LCarrier.{u}) :
    Godel.RudimentaryTerm.stackStepPrefixLAssignment
        predecessorStage.1 predecessorStage.2 (0 : Fin 13) =
      predecessorStage := by
  apply Subtype.ext
  have h := congrFun
    (Godel.RudimentaryTerm.stackStepPrefixLAssignment_val
      predecessorStage.1 predecessorStage.2) (0 : Fin 13)
  exact h

private lemma successorStageState_predecessorStage
    (predecessorStage predecessorRelation stage relation : LCarrier.{u}) :
    successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (0 : Fin 17) = predecessorStage := by
  exact (successorStageState_to_parameters predecessorStage
    predecessorRelation stage relation ((0 : Fin 13).castSucc.castSucc)).trans
    ((leastParameters_to_stackPrefix predecessorStage predecessorRelation
      (0 : Fin 13)).trans (stackStepPrefix_zero predecessorStage))

private lemma historySuccessor_predecessorStage_coordinate
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    historySuccessorWitnessAssignment
        history index stage relation predecessorIndex predecessorStage
          predecessorRelation (18 : Fin 20) =
      successorStageStateLAssignment predecessorStage predecessorRelation
        stage relation (0 : Fin 17) :=
  (historySuccessorWitness_predecessorStage history index stage relation
    predecessorIndex predecessorStage predecessorRelation).trans
    (successorStageState_predecessorStage predecessorStage
      predecessorRelation stage relation).symm

private lemma historySuccessorStepRename_fixed (j : Fin 13) :
    historySuccessorStepRename j.succ.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) j := by
  simp only [historySuccessorStepRename,
    Fin.lastCases_castSucc, Fin.cases_succ]

theorem comp_historySuccessorStepRename
    (history index stage relation predecessorIndex predecessorStage
      predecessorRelation : LCarrier.{u}) :
    (fun i => historySuccessorWitnessAssignment
      history index stage relation predecessorIndex predecessorStage
        predecessorRelation (historySuccessorStepRename i)) =
      successorStageStateLAssignment
        predecessorStage predecessorRelation stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · exact historySuccessor_relation_coordinate history index stage relation
      predecessorIndex predecessorStage predecessorRelation
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · exact historySuccessor_stage_coordinate history index stage relation
        predecessorIndex predecessorStage predecessorRelation
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · exact historySuccessor_predecessorRelation_coordinate history index
          stage relation predecessorIndex predecessorStage predecessorRelation
      · refine Fin.cases ?_ (fun j => ?_) i13
        · exact historySuccessor_predecessorStage_coordinate history index
            stage relation predecessorIndex predecessorStage predecessorRelation
        · rw [historySuccessorStepRename_fixed]
          exact (historySuccessorWitness_fixed_castLE history index stage
            relation predecessorIndex predecessorStage predecessorRelation j).trans
            (successorStageState_fixedParameters predecessorStage
              predecessorRelation stage relation j).symm

/-- The local recursion rule at a successor index. -/
def historySuccessorStateFormula : FOFormula 17 :=
  .ex (.ex (.ex
    (.conj
      (Delta0Formula.successorFOAt (14 : Fin 20) (17 : Fin 20))
      (.conj
        (historyEntryAt
          (13 : Fin 20) (17 : Fin 20) (18 : Fin 20) (19 : Fin 20))
        (FOFormula.rename historySuccessorStepRename
          successorStageStateFormula)))))

@[simp]
theorem satisfies_historySuccessorStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historySuccessorStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessorIndex predecessorStage predecessorRelation :
          LCarrier.{u},
        index.1 = predecessorIndex.1 ∪ {predecessorIndex.1} ∧
          HistoryEntry history predecessorIndex
            predecessorStage predecessorRelation ∧
          FOFormula.Satisfies LMem successorStageStateFormula
            (successorStageStateLAssignment
              predecessorStage predecessorRelation stage relation) := by
  simp only [historySuccessorStateFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_historyEntryAt_iff, HistoryEntry,
    FOFormula.satisfies_rename,
    historySuccessorWitnessAssignment_expanded_eq,
    comp_historySuccessorStepRename,
    historySuccessorWitness_history, historySuccessorWitness_index,
    historySuccessorWitness_predecessorIndex,
    historySuccessorWitness_predecessorStageProjection,
    historySuccessorWitness_predecessorRelation,
    insert_self_eq_union_singleton]

/-- Fully normalized semantics of the successor-history rule. -/
@[simp]
theorem satisfies_historySuccessorStateFormula_iff_outputs
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historySuccessorStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessorIndex predecessorStage predecessorRelation :
          LCarrier.{u},
        index.1 = predecessorIndex.1 ∪ {predecessorIndex.1} ∧
          HistoryEntry history predecessorIndex
            predecessorStage predecessorRelation ∧
          stage.1 = Godel.godelDef predecessorStage.1 ∧
          relation = canonicalSuccessorStateRelation
            predecessorStage predecessorRelation stage := by
  rw [satisfies_historySuccessorStateFormula]
  apply exists_congr
  intro predecessorIndex
  apply exists_congr
  intro predecessorStage
  apply exists_congr
  intro predecessorRelation
  simp only [satisfies_successorStageStateFormula_iff]

end

end Constructible.Model
