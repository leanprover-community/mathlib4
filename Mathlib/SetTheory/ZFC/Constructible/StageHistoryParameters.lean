/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalAbsolute

/-!
# Fixed parameters for constructible-stage histories

All local history rules share thirteen fixed constructible parameters.  The
remaining four coordinates are `(history, index, stage, relation)`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The evaluator constants independent of the current stage and relation:
`(varTag, appTag, empty, op0, ..., op8, omega)`. -/
def stageHistoryFixedParameters : Tuple LCarrier.{u} 13 :=
  ![
    ⟨Godel.RudimentaryTerm.varTag,
      Godel.RudimentaryTerm.varTag_mem_L⟩,
    ⟨Godel.RudimentaryTerm.appTag,
      Godel.RudimentaryTerm.appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨Godel.RudimentaryTerm.operationCode 0,
      Godel.RudimentaryTerm.operationCode_mem_L 0⟩,
    ⟨Godel.RudimentaryTerm.operationCode 1,
      Godel.RudimentaryTerm.operationCode_mem_L 1⟩,
    ⟨Godel.RudimentaryTerm.operationCode 2,
      Godel.RudimentaryTerm.operationCode_mem_L 2⟩,
    ⟨Godel.RudimentaryTerm.operationCode 3,
      Godel.RudimentaryTerm.operationCode_mem_L 3⟩,
    ⟨Godel.RudimentaryTerm.operationCode 4,
      Godel.RudimentaryTerm.operationCode_mem_L 4⟩,
    ⟨Godel.RudimentaryTerm.operationCode 5,
      Godel.RudimentaryTerm.operationCode_mem_L 5⟩,
    ⟨Godel.RudimentaryTerm.operationCode 6,
      Godel.RudimentaryTerm.operationCode_mem_L 6⟩,
    ⟨Godel.RudimentaryTerm.operationCode 7,
      Godel.RudimentaryTerm.operationCode_mem_L 7⟩,
    ⟨Godel.RudimentaryTerm.operationCode 8,
      Godel.RudimentaryTerm.operationCode_mem_L 8⟩,
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩]

@[simp]
theorem stageHistoryFixedParameters_empty :
    stageHistoryFixedParameters (2 : Fin 13) = emptyLCarrier :=
  rfl

@[simp]
theorem stageHistoryFixedParameters_last :
    stageHistoryFixedParameters (Fin.last 12) =
      (⟨Ordinal.omega0.toZFSet, omega_mem_L⟩ : LCarrier.{u}) :=
  rfl

/-- Before the final omega coordinate, the fixed history parameters are the
stack-step prefix with its leading universe coordinate removed. -/
@[simp]
theorem stageHistoryFixedParameters_init
    (U : LCarrier.{u}) (i : Fin 12) :
    stageHistoryFixedParameters i.castSucc =
      Godel.RudimentaryTerm.stackStepPrefixLAssignment U.1 U.2 i.succ := by
  fin_cases i <;> rfl

/-- Assignment layout `(fixed13, history, index, stage, relation)`. -/
def stageHistoryStateLAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc (snoc (snoc (snoc stageHistoryFixedParameters history) index)
    stage) relation

/-- The empty-set parameter, embedded into the full history-rule layout. -/
def stageHistoryEmptyIndex : Fin 17 :=
  (2 : Fin 13).castSucc.castSucc.castSucc.castSucc

@[simp]
theorem stageHistoryStateLAssignment_emptyParameter
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation
        stageHistoryEmptyIndex =
      emptyLCarrier := by
  simp only [stageHistoryStateLAssignment, stageHistoryEmptyIndex,
    snoc_castSucc, stageHistoryFixedParameters_empty]

@[simp]
theorem stageHistoryStateLAssignment_history
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (13 : Fin 17) =
      history :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_index
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (14 : Fin 17) =
      index :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_stage
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (15 : Fin 17) =
      stage :=
  rfl

@[simp]
theorem stageHistoryStateLAssignment_relation
    (history index stage relation : LCarrier.{u}) :
    stageHistoryStateLAssignment history index stage relation (16 : Fin 17) =
      relation :=
  rfl

end

end Constructible.Model
