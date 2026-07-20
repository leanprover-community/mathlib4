/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryBaseFormula
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryLimitFormula
public import Mathlib.SetTheory.ZFC.Constructible.StageHistorySuccessorFormula
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryFunctionality

/-!
# A fixed validity formula for constructible-stage histories

The local rule combines the zero, successor, and nonzero-limit clauses in the
shared seventeen-coordinate layout

`(fixed13, history, index, stage, relation)`.

The global validity formula has layout `(fixed13, history, bound)`.  It says
that every index at most `bound` has exactly one history entry, and that its
stage and relation coordinates obey the appropriate local rule.  As in the
indexed-sequence validity predicate, irrelevant extra members of the history
set are permitted; every lookup uses only the total functional part below the
stated bound.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The unified local rule -/

/-- Select `(history, index, stage, relation)` from the shared seventeen-
coordinate history-state layout. -/
def historyLimitStateRename : Fin 4 → Fin 17 :=
  fun i => Fin.natAdd 13 i

theorem comp_historyLimitStateRename
    (history index stage relation : LCarrier.{u}) :
    (fun i =>
      stageHistoryStateLAssignment history index stage relation
        (historyLimitStateRename i)) =
      historyStateAssignment history index stage relation := by
  funext i
  fin_cases i <;> rfl

/-- The current index is the empty set. -/
def historyIndexIsZeroFormula : FOFormula 17 :=
  .eq (14 : Fin 17) stageHistoryEmptyIndex

/-- The current index has a von Neumann predecessor. -/
def historyIndexHasPredecessorFormula : FOFormula 17 :=
  .ex (Delta0Formula.successorFOAt (14 : Fin 18) (17 : Fin 18))

private lemma historyIndexPredecessorAssignment_index
    (history index stage relation predecessor : LCarrier.{u}) :
    snoc (stageHistoryStateLAssignment history index stage relation) predecessor
        (14 : Fin 18) = index := by
  rw [show (14 : Fin 18) = (14 : Fin 17).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageHistoryStateLAssignment_index]

private lemma historyIndexPredecessorAssignment_predecessor
    (history index stage relation predecessor : LCarrier.{u}) :
    snoc (stageHistoryStateLAssignment history index stage relation) predecessor
        (17 : Fin 18) = predecessor := by
  rw [show (17 : Fin 18) = Fin.last 17 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

@[simp]
theorem satisfies_historyIndexIsZeroFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyIndexIsZeroFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      index = emptyLCarrier := by
  simp only [historyIndexIsZeroFormula, FOFormula.Satisfies,
    stageHistoryStateLAssignment_index,
    stageHistoryStateLAssignment_emptyParameter]

@[simp]
theorem satisfies_historyIndexHasPredecessorFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyIndexHasPredecessorFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1 := by
  simp only [historyIndexHasPredecessorFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier]
  apply exists_congr
  intro predecessor
  rw [historyIndexPredecessorAssignment_index,
    historyIndexPredecessorAssignment_predecessor]

/-- The exact external condition expressed by the limit-state formula. -/
def HistoryLimitState
    (history index stage relation : LCarrier.{u}) : Prop :=
  (∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
        ∃ earlierStage earlierRelation : LCarrier.{u},
          HistoryEntry history earlierIndex earlierStage earlierRelation ∧
            z.1 ∈ earlierStage.1) ∧
  (∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
    ∃ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 ∧
        ∃ earlierStage earlierRelation : LCarrier.{u},
          HistoryEntry history earlierIndex earlierStage earlierRelation ∧
            z.1 ∈ earlierRelation.1)

@[simp]
theorem satisfies_renamed_historyLimitStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (FOFormula.rename historyLimitStateRename historyLimitStateFormula)
        (stageHistoryStateLAssignment history index stage relation) ↔
      HistoryLimitState history index stage relation := by
  simp only [FOFormula.satisfies_rename, comp_historyLimitStateRename,
    satisfies_historyLimitStateFormula, HistoryLimitState]

/-- The exact external condition expressed by the unified local rule. -/
def HistoryLocalState
    (history index stage relation : LCarrier.{u}) : Prop :=
  (index = emptyLCarrier ∧
    stage = emptyLCarrier ∧ relation = emptyLCarrier) ∨
  (∃ predecessorIndex predecessorStage predecessorRelation : LCarrier.{u},
    index.1 = insert predecessorIndex.1 predecessorIndex.1 ∧
      HistoryEntry history predecessorIndex
        predecessorStage predecessorRelation ∧
      stage.1 = Godel.godelDef predecessorStage.1 ∧
      relation = canonicalSuccessorStateRelation
        predecessorStage predecessorRelation stage) ∨
  (index ≠ emptyLCarrier ∧
    ¬ ∃ predecessor : LCarrier.{u},
      index.1 = insert predecessor.1 predecessor.1) ∧
        HistoryLimitState history index stage relation

private lemma insert_self_eq_union_singleton (x : ZFSet.{u}) :
    insert x x = x ∪ {x} := by
  rw [ZFSet.insert_eq]
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_union, or_comm]

/-- Zero, successor, or guarded nonzero-limit recursion at one history entry.
The guards make the three cases disjoint whenever the index is an ordinal. -/
def historyLocalStateFormula : FOFormula 17 :=
  .disj
    historyBaseStateFormula
    (.disj
      historySuccessorStateFormula
      (.conj
        (.conj
          (.neg historyIndexIsZeroFormula)
          (.neg historyIndexHasPredecessorFormula))
        (FOFormula.rename historyLimitStateRename
          historyLimitStateFormula)))

@[simp]
theorem satisfies_historyLocalStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyLocalStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      HistoryLocalState history index stage relation := by
  simp only [historyLocalStateFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_historyBaseStateFormula,
    satisfies_historySuccessorStateFormula_iff_outputs,
    satisfies_historyIndexIsZeroFormula,
    satisfies_historyIndexHasPredecessorFormula,
    satisfies_renamed_historyLimitStateFormula, HistoryLocalState,
    insert_self_eq_union_singleton]

/-! ## Total functional validity through a bound -/

/-- Assignment layout `(fixed13, history, bound)`. -/
def validStageHistoryLAssignment
    (history bound : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters history) bound

/-- Assignment after adjoining `(index, stage, relation)`. -/
def validStageHistoryWitnessLAssignment
    (history bound index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 18 :=
  snoc
    (snoc
      (snoc (validStageHistoryLAssignment history bound) index)
      stage)
      relation

private lemma validHistoryLocal_fixed
    (history bound index stage relation : LCarrier.{u}) (i : Fin 13) :
      validStageHistoryWitnessLAssignment history bound index stage relation
        (Fin.castLE (by decide) i) =
      stageHistoryStateLAssignment history index stage relation
        i.castSucc.castSucc.castSucc.castSucc := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment,
    validStageHistoryLAssignment, stageHistoryStateLAssignment,
    snoc_castSucc]

private lemma validHistoryLocal_history
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (13 : Fin 18) =
      stageHistoryStateLAssignment history index stage relation (13 : Fin 17) := by
  rfl

private lemma validHistoryWitnessAssignment_expanded_eq
    (history bound index stage relation : LCarrier.{u}) :
    snoc (snoc (snoc (validStageHistoryLAssignment history bound) index) stage)
        relation =
      validStageHistoryWitnessLAssignment history bound index stage relation := by
  rfl

@[simp] private lemma validHistoryWitness_history
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (13 : Fin 18) = history := by
  rw [show (13 : Fin 18) =
      (13 : Fin 15).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment,
    validStageHistoryLAssignment, snoc_castSucc]
  rw [show (13 : Fin 15) = (Fin.last 13).castSucc by
    apply Fin.ext
    rfl]
  rw [snoc_castSucc]
  exact snoc_last _ _

@[simp] private lemma validHistoryWitness_index
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (15 : Fin 18) = index := by
  rw [show (15 : Fin 18) =
      (Fin.last 15).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment, snoc_castSucc]
  exact snoc_last _ _

@[simp] private lemma validHistoryWitness_stage
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (16 : Fin 18) = stage := by
  rw [show (16 : Fin 18) = (16 : Fin 17).castSucc by
    apply Fin.ext
    rfl]
  simp only [validStageHistoryWitnessLAssignment, snoc_castSucc]
  exact snoc_last _ _

@[simp] private lemma validHistoryWitness_relation
    (history bound index stage relation : LCarrier.{u}) :
    validStageHistoryWitnessLAssignment history bound index stage relation
        (17 : Fin 18) = relation := by
  rw [show (17 : Fin 18) = Fin.last 17 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- Select `(history, index, stage, relation)` from a global validity
witness assignment. -/
def validHistoryUniqueRename : Fin 4 → Fin 18 :=
  ![(13 : Fin 18), (15 : Fin 18), (16 : Fin 18), (17 : Fin 18)]

/-- Drop the bound coordinate from a global validity witness assignment,
obtaining the shared local-rule layout. -/
def validHistoryLocalRename : Fin 17 → Fin 18 :=
  Fin.lastCases
    (17 : Fin 18)
    (fun i15 => Fin.lastCases
      (16 : Fin 18)
      (fun i14 => Fin.lastCases
        (15 : Fin 18)
        (fun i13 => Fin.castLE (by decide) i13)
        i14)
      i15)

theorem comp_validHistoryUniqueRename
    (history bound index stage relation : LCarrier.{u}) :
    (fun i => validStageHistoryWitnessLAssignment
      history bound index stage relation (validHistoryUniqueRename i)) =
      ![history, index, stage, relation] := by
  funext i
  fin_cases i <;> rfl

theorem comp_validHistoryLocalRename
    (history bound index stage relation : LCarrier.{u}) :
    (fun i => validStageHistoryWitnessLAssignment
      history bound index stage relation (validHistoryLocalRename i)) =
      stageHistoryStateLAssignment history index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · refine Fin.lastCases ?_ (fun j => ?_) i13
        · exact validHistoryLocal_history history bound index stage relation
        · simp only [validHistoryLocalRename, Fin.lastCases_castSucc]
          have hcast :
              (Fin.castLE (by decide) j.castSucc : Fin 18) =
                Fin.castLE (by decide) j := by
            apply Fin.ext
            rfl
          rw [hcast]
          exact validHistoryLocal_fixed history bound index stage relation j

@[simp] private lemma validStageHistoryAssignment_bound
    (history bound : LCarrier.{u}) :
    validStageHistoryLAssignment history bound (14 : Fin 15) = bound := by
  rw [show (14 : Fin 15) = Fin.last 14 by
    apply Fin.ext
    rfl]
  rw [validStageHistoryLAssignment]
  exact snoc_last _ _

@[simp] private lemma validStageHistoryWitness_bound
    (history bound index : LCarrier.{u}) :
    snoc (validStageHistoryLAssignment history bound) index (14 : Fin 16) =
      bound := by
  rw [show (14 : Fin 16) = (Fin.last 14).castSucc by
    apply Fin.ext
    rfl]
  rw [snoc_castSucc]
  exact validStageHistoryAssignment_bound history bound

@[simp] private lemma validStageHistoryWitness_index
    (history bound index : LCarrier.{u}) :
    snoc (validStageHistoryLAssignment history bound) index (15 : Fin 16) =
      index := by
  rw [show (15 : Fin 16) = Fin.last 15 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- At the selected index there is a unique history state and that state
obeys the unified local recursion rule.  The layout before choosing the two
outputs is `(fixed13, history, bound, index)`. -/
def validStageHistoryIndexBody : FOFormula 16 :=
  .ex (.ex
    (.conj
      (historyEntryAt
        (13 : Fin 18) (15 : Fin 18) (16 : Fin 18) (17 : Fin 18))
      (.conj
        (FOFormula.rename validHistoryUniqueRename
          historyStateUniqueBody)
        (FOFormula.rename validHistoryLocalRename
          historyLocalStateFormula))))

/-- A history is total, functional, and locally correct at every index at
most the supplied bound. -/
def validStageHistoryFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.imp
      (FOFormula.disj
        (.mem (15 : Fin 16) (14 : Fin 16))
        (.eq (15 : Fin 16) (14 : Fin 16)))
      validStageHistoryIndexBody)

/-- Exact semantics of the body at one bounded index. -/
@[simp]
theorem satisfies_validStageHistoryIndexBody
    (history bound index : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryIndexBody
        (snoc (validStageHistoryLAssignment history bound) index) ↔
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
        (∀ otherStage otherRelation : LCarrier.{u},
          HistoryEntry history index otherStage otherRelation →
            otherStage = stage ∧ otherRelation = relation) ∧
        HistoryLocalState history index stage relation := by
  simp only [validStageHistoryIndexBody, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry,
    FOFormula.satisfies_rename,
    validHistoryWitnessAssignment_expanded_eq,
    comp_validHistoryUniqueRename, comp_validHistoryLocalRename,
    validHistoryWitness_history, validHistoryWitness_index,
    validHistoryWitness_stage, validHistoryWitness_relation,
    satisfies_historyStateUniqueBody, satisfies_historyLocalStateFormula]

/-- Exact `LCarrier` semantics of bounded valid-stage histories.  No
ordinalhood assumption on `bound` is hidden in this statement. -/
@[simp]
theorem satisfies_validStageHistoryFormula
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryFormula
        (validStageHistoryLAssignment history bound) ↔
      ∀ index : LCarrier.{u},
        (index.1 ∈ bound.1 ∨ index = bound) →
          ∃ stage relation : LCarrier.{u},
            HistoryEntry history index stage relation ∧
            (∀ otherStage otherRelation : LCarrier.{u},
              HistoryEntry history index otherStage otherRelation →
                otherStage = stage ∧ otherRelation = relation) ∧
            HistoryLocalState history index stage relation := by
  simp only [validStageHistoryFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_validStageHistoryIndexBody,
    validStageHistoryWitness_bound, validStageHistoryWitness_index]

/-- Named semantic predicate for a history which is total, functional, and
locally correct through `bound`. -/
def ValidStageHistory (history bound : LCarrier.{u}) : Prop :=
  ∀ index : LCarrier.{u},
    (index.1 ∈ bound.1 ∨ index = bound) →
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
        (∀ otherStage otherRelation : LCarrier.{u},
          HistoryEntry history index otherStage otherRelation →
            otherStage = stage ∧ otherRelation = relation) ∧
        HistoryLocalState history index stage relation

@[simp]
theorem satisfies_validStageHistoryFormula_iff
    (history bound : LCarrier.{u}) :
    FOFormula.Satisfies LMem validStageHistoryFormula
        (validStageHistoryLAssignment history bound) ↔
      ValidStageHistory history bound := by
  rw [satisfies_validStageHistoryFormula]
  rfl

end

end Constructible.Model
