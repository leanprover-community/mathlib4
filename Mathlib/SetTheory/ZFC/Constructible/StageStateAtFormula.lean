/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.ValidStageHistoryFormula
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryOrdinal

/-!
# Fixed output formulas for constructible-stage recursion

The formulas in this file hide a valid history witness and expose the forms
needed by Replacement.  Their thirteen leading coordinates are always the
fixed evaluator parameters.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## A stage/relation state at one index -/

/-- Layout `(fixed13, index, stage, relation)`. -/
def stageStateAtLAssignment
    (index stage relation : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc (snoc stageHistoryFixedParameters index) stage) relation

/-- After adjoining the hidden history witness. -/
def stageStateAtWitnessLAssignment
    (index stage relation history : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc (stageStateAtLAssignment index stage relation) history

private lemma stageStateAtWitnessAssignment_expanded_eq
    (index stage relation history : LCarrier.{u}) :
    snoc (stageStateAtLAssignment index stage relation) history =
      stageStateAtWitnessLAssignment index stage relation history := by
  rfl

@[simp] private lemma stageStateAtWitness_index
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (13 : Fin 17) = index := by
  rw [show (13 : Fin 17) = (13 : Fin 16).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp] private lemma stageStateAtWitness_stage
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (14 : Fin 17) = stage := by
  rw [show (14 : Fin 17) = (14 : Fin 16).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp] private lemma stageStateAtWitness_relation
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (15 : Fin 17) = relation := by
  rw [show (15 : Fin 17) = (Fin.last 15).castSucc by
    apply Fin.ext
    rfl]
  simp only [stageStateAtWitnessLAssignment, snoc_castSucc,
    stageStateAtLAssignment]
  exact snoc_last _ _

@[simp] private lemma stageStateAtWitness_history
    (index stage relation history : LCarrier.{u}) :
    stageStateAtWitnessLAssignment index stage relation history
        (16 : Fin 17) = history := by
  rw [show (16 : Fin 17) = Fin.last 16 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

/-- Select `(fixed13, history, bound)` from the hidden-history layout. -/
def stageStateAtValidHistoryRename : Fin 15 → Fin 17 :=
  Fin.lastCases
    (13 : Fin 17)
    (fun i13 => Fin.lastCases
      (16 : Fin 17)
      (fun i12 => Fin.castLE (by decide) i12)
      i13)

private lemma stageStateAtValidHistory_fixed
    (index stage relation history : LCarrier.{u}) (i : Fin 13) :
    stageStateAtWitnessLAssignment index stage relation history
        i.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageStateAtWitnessLAssignment, stageStateAtLAssignment,
    snoc_castSucc]

private lemma stageStateAtValidHistory_fixed_castLE
    (index stage relation history : LCarrier.{u}) (i : Fin 13) :
    stageStateAtWitnessLAssignment index stage relation history
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact stageStateAtValidHistory_fixed index stage relation history i

private lemma stageStateAtValidHistoryRename_fixed (i : Fin 13) :
    stageStateAtValidHistoryRename i.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageStateAtValidHistoryRename, Fin.lastCases_castSucc]

theorem comp_stageStateAtValidHistoryRename
    (index stage relation history : LCarrier.{u}) :
    (fun i => stageStateAtWitnessLAssignment index stage relation history
      (stageStateAtValidHistoryRename i)) =
      validStageHistoryLAssignment history index := by
  funext i
  refine Fin.lastCases ?_ (fun i13 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i12 => ?_) i13
    · rfl
    · rw [stageStateAtValidHistoryRename_fixed,
        stageStateAtValidHistory_fixed_castLE]
      simp only [validStageHistoryLAssignment, snoc_castSucc]

/-- There is a valid history through `index` containing the stated output. -/
def StageStateAt
    (index stage relation : LCarrier.{u}) : Prop :=
  ∃ history : LCarrier.{u},
    ValidStageHistory history index ∧
      HistoryEntry history index stage relation

/-- A fixed formula defining the pair of state outputs at one index. -/
def stageStateAtFormula : FOFormula 16 :=
  .ex (.conj
    (FOFormula.rename stageStateAtValidHistoryRename
      validStageHistoryFormula)
    (historyEntryAt
      (16 : Fin 17) (13 : Fin 17) (14 : Fin 17) (15 : Fin 17)))

@[simp]
theorem satisfies_stageStateAtFormula
    (index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageStateAtFormula
        (stageStateAtLAssignment index stage relation) ↔
      StageStateAt index stage relation := by
  simp only [stageStateAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    stageStateAtWitnessAssignment_expanded_eq,
    comp_stageStateAtValidHistoryRename,
    satisfies_validStageHistoryFormula_iff,
    satisfies_historyEntryAt_iff, StageStateAt, HistoryEntry,
    stageStateAtWitness_index, stageStateAtWitness_stage,
    stageStateAtWitness_relation, stageStateAtWitness_history]

/-! ## A relation-only output for Replacement -/

/-- Layout `(fixed13, index, relation)`. -/
def stageRelationAtLAssignment
    (index relation : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) relation

private lemma stageRelationAt_fixed
    (index relation : LCarrier.{u}) (i : Fin 13) :
    stageRelationAtLAssignment index relation i.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageRelationAtLAssignment, snoc_castSucc]

private lemma stageRelationAt_fixed_castLE
    (index relation : LCarrier.{u}) (i : Fin 13) :
    stageRelationAtLAssignment index relation (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i = i.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact stageRelationAt_fixed index relation i

private lemma stageRelationWitness_fixed_castLE
    (index relation stage : LCarrier.{u}) (i : Fin 13) :
    snoc (stageRelationAtLAssignment index relation) stage
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageRelationAt_fixed]

/-- Reorder the two output coordinates after binding the hidden stage. -/
def stageRelationAtRename : Fin 16 → Fin 16 :=
  Fin.lastCases
    (14 : Fin 16)
    (fun i14 => Fin.lastCases
      (15 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

private lemma stageRelationAtRename_fixed (i : Fin 13) :
    stageRelationAtRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageRelationAtRename, Fin.lastCases_castSucc]
  apply Fin.ext
  rfl

theorem comp_stageRelationAtRename
    (index relation stage : LCarrier.{u}) :
    (fun i => snoc (stageRelationAtLAssignment index relation) stage
      (stageRelationAtRename i)) =
      stageStateAtLAssignment index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · rw [stageRelationAtRename_fixed,
          stageRelationWitness_fixed_castLE]
        simp only [stageStateAtLAssignment, snoc_castSucc]

/-- The relation coordinate of the unique state at an index. -/
def StageRelationAt (index relation : LCarrier.{u}) : Prop :=
  ∃ stage : LCarrier.{u}, StageStateAt index stage relation

/-- Replacement-ready formula whose input is `index` and output is the
relation graph. -/
def stageRelationAtFormula : FOFormula 15 :=
  .ex (FOFormula.rename stageRelationAtRename stageStateAtFormula)

@[simp]
theorem satisfies_stageRelationAtFormula
    (index relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageRelationAtFormula
        (stageRelationAtLAssignment index relation) ↔
      StageRelationAt index relation := by
  simp only [stageRelationAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, comp_stageRelationAtRename,
    satisfies_stageStateAtFormula, StageRelationAt]

/-! ## A canonical triple output for Replacement -/

/-- Layout `(fixed13, index, entry)`. -/
def stageEntryAtLAssignment
    (index entry : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  snoc (snoc stageHistoryFixedParameters index) entry

@[simp, nolint simpNF] private lemma stageEntryWitness_index
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (13 : Fin 17) = index := by
  rw [show (13 : Fin 17) = (13 : Fin 15).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageEntryAtLAssignment]
  rw [show (13 : Fin 15) = (Fin.last 13).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, snoc_last]

@[simp, nolint simpNF] private lemma stageEntryWitness_entry
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (14 : Fin 17) = entry := by
  rw [show (14 : Fin 17) = (Fin.last 14).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, stageEntryAtLAssignment, snoc_last]

@[simp, nolint simpNF] private lemma stageEntryWitness_stage
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (15 : Fin 17) = stage := by
  rw [show (15 : Fin 17) = (Fin.last 15).castSucc by
    apply Fin.ext
    rfl]
  simp only [snoc_castSucc, snoc_last]

@[simp, nolint simpNF] private lemma stageEntryWitness_relation
    (index entry stage relation : LCarrier.{u}) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (16 : Fin 17) = relation := by
  rw [show (16 : Fin 17) = Fin.last 16 by
    apply Fin.ext
    rfl]
  exact snoc_last _ _

private lemma stageEntryState_fixed
    (index entry stage relation : LCarrier.{u}) (i : Fin 13) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        i.castSucc.castSucc.castSucc.castSucc =
      stageHistoryFixedParameters i := by
  simp only [stageEntryAtLAssignment, snoc_castSucc]

private lemma stageEntryState_fixed_castLE
    (index entry stage relation : LCarrier.{u}) (i : Fin 13) :
    snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
        (Fin.castLE (by decide) i) =
      stageHistoryFixedParameters i := by
  rw [show Fin.castLE (by decide) i =
      i.castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  exact stageEntryState_fixed index entry stage relation i

/-- Select `(fixed13, index, stage, relation)` after binding both state
coordinates behind the entry output. -/
def stageEntryStateRename : Fin 16 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

private lemma stageEntryStateRename_fixed (i : Fin 13) :
    stageEntryStateRename i.castSucc.castSucc.castSucc =
      Fin.castLE (by decide) i := by
  simp only [stageEntryStateRename, Fin.lastCases_castSucc]
  apply Fin.ext
  rfl

theorem comp_stageEntryStateRename
    (index entry stage relation : LCarrier.{u}) :
    (fun i => snoc (snoc (stageEntryAtLAssignment index entry) stage) relation
      (stageEntryStateRename i)) =
      stageStateAtLAssignment index stage relation := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · refine Fin.lastCases ?_ (fun i12 => ?_) i13
      · rfl
      · rw [stageEntryStateRename_fixed,
          stageEntryState_fixed_castLE]
        simp only [stageStateAtLAssignment, snoc_castSucc]

/-- The canonical triple encoding a state at one index. -/
def StageEntryAt (index entry : LCarrier.{u}) : Prop :=
  ∃ stage relation : LCarrier.{u},
    StageStateAt index stage relation ∧
      entry.1 = Godel.triple index.1 stage.1 relation.1

/-- Replacement-ready formula whose output is the canonical history entry. -/
def stageEntryAtFormula : FOFormula 15 :=
  .ex (.ex (.conj
    (FOFormula.rename stageEntryStateRename stageStateAtFormula)
    (Delta0Formula.tripleEqAt
      (14 : Fin 17) (13 : Fin 17) (15 : Fin 17) (16 : Fin 17)).toFO))

@[simp]
theorem satisfies_stageEntryAtFormula
    (index entry : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageEntryAtFormula
        (stageEntryAtLAssignment index entry) ↔
      StageEntryAt index entry := by
  simp only [stageEntryAtFormula, FOFormula.Satisfies, StageEntryAt]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [FOFormula.satisfies_rename, comp_stageEntryStateRename,
    satisfies_stageStateAtFormula]
  apply and_congr_right
  intro _hstate
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_tripleEqAt]
  simp only [stageEntryWitness_entry, stageEntryWitness_index,
    stageEntryWitness_stage, stageEntryWitness_relation]

end

end Constructible.Model
