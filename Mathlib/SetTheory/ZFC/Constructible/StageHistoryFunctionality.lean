/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryEntry

/-!
# Functionality of stage-history lookup

A stage history is functional at an index when it contains exactly one pair
of stage and relation coordinates at that index.  The formula in this file
expresses that property entirely in the first-order membership language.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
The free-variable layout is `(history, index)`.  The first two existential
variables are `(stage, relation)`.  Inside the two universal quantifiers the
layout is

`(history, index, stage, relation, otherStage, otherRelation)`.
-/

/-- Once a history entry has been chosen, every other entry at the same index
has the same stage and relation coordinates. -/
def historyStateUniqueBody : FOFormula 4 :=
  FOFormula.all (FOFormula.all
    (FOFormula.imp
      (historyEntryAt
        (0 : Fin 6) (1 : Fin 6) (4 : Fin 6) (5 : Fin 6))
      (.conj
        (.eq (4 : Fin 6) (2 : Fin 6))
        (.eq (5 : Fin 6) (3 : Fin 6)))))

/-- `history` has exactly one `(stage, relation)` state at `index`. -/
def historyHasUniqueStateFormula : FOFormula 2 :=
  .ex (.ex
    (.conj
      (historyEntryAt
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
      historyStateUniqueBody))

@[simp] private lemma historyStateUniqueWitnessAssignment
    (history index stage relation otherStage otherRelation : LCarrier.{u}) :
    snoc (snoc ![history, index, stage, relation] otherStage) otherRelation =
      ![history, index, stage, relation, otherStage, otherRelation] := by
  funext i
  fin_cases i <;> rfl

@[simp] private lemma historyUniqueStateWitnessAssignment
    (history index stage relation : LCarrier.{u}) :
    snoc (snoc ![history, index] stage) relation =
      ![history, index, stage, relation] := by
  funext i
  fin_cases i <;> rfl

/-- Expanded semantics of the uniqueness body. -/
@[simp]
theorem satisfies_historyStateUniqueBody
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyStateUniqueBody
        ![history, index, stage, relation] ↔
      ∀ otherStage otherRelation : LCarrier.{u},
        HistoryEntry history index otherStage otherRelation →
          otherStage = stage ∧ otherRelation = relation := by
  simp only [historyStateUniqueBody, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.Satisfies]
  apply forall_congr'
  intro otherStage
  apply forall_congr'
  intro otherRelation
  rw [historyStateUniqueWitnessAssignment,
    satisfies_historyEntryAt_iff]
  rfl

/-- Expanded semantics before packaging the two output coordinates as a
product. -/
@[simp]
theorem satisfies_historyHasUniqueStateFormula_expanded
    (history index : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyHasUniqueStateFormula
        ![history, index] ↔
      ∃ stage relation : LCarrier.{u},
        HistoryEntry history index stage relation ∧
          ∀ otherStage otherRelation : LCarrier.{u},
            HistoryEntry history index otherStage otherRelation →
              otherStage = stage ∧ otherRelation = relation := by
  simp only [historyHasUniqueStateFormula, FOFormula.Satisfies]
  apply exists_congr
  intro stage
  apply exists_congr
  intro relation
  rw [historyUniqueStateWitnessAssignment,
    satisfies_historyEntryAt_iff, satisfies_historyStateUniqueBody]
  rfl

/-- Exact semantics: lookup at `(history,index)` has a unique state pair. -/
@[simp]
theorem satisfies_historyHasUniqueStateFormula_iff
    (history index : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyHasUniqueStateFormula
        ![history, index] ↔
      ∃! output : LCarrier.{u} × LCarrier.{u},
        HistoryEntry history index output.1 output.2 := by
  rw [satisfies_historyHasUniqueStateFormula_expanded]
  constructor
  · rintro ⟨stage, relation, hentry, hunique⟩
    refine ⟨(stage, relation), hentry, ?_⟩
    rintro ⟨otherStage, otherRelation⟩ hother
    have hcoordinates := hunique otherStage otherRelation hother
    exact Prod.ext hcoordinates.1 hcoordinates.2
  · rintro ⟨⟨stage, relation⟩, hentry, hunique⟩
    refine ⟨stage, relation, hentry, ?_⟩
    intro otherStage otherRelation hother
    have hpair := hunique (otherStage, otherRelation) hother
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end

end Constructible.Model
