/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryEntry

/-!
# The limit-state clause for constructible-stage histories

At a limit index, both the stage and its coherent order graph are internal
unions of their earlier values.  The formulas here express those two
extensional union clauses using only membership and the verified history-entry
predicate.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
All formulas in this file have the outer layout
`(history, index, stage, relation)`.

After binding a candidate member `z`, the union witness layout is
`(history, index, stage, relation, z, earlierIndex, earlierStage,
earlierRelation)`.
-/

/-- The stage coordinate is the union of all earlier stage coordinates. -/
def historyUnionStageFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (4 : Fin 5) (2 : Fin 5))
      (FOFormula.boundedEx (1 : Fin 5)
        (.ex (.ex
          (.conj
            (historyEntryAt
              (0 : Fin 8) (5 : Fin 8) (6 : Fin 8) (7 : Fin 8))
            (.mem (4 : Fin 8) (6 : Fin 8)))))))

/-- The relation coordinate is the union of all earlier relation graphs. -/
def historyUnionRelationFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (4 : Fin 5) (3 : Fin 5))
      (FOFormula.boundedEx (1 : Fin 5)
        (.ex (.ex
          (.conj
            (historyEntryAt
              (0 : Fin 8) (5 : Fin 8) (6 : Fin 8) (7 : Fin 8))
            (.mem (4 : Fin 8) (7 : Fin 8)))))))

/-- Both coordinates obey their limit-union clauses. -/
def historyLimitStateFormula : FOFormula 4 :=
  .conj historyUnionStageFormula historyUnionRelationFormula

/-- The direct assignment for all history-state formulas. -/
def historyStateAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![history, index, stage, relation]

@[simp]
theorem satisfies_historyUnionStageFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyUnionStageFormula
        (historyStateAssignment history index stage relation) ↔
      ∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierStage.1 := by
  simp only [historyUnionStageFormula, historyStateAssignment,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry]
  rfl

@[simp]
theorem satisfies_historyUnionRelationFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyUnionRelationFormula
        (historyStateAssignment history index stage relation) ↔
      ∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierRelation.1 := by
  simp only [historyUnionRelationFormula, historyStateAssignment,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry]
  rfl

@[simp]
theorem satisfies_historyLimitStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyLimitStateFormula
        (historyStateAssignment history index stage relation) ↔
      (∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierStage.1) ∧
      (∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierRelation.1) := by
  simp only [historyLimitStateFormula, FOFormula.Satisfies,
    satisfies_historyUnionStageFormula,
    satisfies_historyUnionRelationFormula]

end

end Constructible.Model
