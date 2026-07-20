/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryParameters

/-!
# The zero-state clause for constructible-stage histories

In the shared layout `(fixed13, history, index, stage, relation)`, the zero
rule requires all three state coordinates other than the ignored history to
be the empty set.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- The local recursion rule at index zero.  Coordinate `2` among the fixed
parameters is the canonical empty set. -/
def historyBaseStateFormula : FOFormula 17 :=
  .conj
    (.eq (14 : Fin 17) stageHistoryEmptyIndex)
    (.conj
      (.eq (15 : Fin 17) stageHistoryEmptyIndex)
      (.eq (16 : Fin 17) stageHistoryEmptyIndex))

@[simp]
theorem satisfies_historyBaseStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyBaseStateFormula
        (stageHistoryStateLAssignment history index stage relation) ↔
      index = emptyLCarrier ∧
        stage = emptyLCarrier ∧ relation = emptyLCarrier := by
  simp only [historyBaseStateFormula, FOFormula.Satisfies,
    stageHistoryStateLAssignment_index,
    stageHistoryStateLAssignment_stage,
    stageHistoryStateLAssignment_relation,
    stageHistoryStateLAssignment_emptyParameter]

end

end Constructible.Model
