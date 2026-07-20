/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageStateUniqueness

/-!
# Internal transfinite recursion of constructible-stage histories

At every ordinal this file constructs an actual `LCarrier` history together
with its top relation.  The history is valid through the canonical ordinal
index, and its top stage coordinate is exactly `stageLCarrier ordinal`.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The internal history and top relation constructed at one ordinal. -/
structure StageHistoryData (ordinal : Ordinal.{u}) where
  /-- The internally represented stage history. -/
  history : LCarrier.{u}
  /-- The internally represented top-stage relation. -/
  relation : LCarrier.{u}
  valid : ValidStageHistory history (ordinalLCarrier ordinal)
  topEntry : HistoryEntry history (ordinalLCarrier ordinal)
    (stageLCarrier ordinal) relation

/-- A history datum supplies the corresponding history-independent state. -/
theorem StageHistoryData.state {ordinal : Ordinal.{u}}
    (data : StageHistoryData ordinal) :
    StageStateAt (ordinalLCarrier ordinal)
      (stageLCarrier ordinal) data.relation :=
  ⟨data.history, data.valid, data.topEntry⟩

/-- The state supplied by a history datum is the unique state at its index. -/
theorem StageHistoryData.existsUniqueState {ordinal : Ordinal.{u}}
    (data : StageHistoryData ordinal) :
    ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt (ordinalLCarrier ordinal) output.1 output.2 := by
  refine ⟨(stageLCarrier ordinal, data.relation), data.state, ?_⟩
  intro other hother
  exact stageStateAt_ordinal_pair_unique ordinal data.state hother

/-- A datum through `alpha` supplies unique states below `alpha + 1`. -/
theorem StageHistoryData.uniqueStatesBelowSucc
    {alpha : Ordinal.{u}} (data : StageHistoryData alpha) :
    UniqueStageStatesBelow (Order.succ alpha) := by
  intro ordinal hordinal
  have hle : ordinal ≤ alpha := Order.lt_succ_iff.mp hordinal
  have hbound :
      (ordinalLCarrier ordinal).1 ∈ (ordinalLCarrier alpha).1 ∨
        ordinalLCarrier ordinal = ordinalLCarrier alpha := by
    rcases hle.eq_or_lt with rfl | hlt
    · exact Or.inr rfl
    · exact Or.inl
        ((ordinalLCarrier_mem_ordinalLCarrier_iff alpha ordinal).mpr hlt)
  rcases data.valid (ordinalLCarrier ordinal) hbound with
    ⟨stage, relation, hentry, _hunique, _hlocal⟩
  have hstate : StageStateAt (ordinalLCarrier ordinal) stage relation :=
    stageStateAt_of_validHistory rfl hle data.valid hentry
  refine ⟨(stage, relation), hstate, ?_⟩
  intro other hother
  exact stageStateAt_ordinal_pair_unique ordinal hstate hother

/-- A family of earlier history data supplies unique states below a limit. -/
theorem uniqueStageStatesBelow_of_historyData
    {bound : Ordinal.{u}}
    (data : ∀ ordinal < bound, StageHistoryData ordinal) :
    UniqueStageStatesBelow bound := by
  intro ordinal hordinal
  exact (data ordinal hordinal).existsUniqueState

@[simp]
theorem stageLCarrier_zero :
    stageLCarrier (0 : Ordinal.{u}) = emptyLCarrier := by
  apply Subtype.ext
  change LStageZF (0 : Ordinal.{u}) = (∅ : ZFSet.{u})
  exact LStageZF_zero

/-- The unique zero state, represented by a one-entry internal history. -/
def zeroStageHistoryData : StageHistoryData (0 : Ordinal.{u}) := by
  let history : LCarrier.{u} := emptyLCarrier
  let extended := addHistoryEntry history (ordinalLCarrier 0)
    (stageLCarrier 0) emptyLCarrier
  have hstates : UniqueStageStatesBelow (0 : Ordinal.{u}) := by
    intro ordinal hordinal
    exact (not_lt_of_ge bot_le hordinal).elim
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (0 : Ordinal.{u})).1 ∧
            StageEntryAt index entry := by
    intro entry
    constructor
    · intro hentry
      exact (not_mem_emptyLCarrier entry hentry).elim
    · rintro ⟨index, hindex, _hstate⟩
      exact (not_mem_emptyLCarrier index
        (by simpa only [ordinalLCarrier_zero] using hindex)).elim
  have htopLocal : HistoryLocalState extended (ordinalLCarrier 0)
      (stageLCarrier 0) emptyLCarrier := by
    apply (historyLocalState_zero_iff
      extended (stageLCarrier 0) emptyLCarrier).mpr
    exact ⟨stageLCarrier_zero, rfl⟩
  have hvalid : ValidStageHistory extended (ordinalLCarrier 0) :=
    validStageHistory_addTop_of_family 0 hstates history hhistory
      (stageLCarrier 0) emptyLCarrier htopLocal
  have htopEntry : HistoryEntry extended (ordinalLCarrier 0)
      (stageLCarrier 0) emptyLCarrier := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier 0) emptyLCarrier
      (ordinalLCarrier 0) (stageLCarrier 0) emptyLCarrier).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := emptyLCarrier
      valid := hvalid
      topEntry := htopEntry }

/-- The successor datum obtained from the canonical deterministic graph
extension and an internally replaced family of all previous entries. -/
def successorStageHistoryData (alpha : Ordinal.{u})
    (previous : StageHistoryData alpha) :
    StageHistoryData (alpha + 1) := by
  rw [← Order.succ_eq_add_one]
  let hstates : UniqueStageStatesBelow (Order.succ alpha) :=
    previous.uniqueStatesBelowSucc
  let history : LCarrier.{u} :=
    stageEntryFamily (Order.succ alpha) hstates
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier (Order.succ alpha)).1 ∧
            StageEntryAt index entry :=
    mem_stageEntryFamily_iff (Order.succ alpha) hstates
  let nextRelation := canonicalSuccessorRelation alpha previous.relation
  let extended := addHistoryEntry history
    (ordinalLCarrier (Order.succ alpha))
    (stageLCarrier (Order.succ alpha)) nextRelation
  have hpredecessorEntry : HistoryEntry extended
      (ordinalLCarrier alpha) (stageLCarrier alpha) previous.relation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier (Order.succ alpha)) nextRelation
      (ordinalLCarrier alpha) (stageLCarrier alpha)
      previous.relation).mpr
    exact Or.inl
      ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
          (Order.succ alpha) alpha).mpr (Order.lt_succ alpha),
        previous.state⟩
  have hstage : (stageLCarrier (Order.succ alpha)).1 =
      Godel.godelDef (stageLCarrier alpha).1 := by
    simp only [stageLCarrier_val, LStageZF_succ,
      Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)]
  have htopLocal : HistoryLocalState extended
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation := by
    apply (historyLocalState_successor_iff extended alpha
      (stageLCarrier (Order.succ alpha)) nextRelation).mpr
    refine ⟨stageLCarrier alpha, previous.relation,
      hpredecessorEntry, hstage, ?_⟩
    rfl
  have hvalid : ValidStageHistory extended
      (ordinalLCarrier (Order.succ alpha)) :=
    validStageHistory_addTop_of_family (Order.succ alpha) hstates
      history hhistory (stageLCarrier (Order.succ alpha))
      nextRelation htopLocal
  have htopEntry : HistoryEntry extended
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier (Order.succ alpha)) nextRelation
      (ordinalLCarrier (Order.succ alpha))
      (stageLCarrier (Order.succ alpha)) nextRelation).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := nextRelation
      valid := hvalid
      topEntry := htopEntry }

@[simp]
theorem successorStageHistoryData_relation (alpha : Ordinal.{u})
    (previous : StageHistoryData alpha) :
    (successorStageHistoryData alpha previous).relation =
      canonicalSuccessorRelation alpha previous.relation := by
  rfl

/-- At a nonzero limit, Replacement internalizes both the complete earlier
entry family and the complete earlier relation family.  Their internal union
is the top relation. -/
def limitStageHistoryData {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (previous : ∀ ordinal < limit, StageHistoryData ordinal) :
    StageHistoryData limit := by
  let hstates : UniqueStageStatesBelow limit :=
    uniqueStageStatesBelow_of_historyData previous
  let history : LCarrier.{u} := stageEntryFamily limit hstates
  have hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier limit).1 ∧
            StageEntryAt index entry :=
    mem_stageEntryFamily_iff limit hstates
  let family : LCarrier.{u} := stageRelationFamily limit hstates
  have hfamily : ∀ relation : LCarrier.{u},
      relation.1 ∈ family.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier limit).1 ∧
            StageRelationAt index relation :=
    mem_stageRelationFamily_iff limit hstates
  let topRelation := sUnionLCarrier family
  let extended := addHistoryEntry history (ordinalLCarrier limit)
    (stageLCarrier limit) topRelation
  have hstageUnion : ∀ z : LCarrier.{u},
      z.1 ∈ (stageLCarrier limit).1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier limit).1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry extended earlierIndex
                earlierStage earlierRelation ∧
              z.1 ∈ earlierStage.1 := by
    intro z
    constructor
    · intro hz
      have hzLimit : z.1 ∈ LStageZF limit := by
        simpa only [stageLCarrier_val] using hz
      rcases (mem_LStageZF_limit_iff hl).mp hzLimit with
        ⟨ordinal, hordinal, hzOrdinal⟩
      let data := previous ordinal hordinal
      have hindex :
          (ordinalLCarrier ordinal).1 ∈
            (ordinalLCarrier limit).1 :=
        (ordinalLCarrier_mem_ordinalLCarrier_iff
          limit ordinal).mpr hordinal
      have hentry : HistoryEntry extended (ordinalLCarrier ordinal)
          (stageLCarrier ordinal) data.relation := by
        apply (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          (ordinalLCarrier ordinal) (stageLCarrier ordinal)
          data.relation).mpr
        exact Or.inl ⟨hindex, data.state⟩
      refine ⟨ordinalLCarrier ordinal, hindex,
        stageLCarrier ordinal, data.relation, hentry, ?_⟩
      simpa only [stageLCarrier_val] using hzOrdinal
    · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
      rcases exists_eq_ordinalLCarrier_of_mem hindex with
        ⟨ordinal, hordinal, rfl⟩
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          (ordinalLCarrier ordinal) earlierStage earlierRelation).mp
          hentry with hold | htop
      · have hcanonical := (previous ordinal hordinal).state
        have houtputs := stageStateAt_ordinal_outputs_unique
          ordinal hold.2 hcanonical
        have hzOrdinal : z.1 ∈ LStageZF ordinal := by
          simpa only [houtputs.1, stageLCarrier_val] using hzEarlier
        have hzLimit : z.1 ∈ LStageZF limit :=
          LStageZF_mono hordinal.le hzOrdinal
        simpa only [stageLCarrier_val] using hzLimit
      · have hordinalEq : ordinal = limit :=
          ordinalLCarrier_injective htop.1
        exact ((ne_of_lt hordinal) hordinalEq).elim
  have hrelationUnion : ∀ z : LCarrier.{u},
      z.1 ∈ topRelation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier limit).1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry extended earlierIndex
                earlierStage earlierRelation ∧
              z.1 ∈ earlierRelation.1 := by
    intro z
    constructor
    · intro hz
      rcases (mem_sUnionLCarrier_iff family z).mp hz with
        ⟨earlierRelation, hrelationFamily, hzEarlier⟩
      rcases (hfamily earlierRelation).mp hrelationFamily with
        ⟨earlierIndex, hindex, earlierStage, hstate⟩
      have hentry : HistoryEntry extended earlierIndex
          earlierStage earlierRelation := by
        apply (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          earlierIndex earlierStage earlierRelation).mpr
        exact Or.inl ⟨hindex, hstate⟩
      exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
    · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
        hentry, hzEarlier⟩
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory (stageLCarrier limit) topRelation
          earlierIndex earlierStage earlierRelation).mp hentry with
        hold | htop
      · apply (mem_sUnionLCarrier_iff family z).mpr
        refine ⟨earlierRelation, ?_, hzEarlier⟩
        apply (hfamily earlierRelation).mpr
        exact ⟨earlierIndex, hindex, earlierStage, hold.2⟩
      · rw [htop.1] at hindex
        exact (ZFSet.mem_irrefl _ hindex).elim
  have htopLimit : HistoryLimitState extended
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation :=
    ⟨hstageUnion, hrelationUnion⟩
  have htopLocal : HistoryLocalState extended
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation :=
    (historyLocalState_limit_iff extended hl
      (stageLCarrier limit) topRelation).mpr htopLimit
  have hvalid : ValidStageHistory extended (ordinalLCarrier limit) :=
    validStageHistory_addTop_of_family limit hstates history hhistory
      (stageLCarrier limit) topRelation htopLocal
  have htopEntry : HistoryEntry extended (ordinalLCarrier limit)
      (stageLCarrier limit) topRelation := by
    apply (historyEntry_addTop_iff_of_stageEntryFamily
      hhistory (stageLCarrier limit) topRelation
      (ordinalLCarrier limit) (stageLCarrier limit) topRelation).mpr
    exact Or.inr ⟨rfl, rfl, rfl⟩
  exact
    { history := extended
      relation := topRelation
      valid := hvalid
      topEntry := htopEntry }

@[simp]
theorem limitStageHistoryData_relation {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (previous : ∀ ordinal < limit, StageHistoryData ordinal) :
    (limitStageHistoryData hl previous).relation =
      sUnionLCarrier
        (stageRelationFamily limit
          (uniqueStageStatesBelow_of_historyData previous)) := by
  rfl

@[simp]
theorem zeroStageHistoryData_relation :
    zeroStageHistoryData.relation = (emptyLCarrier : LCarrier.{u}) := by
  rfl

/-- The complete ordinal recursion of internal stage histories. -/
noncomputable def stageHistoryData (ordinal : Ordinal.{u}) :
    StageHistoryData ordinal :=
  Ordinal.limitRecOn ordinal
    zeroStageHistoryData
    successorStageHistoryData
    (fun _limit hl previous => limitStageHistoryData hl previous)

@[simp]
theorem stageHistoryData_zero :
    stageHistoryData (0 : Ordinal.{u}) = zeroStageHistoryData := by
  rw [stageHistoryData, Ordinal.limitRecOn_zero]

@[simp]
theorem stageHistoryData_add_one (ordinal : Ordinal.{u}) :
    stageHistoryData (ordinal + 1) =
      successorStageHistoryData ordinal (stageHistoryData ordinal) := by
  exact Ordinal.limitRecOn_add_one ..

@[simp]
theorem stageHistoryData_limit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) :
    stageHistoryData limit =
      limitStageHistoryData hl
        (fun ordinal _hordinal => stageHistoryData ordinal) := by
  simp only [stageHistoryData,
    Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem stageHistoryData_relation_zero :
    (stageHistoryData (0 : Ordinal.{u})).relation = emptyLCarrier := by
  rw [stageHistoryData_zero, zeroStageHistoryData_relation]

@[simp]
theorem stageHistoryData_relation_succ (ordinal : Ordinal.{u}) :
    (stageHistoryData (Order.succ ordinal)).relation =
      canonicalSuccessorRelation ordinal
        (stageHistoryData ordinal).relation := by
  rw [Order.succ_eq_add_one, stageHistoryData_add_one,
    successorStageHistoryData_relation]

theorem stageHistoryData_relation_limit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) :
    (stageHistoryData limit).relation =
      sUnionLCarrier
        (stageRelationFamily limit
          (uniqueStageStatesBelow_of_historyData
            (fun ordinal _hordinal => stageHistoryData ordinal))) := by
  rw [stageHistoryData_limit hl, limitStageHistoryData_relation]

/-- Every canonical ordinal index has an internally witnessed state whose
stage coordinate is exactly `L_ordinal`. -/
theorem exists_stageStateAt_ordinal (ordinal : Ordinal.{u}) :
    ∃ relation : LCarrier.{u},
      StageStateAt (ordinalLCarrier ordinal)
        (stageLCarrier ordinal) relation :=
  ⟨(stageHistoryData ordinal).relation,
    (stageHistoryData ordinal).state⟩

/-- Every canonical ordinal index has a unique stage and relation state. -/
theorem existsUnique_stageStateAt_ordinal (ordinal : Ordinal.{u}) :
    ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt (ordinalLCarrier ordinal) output.1 output.2 :=
  (stageHistoryData ordinal).existsUniqueState

end

end Constructible.Model
