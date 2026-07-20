/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryReplacement

/-!
# Uniqueness of ordinal-indexed stage states

The local history rule is deterministic on canonical ordinal indices.  This
file first normalizes the zero, successor, and limit cases, then uses ordinal
induction to compare states coming from different valid internal histories.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The empty carrier cannot be a von Neumann successor. -/
private theorem emptyLCarrier_ne_insert_self (predecessor : LCarrier.{u}) :
    ¬emptyLCarrier.1 = insert predecessor.1 predecessor.1 := by
  intro h
  have hmem : predecessor.1 ∈ emptyLCarrier.1 := by
    rw [h]
    exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  exact not_mem_emptyLCarrier predecessor hmem

/-- A valid history through a later ordinal remains valid through every
earlier ordinal. -/
theorem ValidStageHistory.restrictOrdinal
    {history : LCarrier.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (halpha : alpha ≤ beta) :
    ValidStageHistory history (ordinalLCarrier alpha) := by
  intro index hindex
  apply hvalid index
  rcases hindex with hindex | rfl
  · left
    exact Ordinal.toZFSet_monotone halpha hindex
  · rcases halpha.eq_or_lt with rfl | halpha
    · exact Or.inr rfl
    · exact Or.inl
        ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr halpha)

/-- An entry in a valid history gives a `StageStateAt` witness at every
canonical earlier bound. -/
theorem stageStateAt_of_validHistory
    {history index stage relation : LCarrier.{u}}
    {alpha beta : Ordinal.{u}}
    (hindex : index = ordinalLCarrier alpha)
    (halpha : alpha ≤ beta)
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (hentry : HistoryEntry history index stage relation) :
    StageStateAt index stage relation := by
  subst index
  exact ⟨history, hvalid.restrictOrdinal halpha, hentry⟩

/-- At its bound, validity transfers the local rule to any entry there. -/
theorem ValidStageHistory.localState_of_entry
    {history bound stage relation : LCarrier.{u}}
    (hvalid : ValidStageHistory history bound)
    (hentry : HistoryEntry history bound stage relation) :
    HistoryLocalState history bound stage relation := by
  rcases hvalid bound (Or.inr rfl) with
    ⟨chosenStage, chosenRelation, _hchosen, hunique, hlocal⟩
  have hcoordinates := hunique stage relation hentry
  simpa only [hcoordinates.1, hcoordinates.2] using hlocal

/-- The zero-index local rule has exactly the empty stage and empty graph. -/
theorem historyLocalState_zero_iff
    (history stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier 0) stage relation ↔
      stage = emptyLCarrier ∧ relation = emptyLCarrier := by
  rw [ordinalLCarrier_zero]
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · exact ⟨hbase.2.1, hbase.2.2⟩
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, _predecessorRelation,
          hpredecessor, _⟩
      exact (emptyLCarrier_ne_insert_self predecessorIndex hpredecessor).elim
    · exact (hlimit.1.1 rfl).elim
  · rintro ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- At a canonical successor index, only the successor branch of the local
rule is possible, and its predecessor index is canonical. -/
theorem historyLocalState_successor_iff
    (history : LCarrier.{u}) (alpha : Ordinal.{u})
    (stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier (Order.succ alpha))
        stage relation ↔
      ∃ predecessorStage predecessorRelation : LCarrier.{u},
        HistoryEntry history (ordinalLCarrier alpha)
          predecessorStage predecessorRelation ∧
        stage.1 = Godel.godelDef predecessorStage.1 ∧
        relation = canonicalSuccessorStateRelation
          predecessorStage predecessorRelation stage := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes :
          ordinalLCarrier (Order.succ alpha) = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : Order.succ alpha = 0 :=
        ordinalLCarrier_injective hcodes
      exact (Order.succ_ne_bot alpha hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, predecessorStage, predecessorRelation,
          hpredecessor, hentry, hstage, hrelation⟩
      have hindex :=
        (ordinalLCarrier_successor_predecessor_iff
          alpha predecessorIndex).mp hpredecessor
      subst predecessorIndex
      exact ⟨predecessorStage, predecessorRelation,
        hentry, hstage, hrelation⟩
    · have hpredecessor :
          ∃ predecessor : LCarrier.{u},
            (ordinalLCarrier (Order.succ alpha)).1 =
              insert predecessor.1 predecessor.1 :=
        ⟨ordinalLCarrier alpha, ordinalLCarrier_succ_val alpha⟩
      exact (hlimit.1.2 hpredecessor).elim
  · rintro ⟨predecessorStage, predecessorRelation,
      hentry, hstage, hrelation⟩
    exact Or.inr (Or.inl
      ⟨ordinalLCarrier alpha, predecessorStage, predecessorRelation,
        ordinalLCarrier_succ_val alpha, hentry, hstage, hrelation⟩)

/-- At a nonzero limit ordinal, only the two union clauses remain. -/
theorem historyLocalState_limit_iff
    (history : LCarrier.{u}) {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit) (stage relation : LCarrier.{u}) :
    HistoryLocalState history (ordinalLCarrier limit) stage relation ↔
      HistoryLimitState history (ordinalLCarrier limit) stage relation := by
  constructor
  · rintro (hbase | hsuccessor | hlimit)
    · have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hbase.1.trans ordinalLCarrier_zero.symm
      have hordinal : limit = 0 := ordinalLCarrier_injective hcodes
      exact (hl.ne_bot hordinal).elim
    · rcases hsuccessor with
        ⟨predecessorIndex, _predecessorStage, _predecessorRelation,
          hpredecessor, _⟩
      exact (ordinalLCarrier_limit_no_predecessor hl
        ⟨predecessorIndex, hpredecessor⟩).elim
    · exact hlimit.2
  · intro hlimit
    refine Or.inr (Or.inr ⟨?_, hlimit⟩)
    constructor
    · intro hzero
      have hcodes : ordinalLCarrier limit = ordinalLCarrier 0 :=
        hzero.trans ordinalLCarrier_zero.symm
      exact hl.ne_bot (ordinalLCarrier_injective hcodes)
    · exact ordinalLCarrier_limit_no_predecessor hl

/-- States at a canonical ordinal index are independent of the valid
internal history used to witness them. -/
theorem stageStateAt_ordinal_outputs_unique (ordinal : Ordinal.{u}) :
    ∀ {stage relation otherStage otherRelation : LCarrier.{u}},
      StageStateAt (ordinalLCarrier ordinal) stage relation →
      StageStateAt (ordinalLCarrier ordinal) otherStage otherRelation →
      stage = otherStage ∧ relation = otherRelation := by
  induction ordinal using Ordinal.limitRecOn with
  | zero =>
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      have houtputs :=
        (historyLocalState_zero_iff history stage relation).mp hlocal
      have hotherOutputs :=
        (historyLocalState_zero_iff
          otherHistory otherStage otherRelation).mp hotherLocal
      exact
        ⟨houtputs.1.trans hotherOutputs.1.symm,
          houtputs.2.trans hotherOutputs.2.symm⟩
  | add_one alpha ih =>
      rw [← Order.succ_eq_add_one]
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      rcases (historyLocalState_successor_iff
          history alpha stage relation).mp hlocal with
        ⟨predecessorStage, predecessorRelation, predecessorEntry,
          hstage, hrelation⟩
      rcases (historyLocalState_successor_iff
          otherHistory alpha otherStage otherRelation).mp hotherLocal with
        ⟨otherPredecessorStage, otherPredecessorRelation,
          otherPredecessorEntry, hotherStage, hotherRelation⟩
      have hpredecessorState :
          StageStateAt (ordinalLCarrier alpha)
            predecessorStage predecessorRelation :=
        stageStateAt_of_validHistory rfl (Order.le_succ alpha)
          hvalid predecessorEntry
      have hotherPredecessorState :
          StageStateAt (ordinalLCarrier alpha)
            otherPredecessorStage otherPredecessorRelation :=
        stageStateAt_of_validHistory rfl (Order.le_succ alpha)
          hotherValid otherPredecessorEntry
      have hpredecessor := ih hpredecessorState hotherPredecessorState
      have hstageEq : stage = otherStage := by
        apply Subtype.ext
        calc
          stage.1 = Godel.godelDef predecessorStage.1 := hstage
          _ = Godel.godelDef otherPredecessorStage.1 := by
            rw [hpredecessor.1]
          _ = otherStage.1 := hotherStage.symm
      have hrelationEq : relation = otherRelation := by
        calc
          relation = canonicalSuccessorStateRelation
              predecessorStage predecessorRelation stage := hrelation
          _ = canonicalSuccessorStateRelation
              otherPredecessorStage otherPredecessorRelation
                otherStage := by
            rw [hpredecessor.1, hpredecessor.2, hstageEq]
          _ = otherRelation := hotherRelation.symm
      exact ⟨hstageEq, hrelationEq⟩
  | limit limit hl ih =>
      intro stage relation otherStage otherRelation hstate hother
      rcases hstate with ⟨history, hvalid, hentry⟩
      rcases hother with ⟨otherHistory, hotherValid, hotherEntry⟩
      have hlocal := hvalid.localState_of_entry hentry
      have hotherLocal := hotherValid.localState_of_entry hotherEntry
      have hlimit :=
        (historyLocalState_limit_iff history hl stage relation).mp hlocal
      have hotherLimit :=
        (historyLocalState_limit_iff
          otherHistory hl otherStage otherRelation).mp hotherLocal
      have hstageEq : stage = otherStage := by
        apply lCarrier_extensionality
        intro z
        constructor
        · intro hz
          rcases (hlimit.1 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hotherValid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hotherLimit.1 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.1] using hzEarlier
        · intro hz
          rcases (hotherLimit.1 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hvalid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hlimit.1 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.1] using hzEarlier
      have hrelationEq : relation = otherRelation := by
        apply lCarrier_extensionality
        intro z
        constructor
        · intro hz
          rcases (hlimit.2 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hotherValid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hotherLimit.2 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.2] using hzEarlier
        · intro hz
          rcases (hotherLimit.2 z).mp hz with
            ⟨earlierIndex, hindex, earlierStage, earlierRelation,
              hearlierEntry, hzEarlier⟩
          rcases exists_eq_ordinalLCarrier_of_mem hindex with
            ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
          rcases hvalid (ordinalLCarrier earlierOrdinal)
              (Or.inl hindex) with
            ⟨targetStage, targetRelation, htargetEntry,
              _htargetUnique, _htargetLocal⟩
          have hearlierState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                earlierStage earlierRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hotherValid hearlierEntry
          have htargetState :
              StageStateAt (ordinalLCarrier earlierOrdinal)
                targetStage targetRelation :=
            stageStateAt_of_validHistory rfl hearlierOrdinal.le
              hvalid htargetEntry
          have houtputs :=
            ih earlierOrdinal hearlierOrdinal hearlierState htargetState
          apply (hlimit.2 z).mpr
          refine ⟨ordinalLCarrier earlierOrdinal, hindex,
            targetStage, targetRelation, htargetEntry, ?_⟩
          simpa only [houtputs.2] using hzEarlier
      exact ⟨hstageEq, hrelationEq⟩

/-- Pair-valued form of ordinal state uniqueness, used by Replacement. -/
theorem stageStateAt_ordinal_pair_unique
    (ordinal : Ordinal.{u})
    {output other : LCarrier.{u} × LCarrier.{u}}
    (houtput : StageStateAt (ordinalLCarrier ordinal)
      output.1 output.2)
    (hother : StageStateAt (ordinalLCarrier ordinal)
      other.1 other.2) :
    other = output := by
  have hcoordinates :=
    stageStateAt_ordinal_outputs_unique ordinal hother houtput
  exact Prod.ext hcoordinates.1 hcoordinates.2

/-- Within a valid ordinal-bounded history, lookup at a canonical earlier
index is equivalent to the history-independent `StageStateAt` predicate. -/
theorem historyEntry_iff_stageStateAt_of_validOrdinal
    {history : LCarrier.{u}} {alpha beta : Ordinal.{u}}
    (hvalid : ValidStageHistory history (ordinalLCarrier beta))
    (halpha : alpha ≤ beta) (stage relation : LCarrier.{u}) :
    HistoryEntry history (ordinalLCarrier alpha) stage relation ↔
      StageStateAt (ordinalLCarrier alpha) stage relation := by
  constructor
  · intro hentry
    exact stageStateAt_of_validHistory rfl halpha hvalid hentry
  · intro hstate
    have hbound :
        (ordinalLCarrier alpha).1 ∈ (ordinalLCarrier beta).1 ∨
          ordinalLCarrier alpha = ordinalLCarrier beta := by
      rcases halpha.eq_or_lt with rfl | halpha
      · exact Or.inr rfl
      · exact Or.inl
          ((ordinalLCarrier_mem_ordinalLCarrier_iff beta alpha).mpr halpha)
    rcases hvalid (ordinalLCarrier alpha) hbound with
      ⟨chosenStage, chosenRelation, hchosenEntry,
        _hchosenUnique, _hchosenLocal⟩
    have hchosenState :
        StageStateAt (ordinalLCarrier alpha)
          chosenStage chosenRelation :=
      stageStateAt_of_validHistory rfl halpha hvalid hchosenEntry
    have houtputs :=
      stageStateAt_ordinal_outputs_unique alpha hstate hchosenState
    simpa only [houtputs.1, houtputs.2] using hchosenEntry

/-- Changing a history without changing any entry below the current index
preserves the local recursion rule. -/
theorem historyLocalState_of_entriesBelow
    {first second index stage relation : LCarrier.{u}}
    (hentries : ∀ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 →
      ∀ earlierStage earlierRelation : LCarrier.{u},
        HistoryEntry first earlierIndex earlierStage earlierRelation ↔
          HistoryEntry second earlierIndex earlierStage earlierRelation)
    (hlocal : HistoryLocalState first index stage relation) :
    HistoryLocalState second index stage relation := by
  rcases hlocal with hbase | hsuccessor | hlimit
  · exact Or.inl hbase
  · rcases hsuccessor with
      ⟨predecessorIndex, predecessorStage, predecessorRelation,
        hpredecessor, hentry, hstage, hrelation⟩
    have hpredecessorMem : predecessorIndex.1 ∈ index.1 := by
      rw [hpredecessor]
      exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    exact Or.inr (Or.inl
      ⟨predecessorIndex, predecessorStage, predecessorRelation,
        hpredecessor,
        (hentries predecessorIndex hpredecessorMem
          predecessorStage predecessorRelation).mp hentry,
        hstage, hrelation⟩)
  · refine Or.inr (Or.inr ⟨hlimit.1, ?_⟩)
    constructor
    · intro z
      constructor
      · intro hz
        rcases (hlimit.2.1 z).mp hz with
          ⟨earlierIndex, hindex, earlierStage, earlierRelation,
            hentry, hzEarlier⟩
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mp hentry,
          hzEarlier⟩
      · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          hentry, hzEarlier⟩
        apply (hlimit.2.1 z).mpr
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mpr hentry,
          hzEarlier⟩
    · intro z
      constructor
      · intro hz
        rcases (hlimit.2.2 z).mp hz with
          ⟨earlierIndex, hindex, earlierStage, earlierRelation,
            hentry, hzEarlier⟩
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mp hentry,
          hzEarlier⟩
      · rintro ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          hentry, hzEarlier⟩
        apply (hlimit.2.2 z).mpr
        exact ⟨earlierIndex, hindex, earlierStage, earlierRelation,
          (hentries earlierIndex hindex
            earlierStage earlierRelation).mpr hentry,
          hzEarlier⟩

/-- Symmetric form of history invariance below an index. -/
theorem historyLocalState_congr_entriesBelow
    {first second index stage relation : LCarrier.{u}}
    (hentries : ∀ earlierIndex : LCarrier.{u},
      earlierIndex.1 ∈ index.1 →
      ∀ earlierStage earlierRelation : LCarrier.{u},
        HistoryEntry first earlierIndex earlierStage earlierRelation ↔
          HistoryEntry second earlierIndex earlierStage earlierRelation) :
    HistoryLocalState first index stage relation ↔
      HistoryLocalState second index stage relation := by
  constructor
  · exact historyLocalState_of_entriesBelow hentries
  · apply historyLocalState_of_entriesBelow
    intro earlierIndex hindex earlierStage earlierRelation
    exact (hentries earlierIndex hindex
      earlierStage earlierRelation).symm

/-- A Replacement-generated family of all earlier states becomes a valid
history through `bound` after adjoining one locally correct top state. -/
theorem validStageHistory_addTop_of_family
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (history : LCarrier.{u})
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (topStage topRelation : LCarrier.{u})
    (htopLocal : HistoryLocalState
      (addHistoryEntry history (ordinalLCarrier bound)
        topStage topRelation)
      (ordinalLCarrier bound) topStage topRelation) :
    ValidStageHistory
      (addHistoryEntry history (ordinalLCarrier bound)
        topStage topRelation)
      (ordinalLCarrier bound) := by
  intro index hindex
  rcases hindex with hindex | rfl
  · rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases hstates ordinal hordinal with
      ⟨⟨stage, relation⟩, hstate, _hstateUnique⟩
    refine ⟨stage, relation, ?_, ?_, ?_⟩
    · apply (historyEntry_addTop_iff_of_stageEntryFamily
        hhistory topStage topRelation
        (ordinalLCarrier ordinal) stage relation).mpr
      exact Or.inl ⟨hindex, hstate⟩
    · intro otherStage otherRelation hotherEntry
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory topStage topRelation
          (ordinalLCarrier ordinal) otherStage otherRelation).mp
          hotherEntry with hold | htop
      · exact stageStateAt_ordinal_outputs_unique
          ordinal hold.2 hstate
      · have hordinalEq : ordinal = bound :=
          ordinalLCarrier_injective htop.1
        exact ((ne_of_lt hordinal) hordinalEq).elim
    · rcases hstate with
        ⟨witnessHistory, hwitnessValid, hwitnessEntry⟩
      have hwitnessLocal :=
        hwitnessValid.localState_of_entry hwitnessEntry
      have hagree : ∀ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ (ordinalLCarrier ordinal).1 →
          ∀ earlierStage earlierRelation : LCarrier.{u},
            HistoryEntry witnessHistory earlierIndex
                earlierStage earlierRelation ↔
              HistoryEntry
                (addHistoryEntry history (ordinalLCarrier bound)
                  topStage topRelation)
                earlierIndex earlierStage earlierRelation := by
        intro earlierIndex hearlierIndex earlierStage earlierRelation
        rcases exists_eq_ordinalLCarrier_of_mem hearlierIndex with
          ⟨earlierOrdinal, hearlierOrdinal, rfl⟩
        have hearlierBound : earlierOrdinal < bound :=
          hearlierOrdinal.trans hordinal
        have hearlierMemBound :
            (ordinalLCarrier earlierOrdinal).1 ∈
              (ordinalLCarrier bound).1 :=
          (ordinalLCarrier_mem_ordinalLCarrier_iff
            bound earlierOrdinal).mpr hearlierBound
        have hearlierNeBound :
            ordinalLCarrier earlierOrdinal ≠ ordinalLCarrier bound := by
          intro heq
          exact (ne_of_lt hearlierBound)
            (ordinalLCarrier_injective heq)
        rw [historyEntry_iff_stageStateAt_of_validOrdinal
          hwitnessValid hearlierOrdinal.le]
        rw [historyEntry_addTop_iff_of_stageEntryFamily
          hhistory]
        simp only [hearlierMemBound, true_and,
          hearlierNeBound, false_and, or_false]
      exact (historyLocalState_congr_entriesBelow hagree).mp
        hwitnessLocal
  · refine ⟨topStage, topRelation, ?_, ?_, htopLocal⟩
    · apply (historyEntry_addTop_iff_of_stageEntryFamily
        hhistory topStage topRelation
        (ordinalLCarrier bound) topStage topRelation).mpr
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · intro otherStage otherRelation hotherEntry
      rcases (historyEntry_addTop_iff_of_stageEntryFamily
          hhistory topStage topRelation
          (ordinalLCarrier bound) otherStage otherRelation).mp
          hotherEntry with hold | htop
      · exact (ZFSet.mem_irrefl _ hold.1).elim
      · exact ⟨htop.2.1, htop.2.2⟩

end

end Constructible.Model
