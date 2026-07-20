/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageStateAtFormula
public import Mathlib.SetTheory.ZFC.Constructible.Replacement
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryOperations

/-!
# Internal replacement families for constructible-stage recursion

Assuming that every earlier ordinal index has a unique stage/relation state,
the fixed formulas from `StageStateAtFormula` turn the earlier history entries
and relation graphs into actual members of `L` by Replacement.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- Unique stage/relation outputs at every ordinal strictly below `bound`. -/
def UniqueStageStatesBelow (bound : Ordinal.{u}) : Prop :=
  ∀ index < bound,
    ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt (ordinalLCarrier index) output.1 output.2

/-- Every member of a von Neumann ordinal code is the canonical code of a
unique smaller ordinal. -/
theorem exists_eq_ordinalLCarrier_of_mem
    {bound : Ordinal.{u}} {index : LCarrier.{u}}
    (hindex : index.1 ∈ (ordinalLCarrier bound).1) :
    ∃ ordinal < bound, index = ordinalLCarrier ordinal := by
  have hraw : index.1 ∈ bound.toZFSet := by
    simpa only [ordinalLCarrier_val] using hindex
  rcases Ordinal.mem_toZFSet_iff.mp hraw with
    ⟨ordinal, hordinal, hcode⟩
  refine ⟨ordinal, hordinal, ?_⟩
  apply Subtype.ext
  exact hcode.symm

/-- Uniqueness of the state pair gives uniqueness of its canonical triple. -/
theorem existsUnique_stageEntryAt_of_uniqueState
    (index : LCarrier.{u})
    (hstate : ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt index output.1 output.2) :
    ∃! entry : LCarrier.{u}, StageEntryAt index entry := by
  rcases hstate with ⟨⟨stage, relation⟩, hstate, hunique⟩
  let entry := tripleLCarrier index stage relation
  refine ⟨entry, ?_, ?_⟩
  · exact ⟨stage, relation, hstate,
      tripleLCarrier_val index stage relation⟩
  · intro other hother
    rcases hother with ⟨otherStage, otherRelation,
      hotherState, hotherCode⟩
    have houtputs :
        (otherStage, otherRelation) = (stage, relation) :=
      hunique (otherStage, otherRelation) hotherState
    have hstage : otherStage = stage := congrArg Prod.fst houtputs
    have hrelation : otherRelation = relation :=
      congrArg Prod.snd houtputs
    subst otherStage
    subst otherRelation
    apply Subtype.ext
    exact hotherCode.trans
      (tripleLCarrier_val index stage relation).symm

/-- Uniqueness of the state pair also gives a unique relation coordinate. -/
theorem existsUnique_stageRelationAt_of_uniqueState
    (index : LCarrier.{u})
    (hstate : ∃! output : LCarrier.{u} × LCarrier.{u},
      StageStateAt index output.1 output.2) :
    ∃! relation : LCarrier.{u}, StageRelationAt index relation := by
  rcases hstate with ⟨⟨stage, relation⟩, hstate, hunique⟩
  refine ⟨relation, ⟨stage, hstate⟩, ?_⟩
  intro otherRelation hother
  rcases hother with ⟨otherStage, hotherState⟩
  have houtputs :
      (otherStage, otherRelation) = (stage, relation) :=
    hunique (otherStage, otherRelation) hotherState
  exact congrArg Prod.snd houtputs

/-- Replacement constructs the internal set of all canonical history entries
strictly below `bound`. -/
theorem exists_stageEntryFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    ∃ history : LCarrier.{u}, ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 →
        ∃! entry : LCarrier.{u},
          FOFormula.Satisfies LMem stageEntryAtFormula
            (snoc (snoc stageHistoryFixedParameters index) entry) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases existsUnique_stageEntryAt_of_uniqueState
      (ordinalLCarrier ordinal) (hstates ordinal hordinal)
      with ⟨entry, hentry, hunique⟩
    refine ⟨entry, ?_, ?_⟩
    · change FOFormula.Satisfies LMem stageEntryAtFormula
        (stageEntryAtLAssignment (ordinalLCarrier ordinal) entry)
      exact (satisfies_stageEntryAtFormula
        (ordinalLCarrier ordinal) entry).mpr hentry
    · intro other hother
      apply hunique other
      apply (satisfies_stageEntryAtFormula
        (ordinalLCarrier ordinal) other).mp
      exact hother
  rcases exists_replacementLCarrier stageEntryAtFormula
      stageHistoryFixedParameters (ordinalLCarrier bound) hfun with
    ⟨history, hhistory⟩
  refine ⟨history, ?_⟩
  intro entry
  rw [hhistory]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_stageEntryAtFormula index entry

/-- Replacement constructs the internal family of all relation graphs
strictly below `bound`. -/
theorem exists_stageRelationFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    ∃ family : LCarrier.{u}, ∀ relation : LCarrier.{u},
      relation.1 ∈ family.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageRelationAt index relation := by
  have hfun : ∀ index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 →
        ∃! relation : LCarrier.{u},
          FOFormula.Satisfies LMem stageRelationAtFormula
            (snoc (snoc stageHistoryFixedParameters index) relation) := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    rcases existsUnique_stageRelationAt_of_uniqueState
      (ordinalLCarrier ordinal) (hstates ordinal hordinal)
      with ⟨relation, hrelation, hunique⟩
    refine ⟨relation, ?_, ?_⟩
    · change FOFormula.Satisfies LMem stageRelationAtFormula
        (stageRelationAtLAssignment (ordinalLCarrier ordinal) relation)
      exact (satisfies_stageRelationAtFormula
        (ordinalLCarrier ordinal) relation).mpr hrelation
    · intro other hother
      apply hunique other
      apply (satisfies_stageRelationAtFormula
        (ordinalLCarrier ordinal) other).mp
      exact hother
  rcases exists_replacementLCarrier stageRelationAtFormula
      stageHistoryFixedParameters (ordinalLCarrier bound) hfun with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro relation
  rw [hfamily]
  apply exists_congr
  intro index
  apply and_congr_right
  intro _hindex
  exact satisfies_stageRelationAtFormula index relation

/-- A chosen internal history containing exactly the earlier canonical
entries.  Its specification, not the metatheoretic choice of witness, is the
public interface. -/
noncomputable def stageEntryFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    LCarrier.{u} :=
  Classical.choose (exists_stageEntryFamily bound hstates)

@[simp]
theorem mem_stageEntryFamily_iff
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (entry : LCarrier.{u}) :
    entry.1 ∈ (stageEntryFamily bound hstates).1 ↔
      ∃ index : LCarrier.{u},
        index.1 ∈ (ordinalLCarrier bound).1 ∧
          StageEntryAt index entry :=
  Classical.choose_spec (exists_stageEntryFamily bound hstates) entry

/-- A chosen internal set containing exactly the earlier relation outputs. -/
noncomputable def stageRelationFamily
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound) :
    LCarrier.{u} :=
  Classical.choose (exists_stageRelationFamily bound hstates)

@[simp]
theorem mem_stageRelationFamily_iff
    (bound : Ordinal.{u}) (hstates : UniqueStageStatesBelow bound)
    (relation : LCarrier.{u}) :
    relation.1 ∈ (stageRelationFamily bound hstates).1 ↔
      ∃ index : LCarrier.{u},
        index.1 ∈ (ordinalLCarrier bound).1 ∧
          StageRelationAt index relation :=
  Classical.choose_spec (exists_stageRelationFamily bound hstates) relation

/-- Exact lookup semantics of a Replacement-generated history.  In
particular, the internal history contains no entries at or above `bound`. -/
theorem historyEntry_iff_of_stageEntryFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (index stage relation : LCarrier.{u}) :
    HistoryEntry history index stage relation ↔
      index.1 ∈ (ordinalLCarrier bound).1 ∧
        StageStateAt index stage relation := by
  let entry := tripleLCarrier index stage relation
  have hentry :
      entry.1 = Godel.triple index.1 stage.1 relation.1 :=
    tripleLCarrier_val index stage relation
  constructor
  · intro hlookup
    have hmem : entry.1 ∈ history.1 := by
      rw [hentry]
      exact hlookup
    rcases (hhistory entry).mp hmem with
      ⟨otherIndex, hotherIndex, otherStage, otherRelation,
        hotherState, hotherCode⟩
    have hcodes :
        Godel.triple index.1 stage.1 relation.1 =
          Godel.triple otherIndex.1 otherStage.1 otherRelation.1 :=
      hentry.symm.trans hotherCode
    have hcoordinates := triple_injective hcodes
    have hindex : index = otherIndex := Subtype.ext hcoordinates.1
    have hstage : stage = otherStage :=
      Subtype.ext hcoordinates.2.1
    have hrelation : relation = otherRelation :=
      Subtype.ext hcoordinates.2.2
    subst otherIndex
    subst otherStage
    subst otherRelation
    exact ⟨hotherIndex, hotherState⟩
  · rintro ⟨hindex, hstate⟩
    have hmem : entry.1 ∈ history.1 := (hhistory entry).mpr
      ⟨index, hindex, stage, relation, hstate, hentry⟩
    change Godel.triple index.1 stage.1 relation.1 ∈ history.1
    rw [← hentry]
    exact hmem

/-- Appending the top state to a Replacement-generated history gives an
exact old-or-top lookup split. -/
theorem historyEntry_addTop_iff_of_stageEntryFamily
    {bound : Ordinal.{u}} {history : LCarrier.{u}}
    (hhistory : ∀ entry : LCarrier.{u},
      entry.1 ∈ history.1 ↔
        ∃ index : LCarrier.{u},
          index.1 ∈ (ordinalLCarrier bound).1 ∧
            StageEntryAt index entry)
    (topStage topRelation index stage relation : LCarrier.{u}) :
    HistoryEntry
        (addHistoryEntry history (ordinalLCarrier bound)
          topStage topRelation)
        index stage relation ↔
      (index.1 ∈ (ordinalLCarrier bound).1 ∧
        StageStateAt index stage relation) ∨
      (index = ordinalLCarrier bound ∧ stage = topStage ∧
        relation = topRelation) := by
  rw [historyEntry_addHistoryEntry_iff,
    historyEntry_iff_of_stageEntryFamily hhistory]

end

end Constructible.Model
