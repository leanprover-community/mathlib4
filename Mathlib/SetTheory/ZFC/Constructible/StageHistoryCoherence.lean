/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageHistoryRecursion
public import Mathlib.SetTheory.ZFC.Constructible.CoherentStageGraphExtension

/-!
# Coherence of the internally recursive stage graphs

The relation coordinate of `stageHistoryData` is now assembled into a graph
system.  Successors use the canonical extension theorem and limits use the
internally represented relation family constructed by Replacement.
-/

@[expose] public section

universe u

namespace Constructible.Model

noncomputable section

/-- The recursively constructed graph at every ordinal below `bound`. -/
def historyStageGraphs (bound : Ordinal.{u}) :
    Set.Iio bound → LCarrier.{u} :=
  fun ordinal => (stageHistoryData ordinal.1).relation

@[simp]
theorem historyStageGraphs_apply (bound : Ordinal.{u})
    (ordinal : Set.Iio bound) :
    historyStageGraphs bound ordinal =
      (stageHistoryData ordinal.1).relation :=
  rfl

/-- The internal relation family used at a limit represents exactly the
range of the recursively constructed earlier graphs. -/
theorem stageRelationFamily_represents_historyStageGraphs
    (limit : Ordinal.{u}) :
    RepresentsStageGraphFamily (historyStageGraphs limit)
      (stageRelationFamily limit
        (uniqueStageStatesBelow_of_historyData
          (fun ordinal _hordinal => stageHistoryData ordinal))) := by
  let hstates : UniqueStageStatesBelow limit :=
    uniqueStageStatesBelow_of_historyData
      (fun ordinal _hordinal => stageHistoryData ordinal)
  intro relation
  rw [show stageRelationFamily limit
      (uniqueStageStatesBelow_of_historyData
        (fun ordinal _hordinal => stageHistoryData ordinal)) =
      stageRelationFamily limit hstates by rfl]
  rw [mem_stageRelationFamily_iff]
  constructor
  · rintro ⟨index, hindex, stage, hstate⟩
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hcanonical := (stageHistoryData ordinal).state
    have houtputs := stageStateAt_ordinal_outputs_unique
      ordinal hstate hcanonical
    refine ⟨⟨ordinal, hordinal⟩, ?_⟩
    exact houtputs.2
  · rintro ⟨ordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal.1, ?_, ?_⟩
    · exact (ordinalLCarrier_mem_ordinalLCarrier_iff
        limit ordinal.1).mpr ordinal.2
    · exact ⟨stageLCarrier ordinal.1,
        (stageHistoryData ordinal.1).state⟩

/-- A stage extension together with the fact that its graph is exactly the
relation selected by the history recursion. -/
structure HistoryStageGraphExtension (ordinal : Ordinal.{u})
    (graphs : Set.Iio ordinal → LCarrier.{u}) where
/-- The coherent graph extension supplied at this stage. -/
  extension : StageGraphExtension ordinal graphs
  nextRelation_eq : extension.nextRelation =
    (stageHistoryData ordinal).relation

/-- In every ordinal case, the recursive relation is a valid coherent
extension of all earlier recursive graphs. -/
theorem historyStageGraphExtension_nonempty (ordinal : Ordinal.{u})
    (hsystem : CoherentStageGraphSystem ordinal
      (historyStageGraphs ordinal)) :
    Nonempty
      (HistoryStageGraphExtension ordinal
        (historyStageGraphs ordinal)) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit ordinal with
    hzero | hsuccessor | hlimit
  · subst ordinal
    let extension : StageGraphExtension (0 : Ordinal.{u})
        (historyStageGraphs 0) :=
      { nextRelation := emptyLCarrier
        wellOrders := zeroStageGraphExtension.wellOrders
        supported := zeroStageGraphExtension.supported
        agreesOnEarlier := by
          intro beta
          exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim
        earlierIsInitial := by
          intro beta
          exact (not_lt_of_ge bot_le (Set.mem_Iio.mp beta.2)).elim }
    exact ⟨
      { extension := extension
        nextRelation_eq := by
          change emptyLCarrier = (stageHistoryData 0).relation
          exact stageHistoryData_relation_zero.symm }⟩
  · rcases hsuccessor with ⟨alpha, rfl⟩
    let extension := canonicalSuccessorStageGraphExtension alpha
      (historyStageGraphs (Order.succ alpha)) hsystem
    refine ⟨
      { extension := extension
        nextRelation_eq := ?_ }⟩
    rw [stageHistoryData_relation_succ]
    rfl
  · let family := stageRelationFamily ordinal
      (uniqueStageStatesBelow_of_historyData
        (fun beta _hbeta => stageHistoryData beta))
    have hfamily : RepresentsStageGraphFamily
        (historyStageGraphs ordinal) family :=
      stageRelationFamily_represents_historyStageGraphs ordinal
    let extension := coherentLimitStageGraphExtension hlimit
      (historyStageGraphs ordinal) hsystem family hfamily
    refine ⟨
      { extension := extension
        nextRelation_eq := ?_ }⟩
    rw [stageHistoryData_relation_limit hlimit]
    rfl

/-- A chosen coherent extension.  Its equality field fixes the chosen graph
to the relation produced by `stageHistoryData`. -/
noncomputable def historyStageGraphExtension (ordinal : Ordinal.{u})
    (hsystem : CoherentStageGraphSystem ordinal
      (historyStageGraphs ordinal)) :
    HistoryStageGraphExtension ordinal (historyStageGraphs ordinal) :=
  Classical.choice (historyStageGraphExtension_nonempty ordinal hsystem)

end

end Constructible.Model
