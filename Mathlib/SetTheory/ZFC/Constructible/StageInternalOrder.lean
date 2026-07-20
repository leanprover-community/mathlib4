/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder
public import Mathlib.SetTheory.ZFC.Constructible.StageOrder

/-!
# From internally represented stage orders to Choice

Every constructible set is contained in some level `L_alpha`.  Consequently,
it is enough to construct, for every level, a well-order whose Kuratowski-pair
graph is itself a member of `L`.  This file proves that reduction and states
the exact internalization obligation for the external birth-layer order from
`StageOrder`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Model

/-- Include an element of one level into the full constructible carrier. -/
def stageToLCarrier (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) : LCarrier.{u} :=
  ⟨x.1, LStageZF_subset_constructibleUniverse alpha x.2⟩

@[simp]
theorem stageToLCarrier_val (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) :
    (stageToLCarrier alpha x).1 = x.1 :=
  rfl

/-- The relation induced on `L_alpha` by a constructible pair graph. -/
def stageGraphRel (r : LCarrier.{u}) (alpha : Ordinal.{u}) :
    LStageCarrier alpha -> LStageCarrier alpha -> Prop :=
  fun x y => GraphRel r (stageToLCarrier alpha x)
    (stageToLCarrier alpha y)

/-- A level has a well-order represented by an actual constructible graph. -/
def StageInternallyWellOrdered (alpha : Ordinal.{u}) : Prop :=
  exists r : LCarrier.{u},
    IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha)

/-- Every level has a constructibly represented well-order. -/
def AllStagesInternallyWellOrdered : Prop :=
  forall alpha : Ordinal.{u}, StageInternallyWellOrdered alpha

/-- Restricting an internally represented stage well-order preserves it. -/
theorem internallyWellOrders_of_stage
    {a : LCarrier.{u}} {alpha : Ordinal.{u}}
    (ha : forall x : ZFSet.{u}, x ∈ a.1 -> x ∈ LStageZF alpha)
    {r : LCarrier.{u}}
    (hr : IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha)) :
    InternallyWellOrders r a := by
  let stageEmbedding : InternalCarrier a -> LStageCarrier alpha :=
    fun x => ⟨x.1.1, ha x.1.1 x.2⟩
  have hinclude : Function.Injective stageEmbedding := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LStageCarrier alpha => z.1) hxy
  change IsWellOrder (InternalCarrier a)
    (InvImage (stageGraphRel r alpha) stageEmbedding)
  letI : IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha) := hr
  exact
    { wf := InvImage.wf stageEmbedding
        (IsWellFounded.wf : WellFounded (stageGraphRel r alpha))
      trichotomous :=
        (InvImage.trichotomous (r := stageGraphRel r alpha)
          hinclude).trichotomous }

/-- Internally represented well-orders of all levels give them for all sets. -/
theorem modelsInternalWellOrdering_of_allStages
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    ModelsInternalWellOrdering.{u} := by
  intro a
  rcases exists_LStage_for_constructible_members a.2 with
    ⟨alpha, halpha⟩
  rcases hstage alpha with ⟨r, hr⟩
  exact ⟨r, internallyWellOrders_of_stage halpha hr⟩

/-- Stage graph internalization is sufficient for Choice in `L`. -/
theorem lCarrier_modelsChoice_of_allStagesInternallyWellOrdered
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    FirstOrder.SetTheory.ModelsChoice LCarrier.{u} :=
  lCarrier_modelsChoice_of_internalWellOrdering
    (modelsInternalWellOrdering_of_allStages hstage)

/-- Stage graph internalization is sufficient for the ZFC model theorem. -/
theorem lCarrier_models_ZFC_of_allStagesInternallyWellOrdered
    (hstage : AllStagesInternallyWellOrdered.{u}) :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFC :=
  lCarrier_models_ZFC_of_internalWellOrdering
    (modelsInternalWellOrdering_of_allStages hstage)

/-! ## Alternative conditional birth-layer route

This section gives a conditional reduction through an externally specified
birth-layer order. The model theorem in `StageHistoryGraphSystem.lean` is
independent of this interface and constructs coherent internal graphs through
stage histories.
-/

/-- A constructible set is the graph of a specified external stage relation. -/
def HasConstructibleStageGraph (alpha : Ordinal.{u})
    (rel : LStageCarrier alpha -> LStageCarrier alpha -> Prop) : Prop :=
  exists r : LCarrier.{u}, forall x y : LStageCarrier alpha,
    stageGraphRel r alpha x y ↔ rel x y

/-- A well-order with a constructible graph gives an internal stage order. -/
theorem stageInternallyWellOrdered_of_hasConstructibleGraph
    {alpha : Ordinal.{u}}
    {rel : LStageCarrier alpha -> LStageCarrier alpha -> Prop}
    (hrel : IsWellOrder (LStageCarrier alpha) rel)
    (hgraph : HasConstructibleStageGraph alpha rel) :
    StageInternallyWellOrdered alpha := by
  rcases hgraph with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have heq : stageGraphRel r alpha = rel := by
    funext x y
    exact propext (hr x y)
  rw [heq]
  exact hrel

/--
For each level, choose local birth-layer orders and require the graph of the
resulting lexicographic stage order to be constructible. This proposition
encapsulates the internal-coding obligation for the birth-layer presentation.
-/
def BirthLayerOrdersHaveConstructibleGraphs : Prop :=
  forall alpha : Ordinal.{u},
    exists layerRel : forall beta : Set.Iio alpha,
        BornAt beta.1 -> BornAt beta.1 -> Prop,
      (forall beta, IsWellOrder (BornAt beta.1) (layerRel beta)) /\
      HasConstructibleStageGraph alpha
        (lStageBirthRel alpha layerRel)

/-- Internalized birth-layer orders yield internally well-ordered stages. -/
theorem allStagesInternallyWellOrdered_of_birthLayerGraphs
    (hgraphs : BirthLayerOrdersHaveConstructibleGraphs.{u}) :
    AllStagesInternallyWellOrdered.{u} := by
  intro alpha
  rcases hgraphs alpha with ⟨layerRel, hwell, hgraph⟩
  apply stageInternallyWellOrdered_of_hasConstructibleGraph
    (lStageBirthRel_isWellOrder alpha layerRel hwell) hgraph

/-- A birth-layer graph hypothesis implies that `L` satisfies the canonical ZFC theory. -/
theorem lCarrier_models_ZFC_of_birthLayerGraphs
    (hgraphs : BirthLayerOrdersHaveConstructibleGraphs.{u}) :
    LCarrier.{u} ⊨ FirstOrder.Language.Theory.ZFC :=
  lCarrier_models_ZFC_of_allStagesInternallyWellOrdered
    (allStagesInternallyWellOrdered_of_birthLayerGraphs hgraphs)

end Model

end Constructible
