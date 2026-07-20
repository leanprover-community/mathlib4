/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.InitialSegmentOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentarySuccessorInternalOrder

/-!
# Coherent internally represented successor-stage orders

The raw least-program order need not extend the order on the previous stage.
For limit unions we instead put the old stage first, preserving its given
relation, and order only the genuinely new values by least successful
programs.  The old stage is therefore an initial segment by construction.
-/

@[expose] public section

universe u

namespace Constructible

namespace Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The fixed extension formula -/

/-- The universe parameter in the seventeen-coordinate layout. -/
def successorUniverseIndex : Fin 17 :=
  (0 : Fin 13).castSucc.castSucc.castSucc.castSucc

/-- The inherited relation parameter in the seventeen-coordinate layout. -/
def successorRelationIndex : Fin 17 :=
  (Fin.last 14).castSucc.castSucc

/-- The left compared value in the seventeen-coordinate layout. -/
def successorLeftIndex : Fin 17 :=
  (Fin.last 15).castSucc

/-- The right compared value in the seventeen-coordinate layout. -/
def successorRightIndex : Fin 17 :=
  Fin.last 16

/-- Select `[relation, left, right]` from the seventeen-coordinate layout. -/
def successorRelationGraphRename : Fin 3 -> Fin 17 :=
  ![successorRelationIndex, successorLeftIndex, successorRightIndex]

theorem comp_successorRelationGraphRename
    (U relation left right : LCarrier.{u}) :
    (fun i =>
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right (successorRelationGraphRename i)) =
      ![relation, left, right] := by
  funext i
  fin_cases i <;> rfl

/--
On `Def(U)`, preserve `relation` on old values, put every old value before
every new value, and compare two new values by least successful programs.
-/
def successorExtensionLtFormula : FOFormula 17 :=
  let leftInU : FOFormula 17 :=
    .mem successorLeftIndex successorUniverseIndex
  let rightInU : FOFormula 17 :=
    .mem successorRightIndex successorUniverseIndex
  let oldGraph : FOFormula 17 :=
    FOFormula.rename successorRelationGraphRename graphRelFormula
  FOFormula.disj
    (.conj leftInU (.conj rightInU oldGraph))
    (FOFormula.disj
      (.conj leftInU (.neg rightInU))
      (.conj (.neg leftInU)
        (.conj (.neg rightInU)
          Godel.RudimentaryTerm.leastProgramValueLtFormula)))

@[simp]
theorem satisfies_successorExtensionLtFormula
    (U relation left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem successorExtensionLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          U relation left right) ↔
      (left.1 ∈ U.1 ∧ right.1 ∈ U.1 ∧
          GraphRel relation left right) ∨
      (left.1 ∈ U.1 ∧ right.1 ∉ U.1) ∨
      (left.1 ∉ U.1 ∧ right.1 ∉ U.1 ∧
        FOFormula.Satisfies LMem
          Godel.RudimentaryTerm.leastProgramValueLtFormula
          (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
            U relation left right)) := by
  have hUCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorUniverseIndex = U := by
    simp [successorUniverseIndex,
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      Godel.RudimentaryTerm.stackStepPrefixLAssignment]
  have hleftCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorLeftIndex = left := by
    change snoc
      (snoc
        (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
          U relation) left) right (Fin.last 15).castSucc = left
    rw [snoc_castSucc, snoc_last]
  have hrightCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorRightIndex = right := by
    change snoc
      (snoc
        (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
          U relation) left) right (Fin.last 16) = right
    rw [snoc_last]
  simp only [successorExtensionLtFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    comp_successorRelationGraphRename, satisfies_graphRelFormula,
    hUCoord, hleftCoord, hrightCoord]
  rfl

/-! ## The corresponding external block order -/

/-- The predicate identifying the old part of the successor carrier. -/
def successorIsOld (alpha : Ordinal.{u})
    (x : InternalCarrier (stageLCarrier (Order.succ alpha))) : Prop :=
  x.1.1 ∈ LStageZF alpha

/-- The old block is canonically the internal carrier of `L_alpha`. -/
def successorOldPartEquiv (alpha : Ordinal.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} ≃
      InternalCarrier (stageLCarrier alpha) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, LStageZF_subset_succ alpha x.2⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The old block uses exactly the supplied internal graph relation. -/
def successorOldBlockRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} ->
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} -> Prop :=
  InvImage (graphRelOn relation (stageLCarrier alpha))
    (successorOldPartEquiv alpha)

/-- The new block is the restriction of the successful-program order. -/
def successorNewBlockRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      Not (successorIsOld alpha x)} ->
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      Not (successorIsOld alpha x)} -> Prop :=
  InvImage
    (Godel.RudimentaryTerm.successfulProgramValueRel
      (LStageZF alpha) relation.1)
    (fun x => successorDefCarrierEquiv alpha x.1)

/-- The coherent old-before-new relation on the successor carrier. -/
def successorExtensionRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    InternalCarrier (stageLCarrier (Order.succ alpha)) ->
      InternalCarrier (stageLCarrier (Order.succ alpha)) -> Prop :=
  partitionLexRel (successorIsOld alpha)
    (successorOldBlockRel alpha relation)
    (successorNewBlockRel alpha relation)

theorem successorOldBlockRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        successorIsOld alpha x}
      (successorOldBlockRel alpha relation) := by
  letI : IsWellOrder (InternalCarrier (stageLCarrier alpha))
      (graphRelOn relation (stageLCarrier alpha)) := hwell
  exact
    { wf := InvImage.wf (successorOldPartEquiv alpha)
        (IsWellFounded.wf : WellFounded
          (graphRelOn relation (stageLCarrier alpha)))
      trichotomous :=
        (InvImage.trichotomous
          (r := graphRelOn relation (stageLCarrier alpha))
          (successorOldPartEquiv alpha).injective).trichotomous }

theorem successorNewBlockRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        Not (successorIsOld alpha x)}
      (successorNewBlockRel alpha relation) := by
  letI : IsWellOrder (Godel.DefCarrier (LStageZF alpha))
      (Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1) :=
    Godel.RudimentaryTerm.successfulProgramValueRel_isWellOrder_of_internal
      (stageLCarrier alpha) relation hwell
  let embedding :
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        Not (successorIsOld alpha x)} ->
        Godel.DefCarrier (LStageZF alpha) :=
    fun x => successorDefCarrierEquiv alpha x.1
  have hinjective : Function.Injective
      embedding := by
    intro x y hxy
    apply Subtype.ext
    exact (successorDefCarrierEquiv alpha).injective hxy
  change IsWellOrder _ (InvImage
    (Godel.RudimentaryTerm.successfulProgramValueRel
      (LStageZF alpha) relation.1) embedding)
  exact
    { wf := InvImage.wf
        embedding
        (IsWellFounded.wf : WellFounded
          (Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1))
      trichotomous :=
        (InvImage.trichotomous
          (r := Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1)
          hinjective).trichotomous }

theorem successorExtensionRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (successorExtensionRel alpha relation) := by
  letI := successorOldBlockRel_isWellOrder alpha relation hwell
  letI := successorNewBlockRel_isWellOrder alpha relation hwell
  exact partitionLexRel_isWellOrder
    (successorIsOld alpha)
    (successorOldBlockRel alpha relation)
    (successorNewBlockRel alpha relation)

/-! ## Formula semantics and internalization -/

private theorem successorLeastFormula_iff_successful
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (x y : InternalCarrier (stageLCarrier (Order.succ alpha))) :
    FOFormula.Satisfies LMem
        Godel.RudimentaryTerm.leastProgramValueLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          (stageLCarrier alpha) relation x.1 y.1) ↔
      Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1
        (successorDefCarrierEquiv alpha x)
        (successorDefCarrierEquiv alpha y) := by
  let U := stageLCarrier alpha
  let xL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha x)
  let yL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha y)
  have hxL : x.1 = xL := by
    apply Subtype.ext
    rfl
  have hyL : y.1 = yL := by
    apply Subtype.ext
    rfl
  rw [hxL, hyL]
  exact
    Godel.RudimentaryTerm.satisfies_leastProgramValueLtFormula_lCarrier_iff_successful
      U relation (successorDefCarrierEquiv alpha x)
        (successorDefCarrierEquiv alpha y)

theorem successorExtensionFormulaRel_eq
    (alpha : Ordinal.{u}) (relation : LCarrier.{u}) :
    formulaRelOn successorExtensionLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha)) =
      successorExtensionRel alpha relation := by
  funext x y
  apply propext
  change
    FOFormula.Satisfies LMem successorExtensionLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          (stageLCarrier alpha) relation x.1 y.1) ↔
      successorExtensionRel alpha relation x y
  rw [satisfies_successorExtensionLtFormula]
  by_cases hx : successorIsOld alpha x
  · by_cases hy : successorIsOld alpha y
    · have hxRaw : x.1.1 ∈ LStageZF alpha := hx
      have hyRaw : y.1.1 ∈ LStageZF alpha := hy
      rw [successorExtensionRel,
        partitionLexRel_old_old (successorIsOld alpha)
          (successorOldBlockRel alpha relation)
          (successorNewBlockRel alpha relation) hx hy]
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧
            GraphRel relation x.1 y.1) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        GraphRel relation x.1 y.1
      simp [hxRaw, hyRaw]
    · have hxRaw : x.1.1 ∈ LStageZF alpha := hx
      have hyRaw : y.1.1 ∉ LStageZF alpha := hy
      have hrel := partitionLexRel_old_new
        (successorIsOld alpha)
        (successorOldBlockRel alpha relation)
        (successorNewBlockRel alpha relation) hx hy
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        successorExtensionRel alpha relation x y
      simp [hxRaw, hyRaw]
      simpa only [successorExtensionRel] using hrel
  · by_cases hy : successorIsOld alpha y
    · have hxRaw : x.1.1 ∉ LStageZF alpha := hx
      have hyRaw : y.1.1 ∈ LStageZF alpha := hy
      have hrel := partitionLexRel_new_old
        (successorIsOld alpha)
        (successorOldBlockRel alpha relation)
        (successorNewBlockRel alpha relation) hx hy
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        successorExtensionRel alpha relation x y
      simp [hxRaw, hyRaw]
      simpa only [successorExtensionRel] using hrel
    · have hxRaw : x.1.1 ∉ LStageZF alpha := hx
      have hyRaw : y.1.1 ∉ LStageZF alpha := hy
      rw [successorLeastFormula_iff_successful]
      rw [successorExtensionRel,
        partitionLexRel_new_new (successorIsOld alpha)
          (successorOldBlockRel alpha relation)
          (successorNewBlockRel alpha relation) hx hy]
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧
            Godel.RudimentaryTerm.successfulProgramValueRel
              (LStageZF alpha) relation.1
              (successorDefCarrierEquiv alpha x)
              (successorDefCarrierEquiv alpha y))) ↔
        Godel.RudimentaryTerm.successfulProgramValueRel
          (LStageZF alpha) relation.1
          (successorDefCarrierEquiv alpha x)
          (successorDefCarrierEquiv alpha y)
      simp [hxRaw, hyRaw]

theorem successorExtensionFormulaRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (formulaRelOn successorExtensionLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha))) := by
  rw [successorExtensionFormulaRel_eq]
  exact successorExtensionRel_isWellOrder alpha relation hwell

/-- The data retained from a coherent successor-stage graph. -/
structure SuccessorOrderExtension (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) where
  /-- The relation extending the well-order to the successor stage. -/
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation
    (stageLCarrier (Order.succ alpha))
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y ->
    x.1 ∈ LStageZF (Order.succ alpha) ∧
      y.1 ∈ LStageZF (Order.succ alpha)
  agreesOnOld : ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF alpha -> y.1 ∈ LStageZF alpha ->
      (GraphRel nextRelation x y ↔ GraphRel relation x y)
  oldIsInitial : ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF alpha ->
      y.1 ∈ LStageZF (Order.succ alpha) ->
        GraphRel nextRelation y x -> y.1 ∈ LStageZF alpha

/-- Separation produces a supported graph which extends the old relation and
makes the old stage an initial segment. -/
theorem exists_successorOrderExtension
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    Nonempty (SuccessorOrderExtension alpha relation) := by
  rcases exists_definableRelationGraph successorExtensionLtFormula
      (successorProgramOrderParameters alpha relation)
      (stageLCarrier (Order.succ alpha)) with
    ⟨nextRelation, hgraph⟩
  have hnextWell :
      InternallyWellOrders nextRelation
        (stageLCarrier (Order.succ alpha)) := by
    have heq :
        graphRelOn nextRelation (stageLCarrier (Order.succ alpha)) =
          formulaRelOn successorExtensionLtFormula
            (successorProgramOrderParameters alpha relation)
            (stageLCarrier (Order.succ alpha)) := by
      funext x y
      apply propext
      have hxy := hgraph x.1 y.1
      simpa only [graphRelOn, formulaRelOn, x.2, y.2,
        true_and] using hxy
    rw [InternallyWellOrders, heq]
    exact successorExtensionFormulaRel_isWellOrder alpha relation hwell
  refine ⟨{
    nextRelation := nextRelation
    wellOrders := hnextWell
    supported := ?_
    agreesOnOld := ?_
    oldIsInitial := ?_ }⟩
  · intro x y hxy
    have hsupported := (hgraph x y).mp hxy
    exact ⟨hsupported.1, hsupported.2.1⟩
  · intro x y hx hy
    have hxSucc : x.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hx
    have hySucc : y.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hy
    have hsem :
        FOFormula.Satisfies LMem successorExtensionLtFormula
            (snoc (snoc (successorProgramOrderParameters alpha relation) x) y) ↔
          GraphRel relation x y := by
      change
        FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x y) ↔
          GraphRel relation x y
      rw [satisfies_successorExtensionLtFormula]
      simp only [stageLCarrier_val, hx, hy, true_and, not_true,
        and_false, false_and, or_false]
    rw [hgraph]
    simp only [stageLCarrier_val, hxSucc, hySucc, true_and]
    exact hsem
  · intro x y hx hySucc hyx
    have hxSucc : x.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hx
    rcases (hgraph y x).mp hyx with ⟨_hyDomain, _hxDomain, hformula⟩
    have hformula' :
        FOFormula.Satisfies LMem successorExtensionLtFormula
          (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
            (stageLCarrier alpha) relation y x) := by
      exact hformula
    rcases (satisfies_successorExtensionLtFormula
        (stageLCarrier alpha) relation y x).mp hformula' with
      hold | hold | hnew
    · exact hold.1
    · exact hold.1
    · exact (hnew.2.1 hx).elim

/-- The coherent successor relation has an actual constructible graph. -/
theorem exists_internalWellOrder_successorStage_extending
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    ∃ nextRelation : LCarrier.{u},
      InternallyWellOrders nextRelation
        (stageLCarrier (Order.succ alpha)) := by
  rcases exists_successorOrderExtension alpha relation hwell with ⟨next⟩
  exact ⟨next.nextRelation, next.wellOrders⟩

end

end Model

end Constructible
