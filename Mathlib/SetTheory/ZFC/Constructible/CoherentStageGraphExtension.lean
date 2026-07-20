/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.CanonicalSuccessorOrder
public import Mathlib.SetTheory.ZFC.Constructible.CoherentLimitOrder
public import Mathlib.SetTheory.ZFC.Constructible.StageZeroInternalOrder

/-!
# Adjoining one graph to a coherent stage system

Successor and limit constructions both produce a graph at one new ordinal,
together with support, agreement, and initial-segment facts relative to all
earlier stages.  This file packages that common interface and proves that
adjoining such a graph preserves the complete coherent-system invariant.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-- The data required to adjoin a graph at `alpha` to a system below
`alpha`. -/
structure StageGraphExtension (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u}) where
  /-- The relation adjoined at the new stage. -/
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation (stageLCarrier alpha)
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y →
    x.1 ∈ LStageZF alpha ∧ y.1 ∈ LStageZF alpha
  agreesOnEarlier : ∀ beta : Set.Iio alpha, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF beta.1 →
      (GraphRel nextRelation x y ↔ GraphRel (graphs beta) x y)
  earlierIsInitial : ∀ beta : Set.Iio alpha, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF alpha →
      GraphRel nextRelation y x → y.1 ∈ LStageZF beta.1

/-- Extend a graph family below `alpha` by one value at `alpha`. -/
def appendStageGraph (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) :
    Set.Iio (Order.succ alpha) → LCarrier.{u} :=
  fun beta =>
    if hbeta : beta.1 < alpha then
      graphs ⟨beta.1, hbeta⟩
    else nextRelation

/-- The last index below `alpha + 1`. -/
def lastStageIndex (alpha : Ordinal.{u}) : Set.Iio (Order.succ alpha) :=
  ⟨alpha, Order.lt_succ alpha⟩

@[simp]
theorem lastStageIndex_val (alpha : Ordinal.{u}) :
    (lastStageIndex alpha).1 = alpha :=
  rfl

@[simp]
theorem appendStageGraph_last (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) :
    appendStageGraph alpha graphs nextRelation (lastStageIndex alpha) =
      nextRelation := by
  simp [appendStageGraph, lastStageIndex]

@[simp]
theorem appendStageGraph_earlier (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (nextRelation : LCarrier.{u}) (beta : Set.Iio alpha) :
    appendStageGraph alpha graphs nextRelation
        ⟨beta.1, lt_trans beta.2 (Order.lt_succ alpha)⟩ =
      graphs beta := by
  have hbeta : beta.1 < alpha := beta.2
  rw [appendStageGraph, dif_pos hbeta]

/-- Adjoining a valid extension preserves well-ordering, support, coherence,
and all earlier initial segments. -/
theorem coherentStageGraphSystem_append
    (alpha : Ordinal.{u})
    (graphs : Set.Iio alpha → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem alpha graphs)
    (extension : StageGraphExtension alpha graphs) :
    CoherentStageGraphSystem (Order.succ alpha)
      (appendStageGraph alpha graphs extension.nextRelation) := by
  refine
    { wellOrders := ?_
      supported := ?_
      coherent := ?_
      initial := ?_ }
  · intro beta
    by_cases hbeta : beta.1 < alpha
    · simpa only [appendStageGraph, dif_pos hbeta] using
        hsystem.wellOrders ⟨beta.1, hbeta⟩
    · have hbetaLe : beta.1 ≤ alpha :=
        Order.lt_succ_iff.mp beta.2
      have hbetaEq : beta.1 = alpha :=
        le_antisymm hbetaLe (le_of_not_gt hbeta)
      have happend :
          appendStageGraph alpha graphs extension.nextRelation beta =
            extension.nextRelation := by
        rw [appendStageGraph, dif_neg hbeta]
      rw [happend, hbetaEq]
      exact extension.wellOrders
  · intro beta x y hxy
    by_cases hbeta : beta.1 < alpha
    · have hxyEarlier :
          GraphRel (graphs ⟨beta.1, hbeta⟩) x y := by
        simpa only [appendStageGraph, dif_pos hbeta] using hxy
      exact hsystem.supported ⟨beta.1, hbeta⟩ x y hxyEarlier
    · have hbetaLe : beta.1 ≤ alpha :=
        Order.lt_succ_iff.mp beta.2
      have hbetaEq : beta.1 = alpha :=
        le_antisymm hbetaLe (le_of_not_gt hbeta)
      have hxyTop : GraphRel extension.nextRelation x y := by
        simpa only [appendStageGraph, dif_neg hbeta] using hxy
      simpa only [hbetaEq] using extension.supported x y hxyTop
  · intro beta gamma hbetaGamma x y hx hy
    by_cases hgamma : gamma.1 < alpha
    · have hbeta : beta.1 < alpha :=
        lt_of_le_of_lt hbetaGamma hgamma
      simpa only [appendStageGraph, dif_pos hbeta, dif_pos hgamma] using
        hsystem.coherent
          ⟨beta.1, hbeta⟩ ⟨gamma.1, hgamma⟩
          hbetaGamma x y hx hy
    · have hgammaLe : gamma.1 ≤ alpha :=
        Order.lt_succ_iff.mp gamma.2
      have hgammaEq : gamma.1 = alpha :=
        le_antisymm hgammaLe (le_of_not_gt hgamma)
      by_cases hbeta : beta.1 < alpha
      · simpa only [appendStageGraph, dif_pos hbeta, dif_neg hgamma] using
          extension.agreesOnEarlier ⟨beta.1, hbeta⟩ x y hx hy
      · simp only [appendStageGraph, dif_neg hbeta, dif_neg hgamma]
  · intro beta gamma hbetaGamma x y hx hy hgraph
    by_cases hgamma : gamma.1 < alpha
    · have hbeta : beta.1 < alpha :=
        lt_of_le_of_lt hbetaGamma hgamma
      have hgraphEarlier :
          GraphRel (graphs ⟨gamma.1, hgamma⟩) y x := by
        simpa only [appendStageGraph, dif_pos hgamma] using hgraph
      exact hsystem.initial
        ⟨beta.1, hbeta⟩ ⟨gamma.1, hgamma⟩
        hbetaGamma x y hx hy hgraphEarlier
    · have hgammaLe : gamma.1 ≤ alpha :=
        Order.lt_succ_iff.mp gamma.2
      have hgammaEq : gamma.1 = alpha :=
        le_antisymm hgammaLe (le_of_not_gt hgamma)
      by_cases hbeta : beta.1 < alpha
      · have hgraphTop : GraphRel extension.nextRelation y x := by
          simpa only [appendStageGraph, dif_neg hgamma] using hgraph
        have hyTop : y.1 ∈ LStageZF alpha := by
          simpa only [hgammaEq] using hy
        exact extension.earlierIsInitial
          ⟨beta.1, hbeta⟩ x y hx hyTop hgraphTop
      · have hbetaLe : beta.1 ≤ alpha :=
          hbetaGamma.trans hgammaLe
        have hbetaEq : beta.1 = alpha :=
          le_antisymm hbetaLe (le_of_not_gt hbeta)
        simpa only [hbetaEq, hgammaEq] using hy

/-- A coherent constructible union at a limit is a generic stage
extension. -/
def LimitOrderExtension.toStageGraphExtension
    {limit : Ordinal.{u}} {graphs : Set.Iio limit → LCarrier.{u}}
    (extension : LimitOrderExtension limit graphs) :
    StageGraphExtension limit graphs where
  nextRelation := extension.nextRelation
  wellOrders := extension.wellOrders
  supported := extension.supported
  agreesOnEarlier := extension.agreesOnEarlier
  earlierIsInitial := extension.earlierIsInitial

/-- The represented union construction in the generic extension form. -/
def coherentLimitStageGraphExtension
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    StageGraphExtension limit graphs :=
  (coherentLimitOrderExtension hl graphs hsystem family hfamily).toStageGraphExtension

/-! ## The zero and successor extensions -/

theorem false_of_mem_Iio_zero
    (beta : Set.Iio (0 : Ordinal.{u})) : False := by
  exact (not_lt_of_ge bot_le) (Set.mem_Iio.mp beta.2)

/-- There are no stage indices below zero. -/
def emptyStageGraphFamily :
    Set.Iio (0 : Ordinal.{u}) → LCarrier.{u} :=
  fun beta => (false_of_mem_Iio_zero beta).elim

/-- The vacuous coherent system below zero. -/
theorem emptyCoherentStageGraphSystem :
    CoherentStageGraphSystem (0 : Ordinal.{u}) emptyStageGraphFamily where
  wellOrders := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim
  supported := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim
  coherent := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim
  initial := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim

/-- The empty graph is a valid extension at stage zero. -/
def zeroStageGraphExtension :
    StageGraphExtension (0 : Ordinal.{u}) emptyStageGraphFamily where
  nextRelation := emptyLCarrier
  wellOrders := by
    rw [InternallyWellOrders]
    refine
      { wf := WellFounded.intro (fun x => ?_)
        trichotomous := fun x => ?_ }
    · have hx : x.1.1 ∈ (∅ : ZFSet.{u}) := by
        simpa only [stageLCarrier_val, LStageZF_zero] using x.2
      exact (ZFSet.notMem_empty x.1.1 hx).elim
    · have hx : x.1.1 ∈ (∅ : ZFSet.{u}) := by
        simpa only [stageLCarrier_val, LStageZF_zero] using x.2
      exact (ZFSet.notMem_empty x.1.1 hx).elim
  supported := by
    intro x y hxy
    change ZFSet.pair x.1 y.1 ∈ (∅ : ZFSet.{u}) at hxy
    exact (ZFSet.notMem_empty _ hxy).elim
  agreesOnEarlier := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim
  earlierIsInitial := by
    intro beta
    exact (false_of_mem_Iio_zero beta).elim

/-- The coherent system containing exactly the zero-stage empty graph. -/
theorem zeroIncludedCoherentStageGraphSystem :
    CoherentStageGraphSystem (Order.succ (0 : Ordinal.{u}))
      (appendStageGraph 0 emptyStageGraphFamily
        zeroStageGraphExtension.nextRelation) :=
  coherentStageGraphSystem_append 0 emptyStageGraphFamily
    emptyCoherentStageGraphSystem zeroStageGraphExtension

/-- At a successor, the canonical formula graph extends the top graph of the
existing system and hence agrees with every earlier graph. -/
def canonicalSuccessorStageGraphExtension
    (alpha : Ordinal.{u})
    (graphs : Set.Iio (Order.succ alpha) → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem (Order.succ alpha) graphs) :
    StageGraphExtension (Order.succ alpha) graphs := by
  let top : Set.Iio (Order.succ alpha) := lastStageIndex alpha
  let previous : LCarrier.{u} := graphs top
  have hprevious :
      InternallyWellOrders previous (stageLCarrier alpha) := by
    simpa only [previous, top, lastStageIndex_val] using
      hsystem.wellOrders top
  let next := canonicalSuccessorOrderExtension alpha previous hprevious
  refine
    { nextRelation := next.nextRelation
      wellOrders := next.wellOrders
      supported := next.supported
      agreesOnEarlier := ?_
      earlierIsInitial := ?_ }
  · intro beta x y hx hy
    have hbetaAlpha : beta.1 ≤ alpha :=
      Order.lt_succ_iff.mp beta.2
    have hxAlpha : x.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hx
    have hyAlpha : y.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hy
    exact (next.agreesOnOld x y hxAlpha hyAlpha).trans
      (hsystem.coherent beta top hbetaAlpha x y hx hy)
  · intro beta x y hx hy hyx
    have hbetaAlpha : beta.1 ≤ alpha :=
      Order.lt_succ_iff.mp beta.2
    have hxAlpha : x.1 ∈ LStageZF alpha :=
      LStageZF_mono hbetaAlpha hx
    have hyAlpha : y.1 ∈ LStageZF alpha :=
      next.oldIsInitial x y hxAlpha hy hyx
    have hyxPrevious : GraphRel previous y x :=
      (next.agreesOnOld y x hyAlpha hxAlpha).mp hyx
    exact hsystem.initial beta top hbetaAlpha x y
      hx hyAlpha hyxPrevious

/-- Appending the canonical successor graph preserves the coherent system. -/
theorem appendCanonicalSuccessorStageGraphSystem
    (alpha : Ordinal.{u})
    (graphs : Set.Iio (Order.succ alpha) → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem (Order.succ alpha) graphs) :
    CoherentStageGraphSystem (Order.succ (Order.succ alpha))
      (appendStageGraph (Order.succ alpha) graphs
        (canonicalSuccessorStageGraphExtension alpha graphs hsystem).nextRelation) :=
  coherentStageGraphSystem_append (Order.succ alpha) graphs hsystem
    (canonicalSuccessorStageGraphExtension alpha graphs hsystem)

end

end Constructible.Model
