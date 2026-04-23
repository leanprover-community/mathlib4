/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang, Oliver Nash
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Separation.Profinite

/-!
# Further separation lemmas
-/

@[expose] public section

variable {X : Type*}

namespace CompletelyRegularSpace

variable [TopologicalSpace X] [T35Space X]

theorem totallySeparatedSpace_of_cardinalMk_lt_continuum (h : Cardinal.mk X < Cardinal.continuum) :
    TotallySeparatedSpace X :=
  totallySeparatedSpace_of_t0_of_basis_clopen <|
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum h

instance [Countable X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_of_cardinalMk_lt_continuum <|
    (Cardinal.mk_le_aleph0_iff.mpr inferInstance).trans_lt Cardinal.aleph0_lt_continuum

protected lemma _root_.Set.Countable.totallySeparatedSpace {s : Set X} (h : s.Countable) :
    TotallySeparatedSpace s :=
  have : _root_.Countable s := h
  inferInstanceAs (TotallySeparatedSpace s)

end CompletelyRegularSpace

/-- Countable subsets of metric spaces are totally disconnected. -/
theorem Set.Countable.isTotallyDisconnected [MetricSpace X] {s : Set X} (hs : s.Countable) :
    IsTotallyDisconnected s := by
  rw [← totallyDisconnectedSpace_subtype_iff]
  have : Countable s := hs
  infer_instance
