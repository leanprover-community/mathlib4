/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang, Oliver Nash
-/
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Profinite

/-!
# Further separation lemmas
-/

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
