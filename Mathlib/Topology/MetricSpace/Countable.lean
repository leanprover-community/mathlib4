/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Bryan Wang
-/
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Properties of countable metric spaces.

-/

open Function Set

variable {γ : Type*} [MetricSpace γ]

namespace Metric

section TotallyDisconnected

open Cardinal in
/-- Countable metric spaces are totally separated. -/
theorem totallySeparatedSpace_of_cardinalMk_lt_continuum
    (hγ : Cardinal.mk γ < continuum) :
    TotallySeparatedSpace γ := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  -- letI : CompletelyRegularSpace γ := ((t35Space_iff γ).mp inferInstance).2
  apply CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum hγ

/-- Countable subsets of metric spaces are totally disconnected. -/
theorem Countable.isTotallyDisconnected {s : Set γ} (hs : Countable s) :
    IsTotallyDisconnected s :=
  totallyDisconnectedSpace_subtype_iff.mp <|
    (totallySeparatedSpace_of_cardinalMk_lt_continuum <|
      (Countable.le_aleph0 hs).trans_lt Cardinal.aleph0_lt_continuum).totallyDisconnectedSpace

end TotallyDisconnected

end Metric
