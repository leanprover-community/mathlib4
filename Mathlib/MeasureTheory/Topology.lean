/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorems combining measure theory and topology

This file gathers theorems that combine measure theory and topology, and cannot easily be added to
the existing files without introducing massive dependencies between the subjects.
-/

public section
open Filter MeasureTheory

/-- Under reasonable assumptions, sets that are codiscrete within `U` are contained in the "almost
everywhere" filter of co-null sets. -/
theorem ae_restrict_le_codiscreteWithin
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α]
    {μ : Measure α} [NoAtoms μ] {U : Set α} (hU : MeasurableSet U) :
    ae (μ.restrict U) ≤ codiscreteWithin U := by
  intro s hs
  have : DiscreteTopology ↑(sᶜ ∩ U) := isDiscrete_iff_discreteTopology.mp
    <| isDiscrete_of_codiscreteWithin ((compl_compl s).symm ▸ hs)
  rw [mem_ae_iff, Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)
