/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
public import Mathlib.Topology.DiscreteSubset

/-!
# Theorems combining measure theory and topology

This file gathers theorems that combine measure theory and topology, and cannot easily be added to
the existing files without introducing massive dependencies between the subjects.
-/

@[expose] public section
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
