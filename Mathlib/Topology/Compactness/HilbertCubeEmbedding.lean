/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.MetricSpace.PiNat
/-!
# Every compact metric space can be embedded into the Hilbert cube.

In this file we prove `exists_closed_embedding_to_hilbert`: every compact metric space can be
embedded into the Hilbert cube (`ℕ → unitInterval`).
-/

/-- Every compact metric space can be embedded into the Hilbert cube. -/
theorem exists_closed_embedding_to_hilbert_cube (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ f : X → (ℕ → unitInterval), Topology.IsClosedEmbedding f := by
  obtain ⟨f,hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  use f
  exact Continuous.isClosedEmbedding (Topology.IsEmbedding.continuous hf) hf.injective
