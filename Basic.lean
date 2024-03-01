/-
Copyright (c) 2024 Panagiotis Angelinos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Panagiotis Angelinos
-/

import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Sober

/-!
# Spectral Spaces
This file defines spectral spaces. A topological space is spectral if it is sober,
quasi-compact, the intersection of two quasi-compact opens is quasi-compact, and
the collection of quasi-compact opens forms a basis for the topology.

## Main Results

- `SpectralSpace` : Predicate for a topological space to be spectral.
- `compact_openEmbedding_of_SpectralSpace_is_SpectralSpace` : proof that a compact open subspace
    of a spectral space is spectral

## Notation

- None so far.

## References
See the [StacksProject], tag 08YF for details.

-/

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y)

/-- Let X be an open subspace of a topological space Y. If the quasi-compact opens
of Y form a basis of Y, then the quasi-compact opens of X form a basis of X.-/
theorem openEmbedding_of_qcOpenBasis_has_qcOpenBasis (X Y: Type*) [TopologicalSpace X]
  [TopologicalSpace Y] (f: X → Y) (hf : OpenEmbedding f)
  (hYb: TopologicalSpace.IsTopologicalBasis {S : Set Y | IsOpen S ∧ IsCompact S}) :
  (TopologicalSpace.IsTopologicalBasis {S : Set X | IsOpen S ∧ IsCompact S}) := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      cases' hU with hoU hcU
      exact hoU
    · intro x S hx hS
      have hfS : IsOpen (f '' S) := by exact (OpenEmbedding.open_iff_image_open hf).mp hS
      apply (TopologicalSpace.IsTopologicalBasis.isOpen_iff hYb).mp at hfS
      specialize hfS (f x)
      have hxinhfS : f x ∈ f '' S := by exact Exists.intro x { left := hx, right := rfl }
      apply hfS at hxinhfS
      cases' hxinhfS with W hW
      cases' hW with hocW hdummyW
      cases' hocW with hoW hcW
      cases' hdummyW with hfxW hWfS
      use (f ⁻¹' W)
      constructor
      · constructor
        · have hfcont : Continuous f := by exact OpenEmbedding.continuous hf
          exact IsOpen.preimage hfcont hoW
        · apply Inducing.isCompact_preimage'
          exact hf.toInducing
          exact hcW
          exact Set.SurjOn.subset_range hWfS
      constructor
      · exact hfxW
      · have hemb : Embedding f := by exact hf.toEmbedding
        cases' hemb with hind hinj
        intro y hy
        exact (Function.Injective.mem_set_image hinj).mp (hWfS hy)

/-- This defines a spectral space as a sober (i.e. quasi-sober and T0), (quasi)-compact,
quasi-separated topological space such that all quasi-compact opens form a basis-/
class SpectralSpace (X : Type*) [TopologicalSpace X] extends CompactSpace X,
    QuasiSober X, QuasiSeparatedSpace X, T0Space X : Prop where
  qc_open_basis: TopologicalSpace.IsTopologicalBasis {S : Set X | IsOpen S ∧ IsCompact S}

theorem compact_openEmbedding_of_SpectralSpace_is_SpectralSpace [TopologicalSpace X]
  [SpectralSpace Y] (hf: OpenEmbedding f) (hX: CompactSpace X) :
  SpectralSpace X where
    isCompact_univ := by exact isCompact_univ
    sober := by
      have h1: QuasiSober Y := by exact SpectralSpace.toQuasiSober
      apply OpenEmbedding.quasiSober at hf
      exact fun {S} a a_1 ↦ QuasiSober.sober a a_1
    inter_isCompact := by
      have hY : QuasiSeparatedSpace Y := by exact SpectralSpace.toQuasiSeparatedSpace
      have hYuniv : IsQuasiSeparated (Set.univ : Set Y) := by exact isQuasiSeparated_univ
      have hsub : (f '' (Set.univ : Set X)) ⊆ (Set.univ : Set Y) := by exact fun ⦃a⦄ a ↦ trivial
      have hfuniv : IsQuasiSeparated (f '' (Set.univ : Set X)) := by exact
        (IsQuasiSeparated.of_subset hYuniv hsub)
      have hXiqs : IsQuasiSeparated (Set.univ : Set X) := by exact
        ((OpenEmbedding.isQuasiSeparated_iff hf).mpr hfuniv)
      have hXqs : QuasiSeparatedSpace X := by exact isQuasiSeparated_univ_iff.mp hXiqs
      exact fun U V a a_1 a_2 a_3 ↦ QuasiSeparatedSpace.inter_isCompact U V a a_1 a_2 a_3
    t0 := by
      have h1: T0Space Y := by exact SpectralSpace.toT0Space
      cases' hf with hfemb hfopen
      cases' hfemb with hfind hfinj
      rw [t0Space_iff_inseparable] at h1
      intro x y hins
      specialize h1 (f x) (f y)
      have hxy : Inseparable (f x) (f y) := by exact (Inducing.inseparable_iff hfind).mpr hins
      apply h1 at hxy
      exact hfinj (h1 (congrArg nhds hxy))
    qc_open_basis := by
      have hYb : TopologicalSpace.IsTopologicalBasis {S : Set Y | IsOpen S ∧ IsCompact S} := by
        exact SpectralSpace.qc_open_basis
      exact openEmbedding_of_qcOpenBasis_has_qcOpenBasis X Y f hf hYb
