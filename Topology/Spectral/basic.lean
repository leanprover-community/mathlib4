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

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

open TopologicalSpace

/-- Let X be an open subspace of a topological space Y. If the quasi-compact opens
of Y form a basis of Y, then the quasi-compact opens of X form a basis of X.-/
theorem OpenEmbedding.has_qcOpenBasis_of_qcOpenBasis (hf : OpenEmbedding f)
    (hYb : IsTopologicalBasis {S : Set Y | IsOpen S ∧ IsCompact S}) :
    IsTopologicalBasis {S : Set X | IsOpen S ∧ IsCompact S} := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.1) <| fun x S hx hS ↦ ?_
  obtain ⟨W, ⟨hoW, hcW⟩, ⟨hfx, hWf⟩⟩ : ∃ t ∈ {S | IsOpen S ∧ IsCompact S}, f x ∈ t ∧ t ⊆ f '' S :=
    hYb.isOpen_iff.mp (hf.open_iff_image_open.mp hS) (f x) ⟨x, hx, rfl⟩
  refine ⟨f ⁻¹' W, ⟨hoW.preimage hf.continuous, ?_⟩, ⟨hfx, fun y hy ↦ ?_⟩⟩
  · exact hf.toInducing.isCompact_preimage' hcW <| Set.SurjOn.subset_range hWf
  · exact hf.inj.mem_set_image.mp (hWf hy)

/-- This defines a spectral space as a sober (i.e. quasi-sober and T0), (quasi)-compact,
quasi-separated topological space such that all quasi-compact opens form a basis-/
class SpectralSpace (X : Type*) [TopologicalSpace X] extends CompactSpace X,
    QuasiSober X, QuasiSeparatedSpace X, T0Space X : Prop where
  qc_open_basis : IsTopologicalBasis {S : Set X | IsOpen S ∧ IsCompact S}

theorem compact_openEmbedding_of_SpectralSpace_is_SpectralSpace
    [SpectralSpace Y] [CompactSpace X] (hf : OpenEmbedding f) :
    SpectralSpace X where
  isCompact_univ := isCompact_univ
  sober {_} := QuasiSober.sober (self := hf.quasiSober)
  inter_isCompact :=
    have hsub : (f '' (Set.univ : Set X)) ⊆ (Set.univ : Set Y) := fun ⦃_⦄ _ ↦ Set.mem_univ _
    have hfuniv : IsQuasiSeparated (f '' (Set.univ : Set X)) := isQuasiSeparated_univ.of_subset hsub
    have hXiqs : IsQuasiSeparated (Set.univ : Set X) := hf.isQuasiSeparated_iff.mpr hfuniv
    have hXqs : QuasiSeparatedSpace X := isQuasiSeparated_univ_iff.mp hXiqs
    QuasiSeparatedSpace.inter_isCompact
  t0 x y hins :=
    have h1 := (t0Space_iff_inseparable Y).mp SpectralSpace.toT0Space (f x) (f y)
    hf.inj (h1 (hf.toInducing.inseparable_iff.mpr hins))
  qc_open_basis := hf.has_qcOpenBasis_of_qcOpenBasis SpectralSpace.qc_open_basis
