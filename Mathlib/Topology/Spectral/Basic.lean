/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Panagiotis Angelinos
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Spectral spaces

A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis. Prime spectra of commutative semirings are spectral spaces.

## Main Results

- `SpectralSpace` : Predicate for a topological space to be spectral.
- `Topology.IsOpenEmbedding.spectralSpace` : a compact open subspace of a spectral space is spectral

## References

See [stacks-project], tag 08YF for details.
-/

@[expose] public section

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/--
A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis.
-/
@[stacks 08YG]
class SpectralSpace (X : Type*) [TopologicalSpace X] : Prop extends
  T0Space X, CompactSpace X, QuasiSober X, QuasiSeparatedSpace X, PrespectralSpace X

theorem Topology.IsOpenEmbedding.spectralSpace
    [SpectralSpace Y] [CompactSpace X] (hf : IsOpenEmbedding f) :
    SpectralSpace X where
  __ := hf.quasiSober
  __ := hf.prespectralSpace
  __ := hf.quasiSeparatedSpace
  __ := hf.isEmbedding.t0Space
