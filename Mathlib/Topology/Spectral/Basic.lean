/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Spectral spaces

A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis. Prime spectra of commutative semirings are spectral spaces.
-/

@[expose] public section

variable (α : Type*) [TopologicalSpace α]

/--
A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis.
-/
@[stacks 08YG]
class SpectralSpace : Prop extends
  T0Space α, CompactSpace α, QuasiSober α, QuasiSeparatedSpace α, PrespectralSpace α
