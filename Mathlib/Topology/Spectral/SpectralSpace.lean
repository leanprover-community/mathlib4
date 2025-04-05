/-
Copyright (c) 2025 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Prespectral

/-!
# Spectral spaces

A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis. Prime spectrums of commutative semirings are spectral spaces.
-/

open TopologicalSpace Topology

variable (α : Type*) [TopologicalSpace α]

/--
A topological space is spectral if it is T0, compact, sober, quasi-separated, and its compact open
subsets form an open basis.
-/
class SpectralSpace : Prop extends
  T0Space α, CompactSpace α, QuasiSober α, QuasiSeparatedSpace α, PrespectralSpace α
