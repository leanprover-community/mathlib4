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
class SpectralSpace : Prop where
  t0_space : T0Space α
  compact_space : CompactSpace α
  quasi_sober : QuasiSober α
  quasi_separated_space : QuasiSeparatedSpace α
  prespectral_space : PrespectralSpace α

namespace SpectralSpace

variable [SpectralSpace α]

instance t0Space : T0Space α := t0_space

instance compactSpace : CompactSpace α := compact_space

instance quasiSober : QuasiSober α := quasi_sober

instance quasiSeparatedSpace : QuasiSeparatedSpace α := quasi_separated_space

instance prespectralSpace : PrespectralSpace α := prespectral_space

end SpectralSpace
