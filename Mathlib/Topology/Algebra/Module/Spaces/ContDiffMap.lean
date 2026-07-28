/-
Copyright (c) 2026 Cameron Beeley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Beeley
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# The compact-open C-infinity topology on smooth maps

For maps between normed spaces, the compact-open C-infinity topology is the
initial topology for all iterated derivatives, where each derivative is given
the topology of uniform convergence on compact subsets.

This file defines the corresponding type of smooth maps and its topology.
The manifold version requires additional chart-domain bookkeeping and is not
part of this construction.
-/

open Set
open scoped ContDiff

@[expose] public section

namespace SmoothMap

noncomputable section

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Smooth maps between normed spaces, bundled with their smoothness proof. -/
def ContDiffMap (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  {f : E → F // ContDiff 𝕜 ∞ f}

instance : FunLike (ContDiffMap 𝕜 E F) E F where
  coe f := f.1
  coe_injective f g h := by exact Subtype.ext h

/-- The family of compact subsets used by compact-open convergence. -/
def compactSets (E : Type*) [TopologicalSpace E] : Set (Set E) :=
  {K | IsCompact K}

/-- The full iterated-derivative jet of a smooth map. -/
def jet (f : ContDiffMap 𝕜 E F) :
    ∀ k : ℕ, UniformOnFun E
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) (compactSets E) :=
  fun k => UniformOnFun.ofFun (compactSets E) (iteratedFDeriv 𝕜 k f)

/-- The compact-open C-infinity topology on smooth maps between normed spaces. -/
@[instance_reducible]
def topology : TopologicalSpace (ContDiffMap 𝕜 E F) :=
  TopologicalSpace.induced jet
    (inferInstance : TopologicalSpace
      (∀ k : ℕ, UniformOnFun E
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) (compactSets E)))

instance : TopologicalSpace (ContDiffMap 𝕜 E F) := topology

@[simp]
theorem jet_apply (f : ContDiffMap 𝕜 E F) (k : ℕ) :
    (jet f k : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) =
      iteratedFDeriv 𝕜 k f :=
  rfl

end
end SmoothMap
