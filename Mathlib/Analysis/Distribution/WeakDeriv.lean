/-
Copyright (c) 2025 Filippo A. E. Nuccio, Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Michael Rothgang
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Weak derivatives of distributions
-/

@[expose] public section

-- Now the fun starts.


open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace TestFunction
open scoped BoundedContinuousFunction NNReal Topology Distributions

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] --[RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    -- [NormedSpace 𝕂 F]
  {n : ℕ∞}

-- We might want to let `g` be a distr on some `Ω' ≠ Ω`. And do we want to define iterated Weak der?
-- def HasWeakDeriv (f : 𝓓^{n + 1}(Ω, F) →L[ℝ] F) (g : 𝓓^{n}(Ω, E [×1]→L[ℝ] F) →L[ℝ] F) : Prop :=
--   ∀ φ : 𝓓^{n + 1}(Ω, F), f φ = - g (iteratedFDerivWithOrderLM 𝕜 (n+1) n 1 φ)
