/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # The inverse function theorem for manifolds

TODO: write a docstring when I'm done

TODOs
* allow M and N to be modelled on different normed spaces (even if they must be isomorphic)
* don't assume M and N are smooth: the groupoid containing the C^1 groupoid suffices
* handle models with corners in my "charts are structomorphs" argument
-/

open Manifold TopologicalSpace Topology

-- Let M and N be manifolds over (E,H) and (E',H'), respectively.
-- We don't assume smoothness, but allow any structure groupoid (which contains C¹ maps).
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
   [TopologicalSpace N] [ChartedSpace H N]
  -- TODO: relax these conditions!!
  (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
  (J : ModelWithCorners ℝ E' H) [SmoothManifoldWithCorners J N]
  -- these lines are what I actually want
  --(I : ModelWithCorners ℝ E H) (G : StructureGroupoid H) [HasGroupoid M G]
  -- (J : ModelWithCorners ℝ E' H') (G' : StructureGroupoid H') [HasGroupoid N G']
  {f : M → N} {x : M}

-- inconsistent: HasFDerivAt f f' x vs HasMFDerivAt f x f'

-- Suppose G consists of C¹ maps, i.e. G\leq contDiffGroupoid n.
/-- Suppose `G` consists of `C^1` maps. Suppose `f:M → N` is `C^1` at `x` and
  the differential $df_x$ is a linear isomorphism.
  Then `x` and `f x` admit neighbourhoods `U ⊆ M` and `V ⊆ N`, respectively such that
  `f` is a structomorphism between `U` and `V`. -/
theorem IFT_manifolds [HasGroupoid M (contDiffGroupoid 1 I)]
    (G : StructureGroupoid H) [HasGroupoid M G]
    (hf : ContMDiffAt I J 1 f x) {f' : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)}
    (hf' : HasMFDerivAt I J f x f') :
    -- TODO: state the correct statement: h.toFun and f "are the same"
    ∃ U : Opens M, ∃ V : Opens N, ∃ h : Structomorph G U V, True /-(∀ x : U → h x = f x.1-/ := by
  sorry
