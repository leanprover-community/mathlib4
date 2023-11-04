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

open Function Manifold TopologicalSpace Topology

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

/-! Pre-requisite results: the differential of a function is surjective/injective/a linear iso
  iff the differential of its coordinate representation (w.r.t. any charts) is.
  Already proven on a branch; just waiting for the most conceptual proof.

  Let `f: M → N` be `C^1` near `x`. For (extended) charts `φ` and `ψ` around `x` and `f x`,
  respectively, denote `f_loc := ψ ∘ f ∘ φ⁻¹`. We show that the differential `df_x` of `f`
  is injective, surjective resp. a linear isomorphism iff `(df_loc)_(φ x)` is. -/
section Prerequisites
-- xxx: for unextended charts, this doesn't make sense unless H is also a normed space
variable (hf : ContMDiffAt I J 1 f x)
  {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
  {e' : LocalHomeomorph N H} (he' : e' ∈ atlas H N)

/-- `df_x` is a linear isomorphism iff `(df_loc)_(φ x)` is a linear isomorphism.-/
-- part 1: isomorphism
def differential_in_charts_iso {dfx : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)}
    (hx : mfderiv I J f x = dfx) : E ≃L[ℝ] E' := sorry

-- part 2: this isomorphism is really the fderiv
lemma differential_in_charts_iso_coe {dfx : TangentSpace I x ≃L[ℝ] TangentSpace J (f x)}
    (hx : mfderiv I J f x = dfx) : (differential_in_charts_iso I J hx).toFun = fderiv ℝ ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x) := sorry

-- FIXME: add converse version, differential_iso_of_in_charts plus `coe` version
-- should follow easily from this one

/-- `df_x` is injective iff `(df_loc)_(φ x)` is injective.-/
lemma differential_injective_iff_in_charts : Injective (mfderiv I J f x) ↔ Injective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x)) := sorry

/-- `df_x` is surjective iff `(df_loc)_(φ x)` is sujective.-/
lemma diff_surjective_iff_in_charts_extend : Surjective (mfderiv I J f x) ↔ Surjective
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') ((e'.extend J) ∘ f ∘ (e.extend I).symm) ((e.extend I) x)) := sorry
end Prerequisites

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
