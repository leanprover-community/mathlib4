import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff
open Topology

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  {H H' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E₁ H} {I' : ModelWithCorners 𝕜 E₂ H'}
  {J : ModelWithCorners 𝕜 E₃ G} {J' : ModelWithCorners 𝕜 E₄ G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

namespace IsSmoothEmbedding

variable {f g : M → N}

-- use IsImmersion.comp and IsEmbedding.comp
/-- The composition of two smooth embeddings between Banach manifolds is a smooth embedding. -/
proof_wanted comp -- [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
    {g : N → N'} (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J' n (g ∘ f)

end IsSmoothEmbedding

-- TODO: prove the same result for local diffeomorphisms and deduce it as a corollary
proof_wanted Diffeomorph.isSmoothEmbedding [IsManifold I n M]
    (φ : Diffeomorph I I M M n) : IsSmoothEmbedding I I n φ

end Manifold
