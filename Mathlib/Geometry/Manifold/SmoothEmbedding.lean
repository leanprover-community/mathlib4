/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-! # Smooth embeddings

In this file, we define `C^n` embeddings between `C^n` manifolds.
This will be useful to define embedded submanifolds.

## Main definitions and results

* `IsSmoothEmbedding I J n f` means `f : M → N` is a `C^n` embedding:
  it is both a `C^n` immersion and a topological embedding
* `IsSmoothEmbedding.prodMap`: the product of two smooth embeddings is a smooth embedding

## Implementation notes

* Unlike immersions, being an embedding is a global notion: this is why we have no definition
`IsSmoothEmbeddingAt`. (Besides, it would be equivalent to being an immersion at `x`.)
* Note that being a smooth embedding is a stronger condition than being a smooth map
  which is a topological embedding.

## TODO
* `IsSmoothEmbedding.contMDiff`: if `f` is a smooth embedding, it is `C^n`.
* `IsSmoothEmbedding.comp`: the composition of smooth embeddings (between Banach manifolds)
  is a smooth embedding

-/

open scoped ContDiff
open Function Set Topology Manifold

@[expose] public section

noncomputable section

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' E''' F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (I J n) in
/-- A `C^k` map `f : M → M'` is a smooth `C^k` embedding if it is a topological embedding
and a `C^k` immersion. -/
@[mk_iff]
structure IsSmoothEmbedding (f : M → N) where
  isImmersion : IsImmersion I J n f
  isEmbedding : IsEmbedding f

namespace IsSmoothEmbedding

variable {f g : M → N}

-- combine isImmersion with `hf.isImmersion.contMDiff` (once proven)
proof_wanted contMDiff (hf : IsSmoothEmbedding I J n f) : ContMDiff I J n f

/-- If `f: M → N` and `g: M' × N'` are smooth embeddings, respectively,
then so is `f × g: M × M' → N × N'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSmoothEmbedding I J n f) (hg : IsSmoothEmbedding I' J' n g) :
    IsSmoothEmbedding (I.prod I') (J.prod J') n (Prod.map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

-- use IsImmersion.comp and IsEmbedding.comp
/-- The composition of two smooth embeddings between Banach manifolds is a smooth embedding. -/
proof_wanted comp -- [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']
    {g : N → N'} (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J' n (g ∘ f)

end IsSmoothEmbedding

end Manifold
