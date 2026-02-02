/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Diffeomorph  -- shake: keep (used in `proof_wanted` only)

/-! # Smooth embeddings

In this file, we define `C^n` embeddings between `C^n` manifolds.
This will be useful to define embedded submanifolds.

## Main definitions and results

* `IsSmoothEmbedding I J n f` means `f : M → N` is a `C^n` embedding:
  it is both a `C^n` immersion and a topological embedding
* `IsSmoothEmbedding.prodMap`: the product of two smooth embeddings is a smooth embedding
* `IsSmoothEmbedding.id`: the identity map is a smooth embedding
* `IsSmoothEmbedding.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth embedding
* `IsSmoothEmbedding.contMDiff`: if `f` is a `C^n` embedding, it is automatically `C^n`
  in the sense of `ContMDiff`.
* `IsSmoothEmbedding.comp`: the composition of smooth embeddings (between Banach manifolds)
  is a smooth embedding

## Implementation notes

* Unlike immersions, being an embedding is a global notion: this is why we have no definition
  `IsSmoothEmbeddingAt`. (Besides, it would be equivalent to being an immersion at `x`.)
* Note that being a smooth embedding is a stronger condition than being a smooth map
  which is a topological embedding. Even being a homeomorphism and a smooth map is not sufficient.
  See e.g. https://math.stackexchange.com/a/2583667 and
  https://math.stackexchange.com/a/3769328 for counterexamples.

## TODO
* `IsLocalDiffeomorph.isSmoothEmbedding`, `Diffeomorph.isSmoothEmbedding`:
  a local diffeomorphism (and in particular, a diffeomorphism) is a smooth embedding

-/

open scoped ContDiff
open Topology

@[expose] public section

noncomputable section

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
  {n : WithTop ℕ∞}

variable (I J n) in
/-- A `C^n` map `f : M → M'` is a smooth `C^n` embedding if it is a topological embedding
and a `C^n` immersion. -/
@[mk_iff]
structure IsSmoothEmbedding (f : M → N) where
  isImmersion : IsImmersion I J n f
  isEmbedding : IsEmbedding f

namespace IsSmoothEmbedding

variable {f g : M → N}

protected lemma id [IsManifold I n M] : IsSmoothEmbedding I I n (@id M) := ⟨.id, .id⟩

/-- If `f: M → N` and `g: M' × N'` are smooth embeddings, respectively,
then so is `f × g: M × M' → N × N'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSmoothEmbedding I J n f) (hg : IsSmoothEmbedding I' J' n g) :
    IsSmoothEmbedding (I.prod I') (J.prod J') n (Prod.map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩

/- The inclusion of an open subset `s` of a smooth manifold `M` is a smooth embedding. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsSmoothEmbedding I I n (Subtype.val : s → M) := by
  rw [isSmoothEmbedding_iff]
  exact ⟨IsImmersion.of_opens s, IsEmbedding.subtypeVal⟩

/-- A smooth embedding is automatically smooth. -/
lemma contMDiff [IsManifold I n M] [IsManifold J n N] (hf : IsSmoothEmbedding I J n f) :
    ContMDiff I J n f :=
  hf.isImmersion.contMDiff

/-- The composition of two smooth embeddings between Banach manifolds is a smooth embedding. -/
lemma comp [CompleteSpace E₁] [CompleteSpace E₃] [CompleteSpace E₄]
    [IsManifold I n M] [IsManifold I 1 M] [IsManifold J n N] [IsManifold J 1 N]
    [IsManifold J' n N'] [IsManifold J' 1 N'] {g : N → N'}
    (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) :
    IsSmoothEmbedding I J' n (g ∘ f) :=
  ⟨hg.isImmersion.comp hf.isImmersion, hg.isEmbedding.comp hf.isEmbedding⟩

/-- If `g` and `g ∘ f` are smooth embeddings, so is `f`. -/
lemma of_comp [IsManifold I' 1 M'] [IsManifold I' n M'] {g : N → M'}
    [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace E₃]
    [IsManifold I 1 M] [IsManifold I n M] [IsManifold J 1 N] [IsManifold J n N]
    (hg : IsSmoothEmbedding J I' n g)
    (hfg : IsSmoothEmbedding I I' n (g ∘ f)) :
    IsSmoothEmbedding I J n f := by
  have := hg.isImmersion.of_comp hfg.isImmersion
  exact ⟨this, .of_comp this.contMDiff.continuous hg.isEmbedding.continuous hfg.isEmbedding⟩

/-- If `g` is a smooth embedding, `g ∘ f` is a smooth embedding iff `f` is. -/
lemma of_comp_iff [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace E₃]
    [IsManifold I 1 M] [IsManifold I n M] [IsManifold J 1 N] [IsManifold J n N]
    [IsManifold I' 1 M'] [IsManifold I' n M'] {g : N → M'} (hg : IsSmoothEmbedding J I' n g) :
    IsSmoothEmbedding I I' n (g ∘ f) ↔ IsSmoothEmbedding I J n f :=
  ⟨fun hfg ↦ hg.of_comp hfg, fun hf ↦ hg.comp hf⟩

/-- If `f` is a `C^n` immersion at `x`, then `mfderiv I J f x` is injective. -/
theorem mfderiv_injective [CompleteSpace E₁] [CompleteSpace E₃]
    [IsManifold I n M] [IsManifold I 1 M] [IsManifold J n N] [IsManifold J 1 N]
    (h : IsSmoothEmbedding I J n f) (x : M) : Function.Injective (mfderiv I J f x) :=
  h.isImmersion.mfderiv_injective x

end IsSmoothEmbedding

-- TODO: prove the same result for local diffeomorphisms and deduce it as a corollary
proof_wanted Diffeomorph.isSmoothEmbedding (φ : Diffeomorph I I M M n) : IsSmoothEmbedding I I n φ

end Manifold
