/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-! # Smooth immersions and embeddings

In this file, we define `C^k` immersions and embeddings between `C^k` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition: we cannot prove the implication yet.

TODO complete this doc-string, once more details are clear.

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] {n : WithTop ℕ∞}

-- XXX: should the next three definitions be a class instead?
-- Are these slice charts canonical enough that we want the typeclass system to kick in?

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.

XXX: why in `maximalAtlas` and not merely atlas? to given ourselves extra freedom?
-/
structure IsImmersionAt (f : M → M') (x : M) where
  equiv : (E × F) ≃L[𝕜] E'
  φ : PartialHomeomorph M H
  ψ : PartialHomeomorph M' H'
  mem_source_x : x ∈ φ.source
  mem_source_fx : f x ∈ ψ.source
  mem_atlas_φ : φ ∈ IsManifold.maximalAtlas I n M
  mem_atlas_ψ : ψ ∈ IsManifold.maximalAtlas I' n M'
  writtenInCharts : (ψ.extend I') ∘ f ∘ (φ.extend I).symm = equiv ∘ (·, 0)

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion on `s` if around each point `x ∈ s`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively,
such that in these charts, `f` looks like `u ↦ (u, 0)`. -/
structure IsImmersionOn (f : M → M') (s : Set M) where
  equiv : (E × F) ≃L[𝕜] E'
  chartsM : M → PartialHomeomorph M H
  chartsM' : M' → PartialHomeomorph M' H'
  mem_source_M : ∀ x, x ∈ s → x ∈ (chartsM x).source
  mem_source_M' : ∀ x, x ∈ s → f x ∈ (chartsM' (f x)).source
  mem_atlas_M: ∀ x, x ∈ s → (chartsM x) ∈ IsManifold.maximalAtlas I n M
  mem_atlas_M': ∀ x, x ∈ s → (chartsM' (f x)) ∈ IsManifold.maximalAtlas I' n M'
  writtenInCharts : ∀ x, x ∈ s →
    ((chartsM' (f x)).extend I') ∘ f ∘ ((chartsM x).extend I).symm = equiv ∘ (·, 0)

variable (F I I' n) in
/-- `f : M → N` is a `C^k` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively,
such that in these charts, `f` looks like `u ↦ (u, 0)`. -/
structure IsImmersion (f : M → M') where
  equiv : (E × F) ≃L[𝕜] E'
  chartsM : M → PartialHomeomorph M H
  chartsM' : M' → PartialHomeomorph M' H'
  mem_source_M : ∀ x, x ∈ (chartsM x).source
  mem_source_M' : ∀ x, f x ∈ (chartsM' (f x)).source
  mem_atlas_M: ∀ x, (chartsM x) ∈ IsManifold.maximalAtlas I n M
  mem_atlas_M': ∀ x, (chartsM' (f x)) ∈ IsManifold.maximalAtlas I' n M'
  writtenInCharts : ∀ x,
    ((chartsM' (f x)).extend I') ∘ f ∘ ((chartsM x).extend I).symm = equiv ∘ (·, 0)

/-- If `f` is an immersion, it is an immersion at each point. -/
def IsImmersion.isImmersionAt {f : M → M'} (h : IsImmersion F I I' n f) (x : M) :
    IsImmersionAt F I I' n f x where
  equiv := h.equiv
  φ := h.chartsM x
  ψ := h.chartsM' (f x)
  mem_source_x := h.mem_source_M x
  mem_source_fx := h.mem_source_M' x
  mem_atlas_φ := h.mem_atlas_M x
  mem_atlas_ψ := h.mem_atlas_M' x
  writtenInCharts := h.writtenInCharts x

/-- If `f` is an immersion, it is an immersion on each set. -/
def IsImmersion.isImmersionOn {f : M → M'} (h : IsImmersion F I I' n f) (s : Set M) :
    IsImmersionOn F I I' n f s where
  equiv := h.equiv
  chartsM x := h.chartsM x
  chartsM' x := h.chartsM' x
  mem_source_M x _hx := h.mem_source_M x
  mem_source_M' x _hx := h.mem_source_M' x
  mem_atlas_M x _hx := h.mem_atlas_M x
  mem_atlas_M' x _hx := h.mem_atlas_M' x
  writtenInCharts x _hx := h.writtenInCharts x

/-- If `f` is an immersion on `Set.univ`, it is an immersion. -/
def IsImmersion.of_isImmersionOn_univ {f : M → M'} (h : IsImmersionOn F I I' n f Set.univ) :
    IsImmersion F I I' n f where
  equiv := h.equiv
  chartsM := h.chartsM
  chartsM' := h.chartsM'
  mem_source_M x := h.mem_source_M x trivial
  mem_source_M' x := h.mem_source_M' x trivial
  mem_atlas_M x := h.mem_atlas_M x trivial
  mem_atlas_M' x := h.mem_atlas_M' x trivial
  writtenInCharts x := h.writtenInCharts x trivial

-- If `f` is an immersion at each `x`, it is an immersion.
-- XXX: how to encode the different equivalences? just make part of the type?

/-- If `f` is a `C^k` immersion on `s`, it is an immersion at each `x ∈ s`. -/
-- The converse also holds, but is cumbersome to state, as `equiv` can vary with each point.
-- We'd have to translate between the equivalences.
def IsImmersionOn.isImmersionAt {f : M → M'} {s : Set M} {x : M}
    (h : IsImmersionOn F I I' n f s) (hx : x ∈ s) : IsImmersionAt F I I' n f x where
  equiv := h.equiv
  φ := h.chartsM x
  ψ := h.chartsM' (f x)
  mem_source_x := h.mem_source_M x hx
  mem_source_fx := h.mem_source_M' x hx
  mem_atlas_φ := h.mem_atlas_M x hx
  mem_atlas_ψ := h.mem_atlas_M' x hx
  writtenInCharts := h.writtenInCharts x hx

/-- If `f` is a `C^k` immersion at `x`, then `mfderiv x` is injective. -/
theorem IsImmersionAt.mfderiv_injective {f : M → M'} {x : M}
    (h : IsImmersionAt F I I' n f x) : Injective (mfderiv I I' f x) :=
  /- Outline of proof:
  (1) `mfderiv` is injective iff `fderiv (writtenInExtChart) is injective`
  I have proven this for Sard's theorem; this depends on some sorries not in mathlib yet
  (2) the injectivity of `fderiv (writtenInExtChart)` is independent of the choice of chart
  in the atlas (in fact, even the rank of the resulting map is),
  as transition maps are linear equivalences.
  (3) (·, 0) has injective `fderiv` --- since it's linear, thus its own derivative. -/
  sorry

/- If `M` is finite-dimensional and `mfderiv x` is injective, then `f` is immersed at `x`.
Some sources call this condition `f is infinitesimally injective at x`. -/
def IsImmersionAt.of_mfderiv_injective [FiniteDimensional 𝕜 E] {f : M → M'} {x : M}
    (hf : Injective (mfderiv I I' f x)) : IsImmersionAt F I I' n f x :=
  -- (1) if mfderiv I I' f x is injective, the same holds in a neighbourhood of x
  -- In particular, mfderiv I I' f x has (locally) constant rank: this suffices
  -- (2) If mfderiv I I' f x has constant rank for all x in a neighbourhood of x,
  -- then f is immersion at x.
  -- This step requires the inverse function theorem (and possibly shrinking the neighbourhood).
  sorry

/- If `M` is finite-dimensional, `f` is `C^k` and each `mfderiv x` is injective,
then `f` is a `C^k` immersion. -/
def IsImmersion.of_mfderiv_injective [FiniteDimensional 𝕜 E] {f : M → M'}
    (hf : ContMDiff I I' n f) (hf' : ∀ x, Injective (mfderiv I I' f x)) : IsImmersion F I I' n f :=
  -- TODO: glue the equivalences/make a type parameters, otherwise easy from the above
  sorry

variable (F I I' n) in
/-- A `C^k` map `f : M → M'` is a smooth `C^k` embedding if it is a topological embedding
and a `C^k` immersion. -/
structure IsSmoothEmbedding (f : M → M') extends IsImmersion F I I' n f where
  isEmbedding : Topology.IsEmbedding f

open Topology

def IsSmoothEmbedding.of_mfderiv_injective_of_compactSpace_of_T2Space
    [FiniteDimensional 𝕜 E] [CompactSpace M] [T2Space M'] {f : M → M'}
    (hf : ContMDiff I I' n f) (hf' : ∀ x, Injective (mfderiv I I' f x)) (hf'' : Injective f) :
    IsSmoothEmbedding F I I' n f where
  toIsImmersion := IsImmersion.of_mfderiv_injective hf hf'
  isEmbedding := (hf.continuous.isClosedEmbedding hf'').isEmbedding
