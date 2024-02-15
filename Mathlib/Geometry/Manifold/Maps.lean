/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.ProperMap

/-! ## Smooth immersions, submersions and embeddings

In this file, we define immersions, submersions and smooth embeddings,
and prove their various relations and basic properties.

## Main definitions (xxx flesh out)
* `Immersion`: a differentiable immersion
* `InjImmersion`: an injective immersion
* `Submersion`: a smooth submersion (not assumed to be surjective)
* `OpenSmoothEmbedding`, `SmoothEmbedding`: (open) smooth embeddings

## Main results
* `SmoothEmbedding.toInjImmersion`: smooth embeddings are injective immersions
* `Embedding.of_proper_injective_immersion`: proper injective immersions are smooth embeddings
* `Submersion.surjective_of_proper`: a proper submersion into a connected manifold is surjective.

* `IsLocalDiffeomorph.toImmersion`: a `C^n` local diffeomorphism (`n≥1`) is an immersion
* `IsLocalDiffeomorph.toSubmersion`: a `C^n` local diffeomorphism (`n≥1`) is a submersion
* `IsLocalDiffeomorph.of_immersion_submersion`: if `f` is both an immersion and submersion,
  it is a local diffeomorphism.

* `Diffeomorph.toOpenSmoothEmbedding`: a `C^n` diffeomorphism (`n≥1`) is an open smooth embedding
(hence also an injective immersion)
* `Diffeomorph.of_immersion_submersion_bijective`: if `f` is an immersion, submersion and bijective,
  it is a diffeomorphism
* `Diffeomorph.of_injImmersion_submersion_isProperMap`: a proper injective immersion and submersion
  is a diffeomorphism
* `SmoothEmbedding.diffeomorph_of_surjective`: surjective smooth embeddings of finite-dimensional
  manifolds are diffeomorphisms

## TODO
- simple things: `DFunLike` instance; id is all of these; composition of them is one
- A submersion has open range (by the inverse function theorem).
- `SmoothEmbedding.toDiffeomorphRange`: a smooth embedding is a diffeomorphism to its range
  (this requires submanifolds to *state*)
- fill remaining sorries

## Implementation notes
- design decision: structure (vs definition, like sphere-eversion's Immersion)
- omit differentiability for immersions, following sphere-eversion?
  (probably not: at best provide a constructor omitting this)
- smooth embeddings don't assume smoothness of the inverse; this is automatic in finite dimension

**NOTE.** These are **not** the correct definitions in the infinite-dimensional context,
but in finite dimensions, the general definitions are equivalent to the ones in this file.

## Tags
manifold, immersion, submersion, smooth embedding

-/
noncomputable section

open Set Function

open scoped Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
-- Let `M'` be a manifold with corners over the pair `(E', H')`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [instE: NormedAddCommGroup E] [instE': NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

section Definitions

variable (I I')

/-- A `C^n` immersion `f : M → M` is a `C^n` map whose differential is injective at every point. -/
-- We don't require immersions to be injective: for instance, the figure eight shall be an immersed
-- manifold, whose most natural parametrisation is non-injective.
structure Immersion (f : M → M') (n : ℕ∞) : Prop :=
  differentiable : ContMDiff I I' n f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

/-- An injective `C^n immersion -/
structure InjImmersion (f : M → M') (n : ℕ∞) extends Immersion I I' f n : Prop :=
  injective : Injective f

/-- A `C^n` submersion `f : M → M` is a `C^n` map whose differential is surjective at every point.
  We do not require submersions to be surjective. -/
structure Submersion (f : M → M') (n : ℕ∞) : Prop :=
  differentiable : ContMDiff I I' n f
  diff_surjective : ∀ p, Surjective (mfderiv I I' f p)

/-- A `C^n` embedding `f : M → M'` is a `C^n` map which is both an immersion and a topological
  embedding. (We do not assume smoothness of the inverse, as this follows automatically.
  See `SmoothEmbedding.diffeomorph_of_surjective` and variants.) -/
-- FIXME: this should extend both Embedding and Immersion... possible? in which order?
structure SmoothEmbedding (f : M → M') (n : ℕ∞) extends Embedding f /-Immersion I I' f n-/ : Prop :=
  differentiable : ContMDiff I I' n f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

-- FIXME: this could also extend OpenEmbedding... same question as above
/-- A `SmoothEmbedding` with open range. -/
structure OpenSmoothEmbedding (f : M → M') (n : ℕ∞) extends SmoothEmbedding I I' f n : Prop :=
  open_range : IsOpen <| range f

-- FIXME: can I avoid this lemma, or is this a necessary by-product of no multiple extend's?
lemma OpenSmoothEmbedding.toOpenEmbedding (f : M → M') (n : ℕ∞) (h : OpenSmoothEmbedding I I' f n) :
    OpenEmbedding f where
  toEmbedding := h.toEmbedding
  open_range := h.open_range

end Definitions

-- Smart constructors about immersions
section Immersion

-- future: an "infinitesimally injective" map is an immersion, i.e.
-- a smooth map with injective differential is an immersion in the Banach manifold definition

/-- If `mfderiv f p` is injective at each point and `dim M` is positive or `M` is connected,
 `f` is an immersion. -/
-- TODO: add these extra conditions, and prove this!
theorem Immersion.of_mfderiv_injective {f : M → M'} (hf : ∀ p, Injective (mfderiv I I' f p))
     (n : ℕ∞) : Immersion I I' f n := sorry

-- for reference: design from sphere-eversion -- omitted differentiability
/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
-- TODO: replace this by a smart constructor for immersions instead
def Immersion' (f : M → M') : Prop :=
  ∀ p, Injective (mfderiv I I' f p)

end Immersion

-- Immersions and embeddings
section ImmersionEmbeddings

variable {f : M → M'} {n : ℕ∞}

/-- A smooth embedding is an injective immersion. -/
lemma SmoothEmbedding.toInjImmersion (h : SmoothEmbedding I I' f n) : InjImmersion I I' f n where
  differentiable := h.differentiable
  diff_injective := h.diff_injective
  injective := h.toEmbedding.inj

-- an injective immersion need not be an embedding: cue the standard example

/-- A proper injective immersion is an embedding, in fact a closed embedding. -/
lemma Embedding.of_proper_injective_immersion (h : Immersion I I' f n) (hp : IsProperMap f)
    (hf : Injective f) : SmoothEmbedding I I' f n where
  -- TODO: use "a proper injective continuous map is a closed embedding"
  -- does mathlib have this and the converse already?
  -- compare with "Submersion.surjective_of_proper" below
  toEmbedding := sorry
  differentiable := h.differentiable
  diff_injective := h.diff_injective

end ImmersionEmbeddings

namespace Submersion

variable {f : M → M'} {n : ℕ∞}

-- A submersion is locally a projection: this is the proper general definition;
-- deducing it from the finite-dimensional version requires the constant rank theorem.

/-- A submersion is an open map. -/
lemma isOpenMap (h : Submersion I I' f n) : IsOpenMap f := by
  -- 1. a submersion is locally a projection, see above
  -- 2. projections are open maps (is kinda in mathlib already: `FiberBundle.isOpenMap_proj`)
  -- 3. being an open map is a local property (essentially in mathlib as `isOpenMap_iff_nhds_le`)
  sorry

/-- A submersion has open range. -/
lemma open_range (h : Submersion I I' f n) : IsOpen (range f) :=
  h.isOpenMap.isOpen_range

/-- A proper submersion into a connected manifold is surjective. -/
-- TODO: remove Nonempty assumption; this is trivially true for the empty manifold
lemma surjective_of_proper (h : Submersion I I' f n) (hprop : IsProperMap f)
    [Nonempty M] (hconn : ConnectedSpace M') : Surjective f := by
  have : IsClopen (range f) := ⟨h.open_range, hprop.isClosedMap.closed_range⟩
  exact range_iff_surjective.mp (this.eq_univ (range_nonempty f))

end Submersion

-- relations to (local) diffeomorphisms
section Diffeo

variable {f : M → M'} {n : ℕ∞}

-- TODO: prove this, using the inverse function theorem
-- perhaps we can weaken differentiability requirement
-- this might require a complete space, for type theory reasons
-- (in a complete space, we can apply the open mapping theorem)
lemma IsLocalDiffeomorphAt.of_bijective_differential {x : M} (hf : ContMDiff I I' n f)
    (h : Bijective (mfderiv I I' f x)) : IsLocalDiffeomorphAt I I' n f x := sorry

/-- A `C^n` local diffeomorphism (`n≥1`) is an immersion. -/
lemma IsLocalDiffeomorph.toImmersion (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n) :
    Immersion I I' f n where
  differentiable := hf.contMDiff
  diff_injective x := (hf x).mfderiv_injective hn

/-- A `C^n` local diffeomorphism (`n≥1`) is a submersion. -/
lemma IsLocalDiffeomorph.toSubmersion (hf : IsLocalDiffeomorph I I' n f) (hn : 1 ≤ n) :
    Submersion I I' f n where
  differentiable := hf.contMDiff
  diff_surjective x := (hf x).mfderiv_surjective hn

/-- If `f` is both an immersion and submersion, it is a local diffeomorphism. -/
theorem IsLocalDiffeomorph.of_immersion_submersion (h : Immersion I I' f n)
    (hf : Submersion I I' f n) : IsLocalDiffeomorph I I' n f :=
  fun x ↦ IsLocalDiffeomorphAt.of_bijective_differential h.differentiable
    ⟨h.diff_injective x, hf.diff_surjective x⟩

/-- A `C^n` diffeomorphism (`n≥1`) is an open smooth embedding. -/
lemma Diffeomorph.toOpenSmoothEmbedding (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) :
    OpenSmoothEmbedding I I' h n where
  differentiable := h.contMDiff_toFun
  diff_injective x := (h.isLocalDiffeomorph x).mfderiv_injective hn
  induced := h.toHomeomorph.inducing.induced
  inj := h.toHomeomorph.injective
  open_range := h.toHomeomorph.isOpenMap.isOpen_range

/-- A `C^n` diffeomorphism (`n≥1`) is an immersion. -/
lemma Diffeomorph.toImmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) : Immersion I I' h n :=
  h.isLocalDiffeomorph.toImmersion hn

/-- A `C^n` diffeomorphism (`n≥1`) is an injective immersion. -/
lemma Diffeomorph.toInjImmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) :
    InjImmersion I I' h n where
  toImmersion := h.toImmersion hn
  injective := h.injective

/-- A `C^n` diffeomorphism (`n≥1`) is a submersion. -/
lemma Diffeomorph.toSubmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) :
    Submersion I I' h n :=
  h.isLocalDiffeomorph.toSubmersion hn

-- covering lemma `ContinuousLinearEquiv.toOpenSmoothEmbedding` in sphere-eversion
/- example : (e : E ≃L[𝕜] E') : OpenSmoothEmbedding 𝓘(𝕜, E) E 𝓘(𝕜, E') E' :=
  e.toDiffeomorph.toOpenSmoothEmbedding -/

/-- If `f` is bijective, an immersion and a submersion, it is a diffeomorphism. -/
def Diffeomorph.of_immersion_submersion_bijective (h : Immersion I I' f n)
    (hf : Submersion I I' f n) (hbij : Bijective f) : Diffeomorph I I' M M' n :=
  (IsLocalDiffeomorph.of_immersion_submersion h hf).diffeomorph_of_bijective hbij

-- xxx: is this lemma useful enough?
--lemma Diffeomorph.isProperMap (h : Diffeomorph I I' M M' n) : IsProperMap h.toFun :=
--  h.toHomeomorph.isProperMap

/-- If `M'` is non-empty and connected, an injective proper immersion `f : M → M'`
  which is a submersion is a diffeomorphism. -/
-- TODO: remove Nonempty assumption; this is trivially true for the empty manifold
def Diffeomorph.of_injImmersion_submersion_isProperMap [Nonempty M] (hconn : ConnectedSpace M')
    (himm : InjImmersion I I' f n) (hsub : Submersion I I' f n) (hprop : IsProperMap f) :
    Diffeomorph I I' M M' n :=
  Diffeomorph.of_immersion_submersion_bijective himm.toImmersion hsub
    ⟨himm.injective, hsub.surjective_of_proper hprop hconn⟩

/-- `TangentSpace I x` is defeq to `E`, hence also a normed additive abelian group. -/
local instance (x : M) : NormedAddCommGroup (TangentSpace I x) := instE
/-- `TangentSpace I x` is defeq to `E`, hence also a normed space. -/
local instance (x : M) : NormedSpace 𝕜 (TangentSpace I x) := instE'

/-- A surjective smooth embedding of finite-dimensional manifolds of the same dimension
  is a diffeomorphism: in particular, its inverse map is smooth.
  TODO: using invariance of domain, remove the equi-dimensionality assumption! -/
def SmoothEmbedding.diffeomorph_of_surjective [ifin: FiniteDimensional 𝕜 E]
    [ifin': FiniteDimensional 𝕜 E'] (h : SmoothEmbedding I I' f n) (hf : Surjective f)
    (hrank : FiniteDimensional.finrank 𝕜 E = FiniteDimensional.finrank 𝕜 E') :
  Diffeomorph I I' M M' n := by
  -- we follow Lee, Proposition 5.5.7 (but avoid passing to local charts)
  suffices h' : IsLocalDiffeomorph I I' n f from
    IsLocalDiffeomorph.diffeomorph_of_bijective h' ⟨h.toEmbedding.inj, hf⟩
  intro x
  have hinj : Injective (mfderiv I I' f x) := h.diff_injective x
  -- as E is finite-dimensional, the differential is also surjective
  haveI : FiniteDimensional 𝕜 (TangentSpace I x) := ifin
  haveI : FiniteDimensional 𝕜 (TangentSpace I' (f x)) := ifin'
  have aux2 : Surjective (mfderiv I I' f x) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    have h1 : TangentSpace I x = E := rfl
    have h2 : TangentSpace I' (f x) = E' := rfl
    sorry -- rw [h1, h2, hrank] "motive is not type correct"
  exact IsLocalDiffeomorphAt.of_bijective_differential h.differentiable ⟨hinj, aux2⟩

/- cannot state the following yet: needs that the range of a smooth embedding is a submanifold
  would follow from the same proof as SmoothEmbedding.diffeomorph_of_surjective
/-- A smooth embedding (in finite dimensions!) is a diffeomorphism to its image. -/
def Diffeomorph.ofSmoothEmbedding [FiniteDimensional 𝕜 E] (h : SmoothEmbedding I I' f n) :
    Diffeomorph I I' M (range f) n := sorry -/

end Diffeo
