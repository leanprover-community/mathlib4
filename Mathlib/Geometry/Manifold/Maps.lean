/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! ## Smooth immersions, submersions and embeddings

In this file, we define immersions, submersions and smooth embeddings,
and prove their various relations and basic properties.

## Main definitions (xxx flesh out)
* `Immersion`: a differentiable immersion
* `InjImmersion`
* `Submersion`

## Main results
* `IsLocalDiffeomorph.toImmersion`: a `C^n` local diffeomorphism (`n≥1`) is an immersion
* `IsLocalDiffeomorph.toSubmersion`: a `C^n` local diffeomorphism (`n≥1`) is a submersion
* `Diffeomorph.toImmersion`: a `C^n` diffeomorphism (`n≥1`) is an immersion
* `Diffeomorph.toSubmersion`: a `C^n` diffeomorphism (`n≥1`) is a submersion

## TODO
- If `f` is both an immersion and submersion, it is a local diffeomorphism.
(This requires the inverse function theorem: an invertible differential at `x` implies
 being a local diffeomorphism at `x`. This may also require working in a complete space.)
- Define smooth embeddings; show smooth embeddings are injective immersions,
  and diffeomorphisms are smooth embeddings.

implementation notes: bundled
omit differentiability for immersions, following sphere-eversion?

## Tags
manifold, immersion, submersion, smooth embedding

-/
noncomputable section

open Set Function

open scoped Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
-- Let `M'` be a manifold with corners over the pair `(E', H')`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

section Definitions

-- for reference: design from sphere-eversion -- unbundled; omitted differentiability
/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
def Immersion' (f : M → M') : Prop :=
  ∀ p, Injective (mfderiv I I' f p)

/-- A `C^n` immersion `f : M → M` is a `C^n` map whose differential is injective at any point. -/
-- We don't require immersions to be injective: for instance, the figure eight shall be an immersed
-- manifold, whose most natural parametrisation is non-injective.
structure Immersion (f : M → M') (n : ℕ∞) : Prop :=
  differentiable : ContMDiff I I' n f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

/-- An injective `C^n immersion -/
structure InjImmersion (f : M → M') (n : ℕ∞) extends
  Immersion I I' f n : Prop :=
  injective : Injective f

/-- A `C^n` submersion `f : M → M` is a `C^n` map whose differential is surjective at any point.
We don't ask for a submersion to be surjective. -/
structure Submersion (f : M → M') (n : ℕ∞) : Prop :=
  differentiable : ContMDiff I I' n f
  diff_surjective : ∀ p, Surjective (mfderiv I I' f p)

end Definitions

section LocalDiffeo
variable {f : M → M'} {n : ℕ∞}
variable {I I'}

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

/-- A `C^n` diffeomorphism (`n≥1`) is an immersion. -/
lemma Diffeomorph.toImmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) : Immersion I I' h n where
  differentiable := h.contMDiff_toFun
  diff_injective x := (h.isLocalDiffeomorph x).mfderiv_injective hn

/-- A `C^n` diffeomorphism (`n≥1`) is an injective immersion. -/
lemma Diffeomorph.toInjImmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) :
    InjImmersion I I' h n where
  toImmersion := h.toImmersion hn
  injective := h.injective

/-- A `C^n` diffeomorphism (`n≥1`) is a submersion. -/
lemma Diffeomorph.toSubmersion (h : Diffeomorph I I' M M' n) (hn : 1 ≤ n) :
    Submersion I I' h n where
  differentiable := h.contMDiff_toFun
  diff_surjective x := (h.isLocalDiffeomorph x).mfderiv_surjective hn

end LocalDiffeo
