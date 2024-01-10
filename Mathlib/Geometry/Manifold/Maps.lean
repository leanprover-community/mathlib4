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
- If `f` is bijective, an immersion and submersion, it is a diffeomorphism.
- A submersion has open range (by the inverse function theorem).
- `f` is a diffeomorphism iff it is an immersion, submersion and proper

- Define smooth embeddings; show smooth embeddings are injective immersions,
  surjective embeddings are diffeomorphisms (and vice versa).

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

-- TODO: prove this, using the inverse function theorem
-- perhaps can weaken differentiability requirement
lemma IsLocalDiffeomorphAt.of_bijective_differential {x : M} (hf : ContMDiff I I' n f)
    (h : Bijective (mfderiv I I' f x)) : IsLocalDiffeomorphAt I I' n f x := sorry

/-- A submersion has open range. -/
lemma Submersion.open_range (h : Submersion I I' f n) : IsOpen (range f) := sorry

/-- A proper submersion into a connected manifold is surjective. -/
lemma Submersion.surjective_of_proper (h : Submersion I I' f n) (hprop : IsProperMap f)
    [Nonempty M] (hconn : ConnectedSpace M') : Surjective f := by
  have : IsClopen (range f) := ⟨h.open_range, hprop.isClosedMap.closed_range⟩
  exact range_iff_surjective.mp (this.eq_univ (range_nonempty f))

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

/-- If `f` is both an immersion and submersion, it is a local diffeomorphism. -/
theorem Immersion.toLocalDiffeomorph_of_submersion (h : Immersion I I' f n)
    (hf : Submersion I I' f n) : IsLocalDiffeomorph I I' n f :=
  fun x ↦ IsLocalDiffeomorphAt.of_bijective_differential h.differentiable
    ⟨h.diff_injective x, hf.diff_surjective x⟩

/-- If `f` is bijective, an immersion and a submersion, it is a diffeomorphism. -/
def Immersion.toDiffeomorph_of_bijective_submersion (h : Immersion I I' f n)
    (hf : Submersion I I' f n) (hbij : Bijective f) : Diffeomorph I I' M M' n :=
  (h.toLocalDiffeomorph_of_submersion hf).diffeomorph_of_bijective hbij

-- xxx: necessary?
lemma Diffeomorph.isProperMap (h : Diffeomorph I I' M M' n) : IsProperMap h.toFun :=
  h.toHomeomorph.isProperMap

/-- If `M'` is non-empty connected, an injective proper immersion `f : M → M'` which is a submersion
 is a diffeomorphism. -/
theorem InjImmersion.toDiffeomorph_of_proper_submersion (himm : InjImmersion I I' f n)
    (hsub : Submersion I I' f n) (hprop : IsProperMap f) [Nonempty M]
    (hconn : ConnectedSpace M') : Diffeomorph I I' M M' n :=
  himm.toImmersion.toDiffeomorph_of_bijective_submersion hsub
    ⟨himm.injective, hsub.surjective_of_proper hprop hconn⟩

end LocalDiffeo

/-- A `C^n` embedding -/
structure SmoothEmbedding (f : M → M') (n : ℕ∞) extends Embedding f : Prop :=
  differentiable : ContMDiff I I' n f

-- xxx: which structure to extend? not sure yet!
-- sphere-eversion avoided extending anything, which is not ideal...
structure OpenSmoothEmbedding (f : M → M') (n : ℕ∞) extends SmoothEmbedding I I' f n : Prop :=
  open_range : IsOpen <| range f

namespace SmoothEmbedding
variable (f : M → M') (n : ℕ∞)

-- xxx: do I need M to be T0?
def toInjImmersion [T0Space M] (h : SmoothEmbedding I I' f n) : InjImmersion I I' f n := {
  differentiable := h.differentiable
  injective := h.toEmbedding.injective
  diff_injective := sorry -- xxx: extra conditions needed?
}

-- an injective immersion need not be an embedding. standard example with bijective cont, not homeo

end SmoothEmbedding

def IsLocalDiffeomorph.toSmoothEmbedding {f : M → M'} {n : ℕ∞} (hf : IsLocalDiffeomorph I I' n f) :
  SmoothEmbedding I I' f n := {
    differentiable := sorry
    induced := sorry
    inj := sorry--diff_injective := sorry
  }
