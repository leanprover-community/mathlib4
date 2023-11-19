/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt I J M N n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `LocalDiffeomorph I J M N n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, and `LocalDiffeomorphAt` implies the next condition.
* `Diffeomorph.of_bijective_local_diffeomorph`: a bijective local diffeomorphisms is a diffeomorphism.
TODO: a local diffeomorphism is a diffeomorphism to its image

* `LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorphAt.of_DifferentialIsoAt`: conversely, if `f` is `C^n` at `x` and
`mfderiv I J n f x` is a linear isomorphism, `f` is a local diffeomorphism at `x`.

* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorph.of_differentialInvertible`: Conversely, if `f` is `C^n` and each differential
is a linear isomorphism, `f` is a local diffeomorphism.

## Design decisions
xxx: fix this up: we don't do this, but instead model after IsLocalStructomorphAt

For all definitions, we use the junk value pattern: a local diffeomorphism at `x` is still given
by a function on all of `M`; its values outside its `source` are irrelevant. (This matches the
treatment of smooth manifolds and `LocalHomeomorph`.)

This combines with the second major design decision: all our definitions are bundled. That is,
we consider `f` together with a choice `g` of inverse. For local diffeomorphisms, `g` can take any
values outside of `f.target`.
A local diffeomorphism contains the data `f` and `g`, together with proofs that these define a
local diffeomorphism at each point.

## Tags
local diffeomorphism, manifold

-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞}

variable (I J M N n)

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ U : Opens M, ∃ V : Opens N, ∃ Φ : Diffeomorph I J U V n, x ∈ U ∧ ∀ x : U, f x = Φ x

/-- `f : M → N` is a **`C^n` local diffeomorph** iff it is a local diffeomorphism at each point. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J M N n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
  IsLocalDiffeomorph I J M N n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J M N n f x := by rfl

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J M N n Φ := by
  intro x
  use ⟨univ, isOpen_univ⟩, ⟨univ, isOpen_univ⟩
  use sorry -- xxx: use Φ now; don't have the same type!!
  refine ⟨trivial, ?_⟩
  -- obvious once this is shown
  sorry

-- TODO: the image of a local diffeomorphism is open
-- def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J M N n f) : Opens N := sorry
-- lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J M N n f) :
--  (LocalDiffeomorph.image I J M N n hf).1 = range f := sorry
-- then deduce the following as a special case

/-- A bijective local diffeomorphism is a diffeomorphism. -/
def Diffeomorph.of_bijective_local_diffeomorph {f : M → N} (hf : IsLocalDiffeomorph I J M N n f)
    (hf' : Bijective f) : Diffeomorph I J M N n := sorry

section Differential
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N] {f : M → N} {x : M}

/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≥ 1`,
  the differential `df_x` is a linear equivalence. -/
  -- LocalDiffeomorphAt.differential_toContinuousLinearEquiv
lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorphAt I J M N n f x) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) := by
  sorry

end Differential
