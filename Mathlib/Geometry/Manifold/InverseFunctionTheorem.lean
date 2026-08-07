/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.Notation

/-! # The inverse function theorem for `C^n` manifolds

Here is a sketch of the inverse function theorem for manifolds.
There are two forms to state it. One is "unbundled", i.e. yielding an honest inverse function
(with separate lemmas stating its smoothness, being a local inverse, etc.)
The other uses local diffeomorphisms. For simplicity, I'll state just the latter for now.

TODO: generalise the proof to a suitable family of pregroupoids
(and deduce this version as a corollary)

TODO: compare with existing work and produce a formalisation of one or both cases

-/

open Function Set Topology
open scoped Manifold ContDiff

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- If `f : M → N` is `C^n` at `x` and has invertible differential at an interior point `x`,
it is a local diffeomorphism at `x`. -/
theorem IsLocalDiffeomorphAt.of_isInvertible_of_isInterriorPoint (hx : I.IsInteriorPoint x)
      (hf : CMDiffAt n f x) (hf' : mfderiv% f x |>.IsInvertible) :
     IsLocalDiffeomorphAt I J n f x := by
  sorry

/-- If `f : M → N` is `C^n` at `x`, has invertible differential at an interior point `x`
and `x` has an open neighbourhood `V` such that `f (V ∩ ∂M) ⊆ ∂N`, then `f` is a local
diffeomorphism at `x`.
Proof e.g. [Margalef-Roig, Theorem 2.2.6] -/
-- This is a tentative generalisation of the above, with a few caveats:
--  * the above proof assumes Margalef-Roig's definition of manifolds; Lean's is more general
--    I'm pretty sure this will generalise, but haven't checked carefuly yet
--  * I *presume* we only need `f` to be `C^n` at x (not globally), but haven't checked yet,
--  * this formalisation allows `V` to be any neighbourhood... but that is fine, `V` will always
--    contain a smaller open neighbourhood (which we could shrink to)
theorem IsLocalDiffeomorphAt.of_isInvertible (hf : CMDiffAt n f x)
    (hf' : mfderiv% f x |>.IsInvertible)
    {V : Set M} (hV : V ∈ 𝓝 x) (hmaps : f '' (V ∩ (I.boundary M)) ⊆ J.boundary N) :
     IsLocalDiffeomorphAt I J n f x := by
  sorry

/-
Counterexample to missing the boundary condition above:
consider `M = N = [0,∞)` with the `C^n` map `f : x ↦ 2x + 3`.
Its differential at `0` is invertible (easy), but `f` is not a local diffeo at `0`:
an open neighbourhood of `0` (like, `[0, ε)` for some `ε > 0`) is not mapped to an
*open neighbourhood* of `f 0 = 3`; the inverse map on an open neighbourhood is not injective.
-/

/-- If `M` has no boundary, `f : M → N` is `C^n` and has invertible differential everywhere,
it is a local diffeomorphism. -/
theorem IsLocalDiffeomorph.of_isInvertible_of_boundaryless [BoundarylessManifold I M]
    (hf : CMDiff n f) (hf' : ∀ x, mfderiv% f x |>.IsInvertible) :
    IsLocalDiffeomorph I J n f :=
  fun x ↦ IsLocalDiffeomorphAt.of_isInvertible_of_isInterriorPoint
    (BoundarylessManifold.isInteriorPoint) (hf x) (hf' x)

/-- If `f : M → N` is `C^n` and has invertible differential everywhere and maps the boundary nicely,
it is a local diffeomorphism. -/
theorem IsLocalDiffeomorph.of_isInvertible
    (hf : CMDiff n f) (hf' : ∀ x, mfderiv% f x |>.IsInvertible)
    {V : M → Set M} (hV : ∀ x, V x ∈ 𝓝 x) (hmap : ∀ x, f '' (V x ∩ (I.boundary M)) ⊆ J.boundary N) :
    IsLocalDiffeomorph I J n f :=
  fun x ↦ IsLocalDiffeomorphAt.of_isInvertible (hf x) (hf' x) (hV x) (hmap x)
