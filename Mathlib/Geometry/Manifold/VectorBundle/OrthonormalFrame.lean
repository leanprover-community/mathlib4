/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Existence of orthonormal frames on Riemannian vector bundles

In this file, we prove that a Riemannian vector bundle has orthonormal frames near each point.
These are constructed by taking any local frame, and applying Gram-Schmidt orthonormalisation
to it (point-wise). If the bundle metric is `C^k`, the resulting orthonormal frame also is.

TODO: add main results, tags, etc

## Implementation note

Like local frames, orthonormal frames use the junk value pattern: their value is meaningless
outside of the `baseSet` of the trivialisation used to define them.

## Tags
vector bundle, local frame, smoothness

-/

open Manifold Bundle ContinuousLinearMap ENat Bornology
open scoped ContDiff Topology

-- Let `V` be a smooth vector bundle with a `C^n` Riemannian structure over a `C^k` manifold `B`.
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]

variable {ι : Type*}

-- bad, for prototyping
variable (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e]
    (b : Basis ι ℝ F) {x : B} (hx : x ∈ e.baseSet)
namespace Basis

-- TODO: revisit this using GramSchmidtOrtho.lean!

-- noncomputable def orthonormalFrame_toBasis_at : Basis ι ℝ (E x) :=
--   sorry -- b.map (e.linearEquivAt (R := 𝕜) x hx).symm

-- open scoped Classical in
-- -- If x is outside of `e.baseSet`, this returns the junk value 0.
-- noncomputable def orthonormalFrame : ι → (x : B) → E x := fun i x ↦
--   -- idea: take the vector b i and apply the trivialisation e to it.
--   b.localFrame e x--if hx : x ∈ e.baseSet then b.localFrame_toBasis_at e hx i else 0
end Basis
