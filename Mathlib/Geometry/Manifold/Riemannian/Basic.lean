/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.VectorBundle.Riemannian

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with a
scalar product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths. -/

open Bundle
open scoped Manifold ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*}

instance (x : unitInterval) : One (TangentSpace (𝓡∂ 1) x) where
  one := fun _ ↦ 1

section

variable [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an inner product, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I 1 γ), ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ

/- TODO: show that this is a distance (symmetry, triange inequality, nondegeneracy) -/

end

section

variable [EMetricSpace M] [ChartedSpace H M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

variable (I M) in
/-- Consider a manifold in which the tangent spaces are already endowed with a scalar product, and
already endowed with an extended distance. We say that this is a Riemannian manifold if the distance
is given by the infimum of the lengths of `C^1` paths, measured using the norm in the tangent
spaces.

This is a `Prop` valued typeclass, on top of existing data. -/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

/- TODO: show that a vector space with an inner product is a Riemannian manifold. -/

end
