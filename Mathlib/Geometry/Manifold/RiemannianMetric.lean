/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-! # Riemannian metrics
TODO: write docstring
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

open Bundle

/-- The contangent bundle of `M` is the dual bundle of `TangentBundle I M`. -/
abbrev CotangentBundle := Bundle.ContinuousLinearMap (RingHom.id 𝕜) (Bundle.Trivial M 𝕜)
  (fun x ↦ TangentSpace I x)

-- proper definition: symmetric bundle... will try this hack first
-- abbrev BiCotangentBundle := Bundle.Prod.smoothVectorBundle I (Bundle.Trivial M 𝕜) (Bundle.Trivial M 𝕜)--CotangentBundle I M)

-- abbrev MyBundle [TopologicalSpace M] [ChartedSpace H M]
--   := Bundle.Prod.smoothVectorBundle I (B := M) (CotangentBundle I M) (CotangentBundle I M)
-- underlying map: (fun (x : M) ↦ (TangentSpace I x) × (TangentSpace I x))

-- structure RiemannianMetric where
--   g : SmoothSection I (Bundle.Prod.smoothVectorBundle I (B := M) (CotangentBundle I M) (CotangentBundle I M)))
--   symm : ∀ x : M, ∀ v w : TangentSpace 𝓘(ℝ, E) x, g x v w = g x w v
--   posdef : ∀ x : M, ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 → 0 < g x v v
