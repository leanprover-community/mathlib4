/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Submanifold
--public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! # The regular value theorem

to be written!
-/

public section

open scoped ContDiff
open Manifold Topology Function Set

universe u
-- Let `M` and `N` be `C^n` manifolds over a field `𝕜`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ E₄ E₅ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  [NormedAddCommGroup E₅] [NormedSpace 𝕜 E₅]
  {H H' H'' G G' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E₁ H} {I' : ModelWithCorners 𝕜 E₂ H'}
  {J : ModelWithCorners 𝕜 E₃ G} {J' : ModelWithCorners 𝕜 E₄ G'} {J'' : ModelWithCorners 𝕜 E₅ H''}
  {M M' N N' P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  [TopologicalSpace P] [ChartedSpace H'' P]
  {n : WithTop ℕ∞}
  {F F' : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-

Finite-dimensional versions:
- constant rank theorem; differential has constant rank
- standard version: differential is surjective everyhere
- conceptual version: differential (is surjective and) has a bounded right inverse

-/

variable {f : M → N}

--lemma regularValueTheorem (hf : ∀ x, HasBoundedRightInverse ())

#exit
-- If the differential of
theorem foo
