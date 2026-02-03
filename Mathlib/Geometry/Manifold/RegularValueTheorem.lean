/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Submanifold
public import Mathlib.Geometry.Manifold.RegularPoint

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

public noncomputable section

variable {f : M → N}

variable (I J) in
def IsRegularValue (f : M → N) (y : N) := ∀ x ∈ f ⁻¹' {y}, IsRegularPoint I J f x

-- Suppose M is not empty. (Otherwise, we can do anything we want.)
-- Pick a pre-image x of y. Then mfderiv has a bounded right inverse;
-- take the image of that right inverse.

def IsRegularValue.complement {x : M} (hx : IsRegularValue I J f (f x)) : Type _ :=
  (hx x rfl).choose.range

instance {x : M} (hx : IsRegularValue I J f (f x)) : NormedAddCommGroup hx.complement := by
  sorry -- infer_instance

instance {x : M} (hx : IsRegularValue I J f (f x)) : NormedSpace 𝕜 hx.complement := by
  sorry -- infer_instance

#exit
--(hf : ∀ x, IsRegularPoint I J f x) :
def regularValueTheorem {y : N} (hy : IsRegularValue I J f y) :
    True := by
  sorry
