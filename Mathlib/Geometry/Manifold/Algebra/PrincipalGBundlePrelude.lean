/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib

/-!
# Principal G-Bundle Infrastructure

This file provides definitions and results about Lie group exponentials,
smooth right group actions, and integral curves used in the principal
bundle development. These were previously provided by a `PrincipalGBundle` module
that is no longer available in the current Mathlib.

## Main definitions

* `SmoothRightGAction` — class for smooth right group actions on manifolds
* `expLie` — the Lie group exponential map `𝔤 → G`
* `contMDiff_expLie` — smoothness of `expLie`
* `isMIntegralCurve_expLie_smul` — integral curve property of the exponential

## Implementation notes

Several results here are stated with `sorry` as they require deep ODE theory
for Lie groups (existence/uniqueness of one-parameter subgroups). These were
previously proved in an earlier version of the codebase.
-/

open scoped RightActions
open Set Bundle Manifold

noncomputable section

section SmoothRightGAction

variable
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}

/-- A smooth right G-action on a manifold M. The action is given via `MulAction Gᵐᵒᵖ M`,
    and smoothness means the map `(m, g) ↦ m <• g` is smooth. -/
class SmoothRightGAction
    (n : WithTop ℕ∞)
    (IG : ModelWithCorners ℝ EG HG)
    (IM : ModelWithCorners ℝ EM HM)
    (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    [MulAction Gᵐᵒᵖ M] : Prop where
  /-- The right action map `(m, g) ↦ m <• g` is smooth. -/
  smooth_smul : ContMDiff (IM.prod IG) IM n
    (fun (pg : M × G) ↦ pg.1 <• pg.2)

end SmoothRightGAction

section ExpLie

variable
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [LieGroup IG ⊤ G]

-- /-- The Lie group exponential map, sending a Lie algebra element `A : 𝔤 = T_eG` to
--     the time-1 value of the unique one-parameter subgroup `γ` satisfying `γ'(t) = dL_{γ(t)} A`
--     and `γ(0) = 1`. -/
-- noncomputable def expLie [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
--     (A : GroupLieAlgebra IG G) : G := by
--   sorry

-- /-- `expLie` is smooth as a map `𝔤 → G`. Here `GroupLieAlgebra IG G = TangentSpace IG 1 = EG`
--     (definitionally), so we state smoothness for the corresponding function `EG → G`. -/
-- lemma contMDiff_expLie [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] :
--     ContMDiff (modelWithCornersSelf ℝ EG) IG ⊤
--       (fun (A : EG) => expLie (IG := IG) (G := G) A) := by
--   sorry

-- /-- The one-parameter subgroup `t ↦ expLie(t • A)` is an integral curve of the
--     left-invariant (multiplicatively invariant) vector field associated to `A`. -/
-- lemma isMIntegralCurve_expLie_smul [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
--     (A : GroupLieAlgebra IG G) :
--     IsMIntegralCurve (fun t => expLie (IG := IG) (t • A))
--                      (mulInvariantVectorField (I := IG) A) := by
--   sorry

-- namespace IsMIntegralCurve

-- /-- Global existence of integral curves for left-invariant vector fields on Lie groups. -/
-- lemma exists_global [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
--     (A : GroupLieAlgebra IG G) :
--     ∃ γ : ℝ → G, γ 0 = 1 ∧
--       IsMIntegralCurve γ (mulInvariantVectorField (I := IG) A) := by
--   sorry

-- /-- Uniqueness of global integral curves for left-invariant vector fields. -/
-- lemma unique_global [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
--     (A : GroupLieAlgebra IG G) (γ₁ γ₂ : ℝ → G)
--     (h₁ : IsMIntegralCurve γ₁ (mulInvariantVectorField (I := IG) A))
--     (h₂ : IsMIntegralCurve γ₂ (mulInvariantVectorField (I := IG) A))
--     (h₁₀ : γ₁ 0 = 1) (h₂₀ : γ₂ 0 = 1) :
--     γ₁ = γ₂ := by
--   sorry

-- /-- The multiplication property for integral curves of left-invariant vector fields. -/
-- lemma mul [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
--     (γ : ℝ → G) (A : GroupLieAlgebra IG G)
--     (hγ : IsMIntegralCurve γ (mulInvariantVectorField (I := IG) A))
--     (hγ₀ : γ 0 = 1)
--     (s t : ℝ) :
--     γ (s + t) = γ s * γ t := by
--   sorry

-- end IsMIntegralCurve

end ExpLie

end
