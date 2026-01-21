/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.FiberBundle.Basic

/-!
# Principal G-Bundles

This file defines smooth principal bundles with Lie group actions on manifolds.

## Main definitions

* `SmoothLeftGAction`: An `n`-times continuously differentiable left action of a Lie group
  on a manifold
* `SmoothRightGAction`: An `n`-times continuously differentiable right action of a Lie group
  on a manifold
* `PrincipalBundleCore`: The core structure of a principal bundle, consisting of a fiber bundle
  with a free and transitive group action on the fibers

## Implementation notes

Right actions are encoded using `MulAction (MulOpposite G)` to maintain compatibility with
Mathlib's action conventions while preserving the correct associativity for principal bundles.

## References

* Standard reference on principal bundles and connections

-/

open Matrix Bundle Manifold MulAction

open RightActions

/-- An `n`-times continuously differentiable left action of a Lie group `G` on a manifold `M`.

This class asserts that the left action map `(g, m) ↦ g • m` is `n`-times continuously
differentiable as a map `G × M → M` between manifolds. This is the standard notion of
a Lie group acting differentiably on a manifold.

## Smoothness parameter
- `n`: The differentiability degree used uniformly for the Lie group `G`, the manifold `M`,
  and the action map itself (Cⁿ structures throughout)
- Common choices: `n = ⊤` (infinitely differentiable/smooth), or `n = ∞` (real analytic)

The dimensions of `G` and `M` are independent and are determined by the model spaces
`E_G` and `E_M` respectively.

## Main condition
- `smooth_smul`: The action map `(g, m) ↦ g • m` is `n`-times continuously differentiable
  (ContMDiff with degree `n`)

## Terminology note
The field is named `smooth_smul` following Mathlib conventions, even though it asserts
`n`-times differentiability rather than infinite differentiability when `n ≠ ⊤`.

## Related definitions
- For right actions, see `SmoothRightGAction`
- For actions on principal bundles, the differentiability is typically automatic from the
  fiber bundle structure
-/
class SmoothLeftGAction
{𝕜 : Type*} [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞)
{E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
{E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
{H_G : Type*} [TopologicalSpace H_G] (I_G : ModelWithCorners 𝕜 E_G H_G)
{H_M : Type*} [TopologicalSpace H_M] (I_M : ModelWithCorners 𝕜 E_M H_M)
(G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
(M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]
[MulAction G M]
[IsManifold I_G n G]
[IsManifold I_M n M] : Prop where
 (smooth_smul : ContMDiff (I_G.prod I_M) I_M n (fun p : G × M => p.1 •> p.2))

/-- An `n`-times continuously differentiable right action of a Lie group `G` on a manifold `M`.

This class asserts that the right action map `(m, g) ↦ m <• g` is `n`-times continuously
differentiable as a map `M × G → M` between manifolds. Right actions are encoded via
`MulAction (MulOpposite G) M`, which allows reusing the left action infrastructure while
maintaining the correct associativity: `(m <• g) <• h = m <• (g * h)`.

Right actions appear naturally in the theory of principal bundles, where the structure
group acts on the right to preserve the geometric structure.

## Smoothness parameter
- `n`: The differentiability degree used uniformly for the Lie group `G`, the manifold `M`,
  and the action map itself (Cⁿ structures throughout)
- Common choices: `n = ⊤` (infinitely differentiable/smooth), or `n = ∞` (real analytic)

The dimensions of `G` and `M` are independent and are determined by the model spaces
`E_G` and `E_M` respectively.

## Main condition
- `smooth_smul`: The right action map `(m, g) ↦ m <• g` is `n`-times continuously differentiable

## Terminology note
The field is named `smooth_smul` following Mathlib conventions, even though it asserts
`n`-times differentiability rather than infinite differentiability when `n ≠ ⊤`.

## Implementation notes
- The action is encoded as `MulAction (MulOpposite G) M` rather than a separate right
  action typeclass, which is the standard Mathlib convention
- The differentiability is stated for the map `M × G → M` (note the order of factors)

## Related definitions
- For left actions, see `SmoothLeftGAction`
- For principal bundles, right actions are typically required for the structure group
-/
class SmoothRightGAction
 {𝕜 : Type*} [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞)
 {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
 {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
 {H_G : Type*} [TopologicalSpace H_G] (I_G : ModelWithCorners 𝕜 E_G H_G)
 {H_M : Type*} [TopologicalSpace H_M] (I_M : ModelWithCorners 𝕜 E_M H_M)
 (G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
 (M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]
 [MulAction (MulOpposite G) M]
 [IsManifold I_G n G]
 [IsManifold I_M n M]
 : Prop where
 smooth_smul : ContMDiff (I_M.prod I_G) I_M n (fun p : M × G => p.1 <• p.2)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {n : WithTop ℕ∞}
variable {E_G E_M : Type*} [NormedAddCommGroup E_G] [NormedAddCommGroup E_M]
variable [NormedSpace 𝕜 E_G] [NormedSpace 𝕜 E_M]
variable {H_G H_M : Type*} [TopologicalSpace H_G] [TopologicalSpace H_M]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace H_G G] [Group G]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H_M M]
variable {I_G : ModelWithCorners 𝕜 E_G H_G}
variable {I_M : ModelWithCorners 𝕜 E_M H_M}
variable [LieGroup I_G n G]
variable [IsManifold I_G n G] [IsManifold I_M n M]
variable [MulAction G M] [SmoothLeftGAction n I_G I_M G M]

open MulOpposite

instance mulAction_op_of_left [Group G] [MulAction G M] : MulAction (Gᵐᵒᵖ) M where
  smul g m := (unop g)⁻¹ • m
  one_smul := by
    intro b
    have h1 : (1 : G) • b = b := MulAction.one_smul b
    have h3 : unop (1 : Gᵐᵒᵖ)⁻¹ •> b = b := by rw [<-inv_one] at h1; exact h1
    exact h3

  mul_smul := by
    intro g₁ g₂ m
    have h1 : (unop (g₁ * g₂))⁻¹ •> m = (unop g₁)⁻¹ • ((unop g₂)⁻¹ • m) := by
      calc
      (unop (g₁ * g₂))⁻¹ •> m
        = (unop g₂ * unop g₁)⁻¹ •> m       := by rw [unop_mul]
      _ = ((unop g₁)⁻¹ * (unop g₂)⁻¹) •> m := by rw [_root_.mul_inv_rev]
      _ = (unop g₁)⁻¹ • ((unop g₂)⁻¹ • m)  := by rw [SemigroupAction.mul_smul];
    exact h1

instance SmoothRightGAction_of_Left
  [MulAction G M]
  [SmoothLeftGAction n I_G I_M G M] :
  SmoothRightGAction n I_G I_M G M where

  smooth_smul := by
    let f : M × G → G × M := fun (p, g) => (g⁻¹, p)
    have hf : ContMDiff (I_M.prod I_G) (I_G.prod I_M) n f := by
      apply ContMDiff.prodMk
      · exact ContMDiff.comp (contMDiff_inv I_G n) contMDiff_snd
      · exact contMDiff_fst
    exact ContMDiff.comp SmoothLeftGAction.smooth_smul hf

universe uK uB uF uH uI uG uP

/-- The core structure of a principal G-bundle.

A principal bundle consists of a fiber bundle where the structure group G acts on the fibers
in a way that is free (no non-trivial stabilizers) and transitive (the action connects any
two points in the same fiber). This captures the essential structure needed for principal
bundles in differential geometry.

## Main conditions
- `respects_fibres`: The group action preserves fibers
- `is_free`: The action has no fixed points (except for the identity)
- `is_transitive`: The action is transitive on each fiber

Together, `is_free` and `is_transitive` mean that each fiber is a principal homogeneous
space (also called a G-torsor in some contexts) for G.
-/
structure PrincipalBundleCore
  (ι : Type uP)
  {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
  {n : WithTop ℕ∞}
  {E_B : Type uB} {E_F : Type uF} {E_G : Type uG}
  [NormedAddCommGroup E_B] [NormedSpace 𝕜 E_B]
  [NormedAddCommGroup E_F] [NormedSpace 𝕜 E_F]
  [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
  {H_B : Type uH} {H_F : Type uI} {H_G : Type uG}
  [TopologicalSpace H_B] [TopologicalSpace H_F] [TopologicalSpace H_G]
  {I_B : ModelWithCorners 𝕜 E_B H_B}
  {I_F : ModelWithCorners 𝕜 E_F H_F}
  {I_G : ModelWithCorners 𝕜 E_G H_G}
  (B : Type uB) [TopologicalSpace B] [ChartedSpace H_B B] [IsManifold I_B n B]
  (F : Type uF) [TopologicalSpace F]
  [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
  (core : FiberBundleCore ι B F)
  [MulAction (MulOpposite G) (TotalSpace F (core.Fiber))]
  [ChartedSpace (ModelProd H_B H_F) (TotalSpace F core.Fiber)]
  [IsManifold (ModelWithCorners.prod I_B I_F) n (TotalSpace F core.Fiber)]
  [SmoothRightGAction n I_G (ModelWithCorners.prod I_B I_F) G (TotalSpace F core.Fiber)]
  where
  (respects_fibres : ∀ (p : TotalSpace F (core.Fiber)) (g : G), core.proj (p <• g) = core.proj p)
  (is_free : ∀ (g : G), stabilizer G g = ⊥)
  (is_transitive : ∀ (b : B) (p q : TotalSpace F (core.Fiber)),
    core.proj p = b → core.proj q = b → q ∈ orbit (MulOpposite G) p)

-- TODO: move to better location
instance {α : Type*} [DecidableEq α] [Fintype α] : MulAction (orthogonalGroup α ℝ) (α -> ℝ) where
  smul g x := g.1.mulVec x
  one_smul x := by
    change (1 : orthogonalGroup α ℝ).1.mulVec x = x
    simp
  mul_smul := fun f g x => by
    change (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]
