/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivative of the inversion

In this file we prove a formula for the derivative of `EuclideanGeometry.inversion c R`.

## Implementation notes

Since `fderiv` and related definiitons do not work for affine spaces, we deal with an inner product
space in this file.

## Keywords

inversion, derivative
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open Metric Function AffineMap Set AffineSubspace
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open EuclideanGeometry

section DotNotation

variable {c x : E → F} {R : E → ℝ} {s : Set E} {a : E} {n : ℕ∞}

protected theorem ContDiffWithinAt.inversion (hc : ContDiffWithinAt ℝ n c s a)
    (hR : ContDiffWithinAt ℝ n R s a) (hx : ContDiffWithinAt ℝ n x s a) (hne : x a ≠ c a) :
    ContDiffWithinAt ℝ n (fun a ↦ inversion (c a) (R a) (x a)) s a :=
  (((hR.div (hx.dist ℝ hc hne) (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

protected theorem ContDiffOn.inversion (hc : ContDiffOn ℝ n c s) (hR : ContDiffOn ℝ n R s)
    (hx : ContDiffOn ℝ n x s) (hne : ∀ a ∈ s, x a ≠ c a) :
    ContDiffOn ℝ n (fun a ↦ inversion (c a) (R a) (x a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected nonrec theorem ContDiffAt.inversion (hc : ContDiffAt ℝ n c a) (hR : ContDiffAt ℝ n R a)
    (hx : ContDiffAt ℝ n x a) (hne : x a ≠ c a) :
    ContDiffAt ℝ n (fun a ↦ inversion (c a) (R a) (x a)) a :=
  hc.inversion hR hx hne

protected nonrec theorem ContDiff.inversion (hc : ContDiff ℝ n c) (hR : ContDiff ℝ n R)
    (hx : ContDiff ℝ n x) (hne : ∀ a, x a ≠ c a) :
    ContDiff ℝ n (fun a ↦ inversion (c a) (R a) (x a)) :=
  contDiff_iff_contDiffAt.2 fun a ↦ hc.contDiffAt.inversion hR.contDiffAt hx.contDiffAt (hne a)

protected theorem DifferentiableWithinAt.inversion (hc : DifferentiableWithinAt ℝ c s a)
    (hR : DifferentiableWithinAt ℝ R s a) (hx : DifferentiableWithinAt ℝ x s a) (hne : x a ≠ c a) :
    DifferentiableWithinAt ℝ (fun a ↦ inversion (c a) (R a) (x a)) s a :=
  -- TODO: Use `.div` #5870
  (((hR.mul <| (hx.dist ℝ hc hne).inv (dist_ne_zero.2 hne)).pow _).smul (hx.sub hc)).add hc

protected theorem DifferentiableOn.inversion (hc : DifferentiableOn ℝ c s)
    (hR : DifferentiableOn ℝ R s) (hx : DifferentiableOn ℝ x s) (hne : ∀ a ∈ s, x a ≠ c a) :
    DifferentiableOn ℝ (fun a ↦ inversion (c a) (R a) (x a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha) (hne a ha)

protected theorem DifferentiableAt.inversion (hc : DifferentiableAt ℝ c a)
    (hR : DifferentiableAt ℝ R a) (hx : DifferentiableAt ℝ x a) (hne : x a ≠ c a) :
    DifferentiableAt ℝ (fun a ↦ inversion (c a) (R a) (x a)) a := by
  rw [← differentiableWithinAt_univ] at *
  exact hc.inversion hR hx hne

protected theorem Differentiable.inversion (hc : Differentiable ℝ c)
    (hR : Differentiable ℝ R) (hx : Differentiable ℝ x) (hne : ∀ a, x a ≠ c a) :
    Differentiable ℝ (fun a ↦ inversion (c a) (R a) (x a)) := fun a ↦
  (hc a).inversion (hR a) (hx a) (hne a)

end DotNotation

namespace EuclideanGeometry

variable {a b c d x y z : F} {r R : ℝ}

/-- Formula for the Fréchet derivative of `EuclideanGeometry.inversion c R`. -/
theorem hasFDerivAt_inversion (hx : x ≠ c) :
    HasFDerivAt (inversion c R)
      ((R / dist x c) ^ 2 • (reflection (ℝ ∙ (x - c))ᗮ : F →L[ℝ] F)) x := by
  rcases add_left_surjective c x with ⟨x, rfl⟩
  have : HasFDerivAt (inversion c R) (_ : F →L[ℝ] F) (c + x)
  · simp_rw [inversion, dist_eq_norm, div_pow, div_eq_mul_inv]
    have A := (hasFDerivAt_id (𝕜 := ℝ) (c + x)).sub_const c
    have B := ((hasDerivAt_inv <| by simpa using hx).comp_hasFDerivAt _ A.norm_sq).const_mul
      (R ^ 2)
    exact (B.smul A).add_const c
  refine this.congr_fderiv (LinearMap.ext_on_codisjoint
    (Submodule.isCompl_orthogonal_of_completeSpace (K := ℝ ∙ x)).codisjoint
    (LinearMap.eqOn_span' ?_) fun y hy ↦ ?_)
  · have : ((‖x‖ ^ 2) ^ 2)⁻¹ * (‖x‖ ^ 2) = (‖x‖ ^ 2)⁻¹
    · rw [← div_eq_inv_mul, sq (‖x‖ ^ 2), div_self_mul_self']
    dsimp
    simp only [add_sub_cancel', ContinuousLinearMap.comp_id, neg_smul, smul_neg,
      dist_self_add_left, div_eq_mul_inv, mul_pow, inv_pow, eqOn_singleton,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.neg_apply, innerSL_apply_coe, nsmul_eq_mul, Nat.cast_ofNat,
      two_mul, smul_add, Pi.add_apply, neg_add_rev, add_smul,
      reflection_orthogonalComplement_singleton_eq_neg]
    rw [Pi.smul_apply, Pi.smul_apply, real_inner_self_eq_norm_sq]
    simp only [smul_eq_mul, this, add_neg_cancel_comm_assoc]
  · simp only [id_eq, Function.comp_apply, add_sub_cancel', ContinuousLinearMap.comp_id,
      neg_smul, smul_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_id', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.neg_apply, innerSL_apply_coe, nsmul_eq_mul, Nat.cast_ofNat,
      dist_self_add_left, div_eq_mul_inv, mul_pow, inv_pow, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, reflection_mem_subspace_eq_self hy, add_right_eq_self,
      neg_eq_zero, smul_eq_zero]
    rw [Pi.smul_apply, Pi.smul_apply]
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right.1 hy,
      reflection_mem_subspace_eq_self hy, div_eq_mul_inv, mul_pow]


end EuclideanGeometry
