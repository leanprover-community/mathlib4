/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Fixed points of isometries of the upper half-plane

In this file we show that the scalar multiplication by an element `g : SL (Fin 2) ℝ`
has the following set of fixed points, depending on `g`.

- if `g` preserves orientation (i.e., has a positive determinant) and is an elliptic matrix,
  then `z ↦ g • z` has a unique fixed point;
- if `g` is a scalar matrix, then it acts by the identity map (proved upstream of this file);
- if `g` preserves orientation, but it is neither a sclar matrix, nor an elliptic map,
  then it has no fixed points;
- if `g` reverses orientation and has zero trace, then it has a geodesic line of fixed points;
  - if `g 1 0 = 0`, then this is the vertical line `re z = g 0 1 / (2 * g 1 1)`;
  - otherwise, it's a half-circle with a center at the real axis;
- if `g` reverses orientation and has a nonzero trace, then it has no fixed points.

As a corollary of this classification, we conclude that `PSL(2, ℝ)` acts faithfully
on the upper half-plane.
-/

open Matrix
open scoped MatrixGroups ComplexConjugate

public noncomputable section

namespace UpperHalfPlane

section GLAction

variable {g : GL (Fin 2) ℝ} {z w : ℍ}

theorem gl_smul_eq_iff_num_eq :
    g • z = w ↔ num g z = σ g w * denom g z := by
  rw [← (σ_bijective g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

/-- If the action of a matrix `!![a, b; c, d]`, `a * d - b * c < 0`, on the upper half plane
has a fixed point, then `a + d = 0`. -/
theorem add_eq_zero_of_gl_smul_eq_self_of_det_neg (h : g.val.det < 0) (him : g • z = z) :
    g 0 0 + g 1 1 = 0 := by
  rw [gl_smul_eq_iff_num_eq] at him
  linear_combination (norm := { simp [σ, h.not_gt, num, denom, z.im_ne_zero, field] })
    congr($(him).im / z.im)

theorem gl_smul_eq_self_iff_re_eq (h : g.val.det < 0) (hadd : g 0 0 + g 1 1 = 0) (hc : g 1 0 = 0) :
    g • z = z ↔ z.re = g 0 1 / (2 * g 1 1) := by
  rw [← eq_neg_iff_add_eq_zero] at hadd
  have h₀ : g 1 1 ≠ 0 := by
    intro h₀
    simp [Matrix.det_fin_two, h₀, hc, hadd] at h
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, hadd, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff, h₀]
  grind

theorem gl_smul_eq_self_iff_dist_sq_eq (h : g.val.det < 0) (hadd : g 0 0 + g 1 1 = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) ^ 2 = (-g.val.det) / g 1 0 ^ 2 := by
  rw [← eq_neg_iff_add_eq_zero] at hadd
  rw [eq_div_iff (by positivity), dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    gl_smul_eq_iff_num_eq, σ, g.val_det_apply, if_neg h.not_gt]
  simp [num, denom, Complex.ext_iff, hadd, Matrix.det_fin_two, field]
  grind

theorem gl_smul_eq_self_iff_dist_eq (h : g.val.det < 0) (hadd : g 0 0 + g 1 1 = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) = √(-g.val.det) / |g 1 0| := by
  rw [gl_smul_eq_self_iff_dist_sq_eq h hadd hc, eq_comm, ← Real.sqrt_eq_iff_eq_sq, eq_comm,
    Real.sqrt_div', Real.sqrt_sq_eq_abs]
  · apply sq_nonneg
  · exact div_nonneg (by simpa using h.le) (sq_nonneg _)
  · apply dist_nonneg

/-- An orientation-reversing isometry of the hyperbolic plane has a fixed point
iff the corresponding matrix has zero trace. -/
theorem exists_gl_smul_eq_self_iff_trace_eq_zero (h : g.val.det < 0) :
    (∃ z : ℍ, g • z = z) ↔ g.val.trace = 0 := by
  rw [Matrix.trace_fin_two]
  constructor
  · rintro ⟨z, hz⟩
    exact add_eq_zero_of_gl_smul_eq_self_of_det_neg h hz
  · intro hadd
    by_cases hc : g 1 0 = 0
    · use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · use ⟨⟨-g 1 1 / g 1 0, √(-g.val.det) / |g 1 0|⟩, by simp [*]⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, div_pow, h.le]

theorem c_ne_zero_of_pos_of_gl_smul_eq_self (h : 0 < g.val.det) (hz : g • z = z)
    (hgc : g ∉ Subgroup.center _) :
    g 1 0 ≠ 0 := by
  intro hc
  simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero] at hz
  grind

theorem gl_smul_eq_self_iff_quadratic (h : 0 < g.val.det) :
    g • z = z ↔ (g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + -g 0 1 : ℂ) = 0 := by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

theorem isElliptic_of_exists_smul_eq_self (h : 0 < g.val.det) (hgc : g ∉ Subgroup.center _)
    (hfix : ∃ z : ℍ, g • z = z) : g.IsElliptic := by
  rcases hfix with ⟨z, hz⟩
  have hc := c_ne_zero_of_pos_of_gl_smul_eq_self h hz hgc
  refine lt_of_not_ge fun hge ↦ ?_
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h, quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  norm_cast at hz
  simp only [z.ne_ofReal, false_or] at hz

/-- The unique fixed point of an orientation-preserving elliptic matrix acting on `ℍ`. -/
def fixedPt (g : GL (Fin 2) ℝ) (hell : g.IsElliptic) : ℍ :=
  ⟨(g 0 0 - g 1 1) / (2 * g 1 0) + .I * (√(-g.val.discr) / (2 * |g 1 0|)), by
    simpa [div_pos, Complex.div_re, Complex.div_im, hell.c_ne_zero]⟩

@[simp]
theorem fixedPt_neg (hg : (-g).IsElliptic) :
    fixedPt (-g) hg = fixedPt g (isElliptic_neg_iff.mp hg) := by
  ext
  simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]
  ring

theorem gl_smul_eq_self_iff_eq_fixedPt (hpos : 0 < g.val.det) (hell : g.IsElliptic) :
    g • z = z ↔ z = fixedPt g hell := by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos, quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · simp [fixedPt, UpperHalfPlane.ext_iff, abs_of_pos hc, field]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im, h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]

theorem gl_smul_I_eq_I_iff_of_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    g • I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, if_pos hg]
  simp [Complex.ext_iff, num, denom, and_comm]

theorem gl_smul_I_eq_I_iff_of_neg {g : GL (Fin 2) ℝ} (hg : g.det.val < 0) :
    g • I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, if_neg (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

theorem forall_smul_eq_self_iff_mem_center {g : GL (Fin 2) ℝ} :
    (∀ z : ℍ, g • z = z) ↔ g ∈ Subgroup.center _ := by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq hlt (by simp [ha]) hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨-g 1 1 / g 1 0, 1 + √(-g.val.det) / |g 1 0|⟩, this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt (by simp [ha]) hc, Complex.dist_eq_re_im,
          Real.sqrt_sq this.le] at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

end GLAction

instance : FaithfulSMul PGL(2, ℝ) ℍ := by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

end UpperHalfPlane
