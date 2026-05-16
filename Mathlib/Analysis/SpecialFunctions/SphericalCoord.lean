/-
Copyright (c) 2026 Anthony Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Wang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Spherical coordinates

We define spherical coordinates similarly to polar coordinates, as an open partial homeomorphism
in `ℝ^3` between `ℝ^3 - (-∞, 0]` and `(0, +∞) × (-π, π) × (0, π)`. Its inverse is given by
`(r, θ, φ) ↦ (r sin φ cos θ, r sin φ sin θ, r cos φ)`.
-/

@[expose] public section

noncomputable section Real

open Real Set

/-- The spherical coordinates are an open partial homeomorphism in `ℝ^3`, mapping
`(r sin φ cos θ, r sin φ sin θ, r cos φ)` to `(r, θ, φ)`. It is a homeomorphism between
`ℝ^3 - (-∞, 0] × ℝ` and `(0, +∞) × (-π, π) × (0, π)`. -/
@[simps]
def sphericalCoord : OpenPartialHomeomorph (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) where
  toFun q := (√(q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2),
    Complex.arg (Complex.equivRealProd.symm (q.1, q.2.1)),
    Complex.arg (Complex.equivRealProd.symm (q.2.2, √(q.1 ^ 2 + q.2.1 ^ 2))))
  invFun p := (p.1 * sin p.2.2 * cos p.2.1, p.1 * sin p.2.2 * sin p.2.1, p.1 * cos p.2.2)
  source := {q | 0 < q.1} ∪ {q | q.2.1 ≠ 0}
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π ×ˢ Ioo 0 π
  map_target' := by
    rintro ⟨r, θ, φ⟩ ⟨hr, hθ, hφ⟩
    dsimp at hr hθ hφ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simp only [ne_eq, cos_zero, mul_one, sin_zero, mul_zero, mem_union, mem_setOf_eq]
      left
      exact Left.mul_pos hr (sin_pos_of_mem_Ioo hφ)
    · simp only [ne_eq, mem_union, mem_setOf_eq, mul_eq_zero, not_or]
      right
      and_intros
      · linarith [mem_Ioi.mp hr]
      · linarith [sin_pos_of_mem_Ioo hφ]
      · simp [sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2, h'θ]
  map_source' := by
    rintro ⟨x, y, z⟩ h
    simp only [Complex.equivRealProd_symm_apply, mem_prod, mem_Ioi, sqrt_pos, mem_Ioo,
      Complex.neg_pi_lt_arg, Complex.arg_lt_pi_iff, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero, Complex.add_im, Complex.mul_im, zero_add, ne_eq, true_and]
    have hpos : 0 < x ^ 2 + y ^ 2 := by
      rcases h with h | h <;> dsimp at h <;> positivity
    and_intros
    · linarith [sq_nonneg z]
    · rcases h with h | h
      · exact Or.inl (le_of_lt h)
      · exact Or.inr h
    · apply Complex.arg_of_im_pos'
      simp [hpos]
    · exact Or.inr (by simp only [sqrt_ne_zero', hpos])
  right_inv' := by
    rintro ⟨r, θ, φ⟩ ⟨hr, hθ, hφ⟩
    ext <;> dsimp at hr hθ hφ ⊢
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq φ,
        ← one_mul (sin φ ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert Complex.arg_mul_cos_add_sin_mul_I (Left.mul_pos hr (sin_pos_of_mem_Ioo hφ))
        ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_sin,
        Complex.ofReal_cos]
      ring
    · have : -π < φ := by linarith [pi_pos, hφ.1]
      convert Complex.arg_mul_cos_add_sin_mul_I hr ⟨this, hφ.2.le⟩
      have : √((r * sin φ * cos θ) ^ 2 + (r * sin φ * sin θ) ^ 2) = r * sin φ := by
        conv_rhs => rw [← sqrt_sq (le_of_lt (Left.mul_pos hr (sin_pos_of_mem_Ioo hφ))),
          ← one_mul ((r * sin φ) ^ 2), ← sin_sq_add_cos_sq θ]
        congr 1
        ring
      simp only [this, Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y, z⟩ h
    have A : √(x ^ 2 + y ^ 2) = ‖x + y * Complex.I‖ := by
      rw [Complex.norm_def, Complex.normSq_add_mul_I]
    have : √(x ^ 2 + y ^ 2) ≠ 0 := by
      rcases h with h | h <;> dsimp at h <;> positivity
    have A' : x + y * Complex.I ≠ 0 := by
      simp_all only [ne_eq, norm_eq_zero, not_false_eq_true]
    have B : √(x ^ 2 + y ^ 2 + z ^ 2) = ‖z + √(x ^ 2 + y ^ 2) * Complex.I‖ := by
      rw [Complex.norm_def, Complex.normSq_add_mul_I, sq_sqrt (by positivity), add_comm]
    have : √(x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := by
      rcases h with h | h <;> dsimp at h <;> positivity
    have B' : z + √(x ^ 2 + y ^ 2) * Complex.I ≠ 0 := by
      simp_all only [ne_eq, mem_union, mem_setOf_eq, norm_eq_zero, not_false_eq_true]
    simp only [Complex.equivRealProd_symm_apply, Complex.sin_arg, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, ← B, Complex.cos_arg A', Complex.add_re, Complex.mul_re, sub_self, ← A,
      Complex.cos_arg B', Prod.mk.injEq]
    field_simp
    trivial
  open_target := isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun (Continuous.fst continuous_snd) continuous_const)
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) ?_
    simp only [Complex.equivRealProd_symm_apply, ne_eq]
    apply ContinuousOn.prodMk <;> apply continuousOn_of_forall_continuousAt <;>
      rintro ⟨x, y, z⟩ h <;> refine Complex.continuousAt_arg ?_ |>.comp (by fun_prop)
    · rcases h with h | h <;> dsimp at h <;> simp [Complex.slitPlane, h]
    · rcases h with h | h <;> dsimp at h <;>
        (norm_num [Complex.slitPlane]; exact Or.inr (by positivity))

@[fun_prop]
theorem continuous_sphericalCoord_symm :
    Continuous sphericalCoord.symm :=
  .prodMk (by fun_prop) (by fun_prop)
