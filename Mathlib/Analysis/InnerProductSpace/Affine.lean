/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
/-!
# Normed affine spaces over an inner product space
-/

@[expose] public section

variable {𝕜 V P : Type*}

section RCLike
variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped InnerProductSpace

theorem inner_vsub_left_eq_zero_symm {a b : P} {v : V} :
    ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ a, v⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero]

theorem inner_vsub_right_eq_zero_symm {v : V} {a b : P} :
    ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right, neg_eq_zero]

end RCLike

section Real
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped RealInnerProductSpace

/-!
In this section, the first `left`/`right` indicates where the common argument to `vsub` is,
and the section refers to the argument of `inner` that ends up in the `dist`.

The lemma shapes are such that the relevant argument of `inner` remains unchanged,
and that the other `vsub` preserves the position of the unchanging argument. -/

theorem inner_vsub_vsub_left_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_left,
    inner_vsub_right_eq_zero_symm]

theorem inner_vsub_vsub_left_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_left_eq_dist_sq_left_iff, real_inner_comm]

theorem inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_right,
    inner_vsub_right_eq_zero_symm]

theorem inner_vsub_vsub_right_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist b c ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_right_eq_dist_sq_left_iff, real_inner_comm]

/-- Squared distance between two points on lines from a common origin,
given orthogonality of the direction vectors. -/
theorem dist_sq_lineMap_lineMap_of_inner_eq_zero {a b c : P} (t₁ t₂ : ℝ)
    (h_inner : ⟪b -ᵥ a, c -ᵥ a⟫ = 0) :
    dist (AffineMap.lineMap a b t₁) (AffineMap.lineMap a c t₂) ^ 2 =
      t₁ ^ 2 * dist a b ^ 2 + t₂ ^ 2 * dist a c ^ 2 := by
  have hvec : AffineMap.lineMap a b t₁ -ᵥ AffineMap.lineMap a c t₂ =
              t₁ • (b -ᵥ a) - t₂ • (c -ᵥ a) := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, vadd_vsub_vadd_cancel_right]
  rw [dist_eq_norm_vsub V, hvec, norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, inner_smul_left, inner_smul_right, h_inner]
  simp only [mul_zero, sub_zero, mul_pow, sq_abs, ← dist_eq_norm_vsub' V]

/-- Squared distance from `p` to a point on the line from `a` to `b`,
given that `p -ᵥ a` is orthogonal to `b -ᵥ a`. -/
theorem dist_sq_lineMap_of_inner_eq_zero {a b p : P} (t : ℝ)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p (AffineMap.lineMap a b t) ^ 2 = dist p a ^ 2 + t ^ 2 * dist a b ^ 2 := by
  have h := dist_sq_lineMap_lineMap_of_inner_eq_zero (t₁ := 1) (t₂ := t) h_inner
  simp only [AffineMap.lineMap_apply_one, one_pow, one_mul] at h
  rwa [dist_comm a p] at h

/-- **Pythagorean theorem**: if `p -ᵥ a` is orthogonal to `b -ᵥ a`, then
`dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2`. -/
theorem dist_sq_of_inner_eq_zero {a b p : P}
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2 := by
  simpa using dist_sq_lineMap_of_inner_eq_zero 1 h_inner

end Real
