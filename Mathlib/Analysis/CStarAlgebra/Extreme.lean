/-
Copyright (c) 2026 Monica Omar, Jireh Loreaux, Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar, Jireh Loreaux, Jon Bannon
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Convex.Extreme

/-! # Extreme points of the closed unit ball in C⋆-algebras

This file contains results on the extreme points of the closed unit ball in (unital) C⋆-algebras.

## References

[C⋆-algebras and W⋆-algebras][sakai1971] -/

public section

open Set Metric CFC CStarAlgebra Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The star projections in a non-unital C⋆-algebra are exactly the extreme points of
the nonnegative closed unit ball. -/
theorem isStarProjection_iff_mem_extremePoints_setOf_nonneg_inter_unitClosedBall
    [PartialOrder A] [StarOrderedRing A] {e : A} :
    IsStarProjection e ↔ e ∈ extremePoints ℝ ({x : A | 0 ≤ x} ∩ closedBall 0 1) := by
  simp only [mem_closedBall_zero_iff, mem_extremePoints_iff_left, mem_inter_iff,
    mem_setOf_eq, and_imp]
  refine ⟨fun he ↦ ⟨⟨he.nonneg, he.norm_le⟩,
    fun a ha ha1 b hb hb1 ⟨t, s, h0t, h0s, hts, hlin⟩ ↦ ?_⟩, fun ⟨⟨h1, h2⟩, h3⟩ ↦ ?_⟩
  · /- Suppose `e` is a star projection, and `a` and `b` are in the nonnegative closed unit ball
    such that `t • a + s • b = e` where `t` and `s` are positive.
    Then we want to show `a = e`.
    As `t • a + s • b = e`, we have that in the unitization
    `t • (e * (1 - a) * e)) + s • (e * (1 - b) * e) = 0`.
    And as `a` and `b` are in the nonnegative closed unit ball, we get `1 - a` and
    `1 - b` are nonnegative (and so are `e * (1 - a) * e` and `e * (1 - b) * e`).
    Then `t • (e * (1 - a) * e)) ≤ t • (e * (1 - a) * e)) + s • (e * (1 - b) * e) = 0`,
    and so `t • (e * (1 - a) * e)) = 0`.
    Note that we also get `0 ≤ t • a ≤ t • a + s • b = e` and so `t • e * a * e = t • a` using
    `IsStarProjection.conjugate_of_nonneg_of_le`.
    And so the result then follows. -/
    have ⟨ha01, hb01⟩ : (a : A⁺¹) ∈ Icc 0 1 ∧ (b : A⁺¹) ∈ Icc 0 1 := by
      grind [inr_mem_Icc_iff_norm_le]
    suffices t • (e * (1 - a : A⁺¹) * e) = 0 by
      rw [← h0t.ne'.isUnit.smul_left_cancel, ← he.conjugate_of_nonneg_of_le
          (smul_nonneg h0t.le ha) ?hae]
      case hae => simpa [hlin] using le_add_of_nonneg_right (a := t • a) (by positivity : 0 ≤ s • b)
      apply inr_injective (R := ℂ) <| Eq.symm ?_
      simpa only [mul_one_sub_mul, he.inr.isIdempotentElem.eq, smul_sub, sub_eq_zero,
        smul_mul_assoc, mul_smul_comm, smul_sub, inr_mul, inr_smul]
    apply le_antisymm ?_ <| smul_nonneg h0t.le <| he.inr.isSelfAdjoint.conjugate_nonneg <| by
      simpa using ha01.2
    calc
      _ ≤ t • (e * (1 - a : A⁺¹) * e) + s • (e * (1 - b) * e) := by
        refine le_add_of_nonneg_right <| smul_nonneg h0s.le ?_
        simpa [mul_one_sub_mul] using he.inr.isSelfAdjoint.conjugate_le_conjugate <|
          norm_le_one_iff_of_nonneg (b : A⁺¹) (by simpa) |>.mp (by simpa [norm_inr])
      _ = e - e * (t • a + s • b) * e := by
        simp only [mul_one_sub_mul, he.inr.isIdempotentElem.eq, smul_sub, mul_add,
          Algebra.mul_smul_comm, add_mul, Algebra.smul_mul_assoc]
        match_scalars <;> grind
      _ = 0 := by simp [← inr_smul, ← inr_add, hlin, ← inr_mul, he.isIdempotentElem.eq]
  · /- Now suppose `e` is an extreme point of the nonnegative closed unit ball.
    So then it is self-adjoint, and so we only need to show `e * e = e`.
    Note that since `0 ≤ e ≤ 1` in the unitization, we also get `0 ≤ e * (2 - e) = 2 • e - e * e`,
    and `0 ≤ star (1 - e) * (1 - e) = 1 - 2 • e - e * e` which means `2 • e - e * e` is in the
    closed unit ball. So `2 • e - e * e` is in the nonnegative closed unit ball.
    Then using the extremity of `e`, we get `e * e = e` since `e * e` is obviously in the
    nonnegative closed unit ball, and `e = 2⁻¹ • e * e + 2⁻¹ • (2 • e - e * e)`. -/
    have := calc
      0 ≤ (e : A⁺¹) * (2 - e) := by
        have : (e : A⁺¹) ≤ 1 := norm_le_one_iff_of_nonneg _ (by simpa) |>.mp (by simpa [norm_inr])
        apply Commute.mul_nonneg (by simpa) (by grw [sub_nonneg, this, one_le_two])
        simp [commute_iff_eq, mul_sub, sub_mul, mul_two, two_mul]
      _ = (((2 : ℝ) • e - e * e : A) : A⁺¹) := by simp [mul_sub, two_smul, mul_two]
    refine ⟨h3 _ (Commute.mul_nonneg h1 h1 rfl) ?_ ((2 : ℝ) • e - e * e) this.of_inr ?_
      ⟨2⁻¹, 2⁻¹, by simp [smul_sub, ← one_div, smul_smul]⟩, h1.isSelfAdjoint⟩
    · grw [norm_mul_le, h2, one_mul]
    · rw [← norm_inr (𝕜 := ℂ), norm_le_one_iff_of_nonneg _ this, ← sub_nonneg]
      calc 0 ≤ star (1 - e : A⁺¹) * (1 - e) := star_mul_self_nonneg _
        _ = _ := by simp [LE.le.star_eq, h1, mul_sub, sub_mul, two_smul, sub_sub, add_sub]
