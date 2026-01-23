/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`, we have
`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation Notes

The proof applies the Schwarz lemma to the transformed function `fun z ↦ f z / (2 * M - f z)`,
which maps the ball `|z| < R` into the unit disk provided that `(f z).re < M` for all `|z| < R`.
After obtaining bounds on `w`, we invert the transformation to recover bounds on `f`.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric

namespace Complex

variable {f : ℂ → ℂ} {s : Set ℂ} {M R : ℝ} {z w : ℂ}

section SchwarzTransform

/-- If `w = z / (2M - z)`, then `z = 2M * w / (1 + w)`. This is the inverse of the
Schwarz transform used in the proof of the Borel-Carathéodory theorem. -/
lemma eq_mul_div_one_add_of_eq_div_sub (_ : M ≠ 0) (_ : 2 * M - z ≠ 0)
    (h : w = z / (2 * M - z)) : z = 2 * M * w / (1 + w) := by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

/-- Norm inequality for the inverse Schwarz transform: if `‖w‖ < 1`, then
`‖2M * w / (1 + w)‖ ≤ 2M * ‖w‖ / (1 - ‖w‖)`. -/
lemma norm_two_mul_div_one_add_le (hM : 0 < M) (hw : ‖w‖ < 1) :
    ‖2 * ↑M * w / (1 + w)‖ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr; · linarith
  rw [← norm_one (α := ℂ)]; exact norm_sub_le_norm_add 1 w

/-- If `z.re < M`, then `‖z‖ < ‖2M - z‖`. This shows that the Schwarz transform
`z ↦ z / (2M - z)` has numerator smaller than denominator when the real part is bounded by M -/
lemma norm_lt_norm_two_mul_sub (_ : 0 < M) (_ : z.re < M) : ‖z‖ < ‖2 * M - z‖ := by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re < (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

/-- Application of the Schwarz lemma to the transformed function. If `f` is differentiable on
the ball, maps into `{z | z.re < M}`, and satisfies `f 0 = 0`, then the Schwarz transform
satisfies the bound from the Schwarz lemma. -/
private lemma schwarz_applied (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hz : z ∈ ball 0 R) (hf₂ : f 0 = 0) :
    ‖f z / (2 * M - f z)‖ ≤ (1 / R) * ‖z‖ := by
  rw [← dist_zero_right, ← dist_zero_right]
  nth_rw 1 [← zero_div (2 * M - f 0), ← hf₂]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ (fun x hx ↦ ?_) hz
  · apply hf.div (hf.const_sub _) fun x hx h ↦ ?_
    have := sub_eq_zero.mp h ▸ hf₁ hx
    aesop
  · simpa [hf₂] using
      div_le_one_of_le₀ (norm_lt_norm_two_mul_sub hM (hf₁ hx)).le (by positivity)

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re < M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory_zero (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
  set w := f z / (2 * M - f z)
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hwR := by simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div]
    using schwarz_applied hM hf hf₁ hz hf₂
  have h_denom : 2 * M - f z ≠ 0 := sub_ne_zero_of_ne (fun h => by simpa [← h, hM] using hf₁ hz)
  calc ‖f z‖
    _ = ‖2 * M * w / (1 + w)‖ := by rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' h_denom rfl]
    _ ≤ 2 * M * ‖w‖ / (1 - ‖w‖) := by
      simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
      gcongr
      · linarith [hwR.trans_lt ((div_lt_one₀ hR).mpr hzR)]
      · simpa using norm_sub_le_norm_add 1 w
    _ = 2 * M * (‖w‖ / (1 - ‖w‖)) := by ring
    _ ≤ 2 * M * (‖z‖ / R / (1 - ‖z‖ / R)) := by gcongr; simpa [div_lt_one hR]
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re < M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re < M}) (hR : 0 < R) (hz : z ∈ ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  have hfz : ‖f z - f 0‖ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (by positivity) (by fun_prop) ?_ hR hz (by simp)
    intro x hx
    simp only [Set.mem_setOf_eq, sub_re]
    calc (f x).re - (f 0).re < M - (f 0).re := by gcongr; exact hf₁ hx
      _ ≤ M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  have h_denom_ne : R - ‖z‖ ≠ 0 := by linarith [mem_ball_zero_iff.mp hz]
  calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by field_simp; ring

/-!
### Corollaries

These allow non-strict bounds on the real part, and producing a uniform bound
on a smaller closed ball.
-/

/-- A closed-ball, non-strict-inequality corollary of `Complex.borelCaratheodory_zero`.

If `f` is analytic in a neighbourhood of the closed ball of radius `R`, satisfies `f 0 = 0`,
and has real part bounded above by `M` on `‖z‖ ≤ R`, then on the smaller closed ball `‖z‖ ≤ r`
we have a uniform norm bound `‖f z‖ ≤ 2 * M * r / (R - r)`. -/
public theorem borelCaratheodory_zero_closedBall {f : ℂ → ℂ} {r R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hM : 0 < M)
    (hf0 : f 0 = 0)
    (hf_re : ∀ z, ‖z‖ ≤ R → (f z).re ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖f z‖ ≤ 2 * M * r / (R - r) := by
  intro z hz
  have hRpos : 0 < R := lt_trans hr hR
  have hRrpos : 0 < R - r := sub_pos.2 hR
  have hz_lt_R : ‖z‖ < R := lt_of_le_of_lt hz hR
  have hf_diffOn : DifferentiableOn ℂ f (ball 0 R) := by
    intro w hw
    have hw' : w ∈ closedBall (0 : ℂ) R := by
      have : ‖w‖ ≤ R := le_of_lt (by simpa [mem_ball, dist_zero_right] using hw)
      simpa [mem_closedBall, dist_zero_right] using this
    exact (hf w hw').differentiableAt.differentiableWithinAt
  have hz_ball : z ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_zero_right] using hz_lt_R
  have hbc_eps :
      ∀ ε : ℝ, 0 < ε → ‖f z‖ ≤ 2 * (M + ε) * r / (R - r) := by
    intro ε hε
    have hf_mapsTo :
        Set.MapsTo f (ball (0 : ℂ) R) {w : ℂ | w.re < M + ε} := by
      intro w hw
      have hw_norm_le : ‖w‖ ≤ R := le_of_lt (by simpa [mem_ball, dist_zero_right] using hw)
      have hw_re : (f w).re ≤ M := hf_re w hw_norm_le
      exact lt_of_le_of_lt hw_re (lt_add_of_pos_right _ hε)
    have hz_bc :
        ‖f z‖ ≤ 2 * (M + ε) * ‖z‖ / (R - ‖z‖) :=
      Complex.borelCaratheodory_zero (f := f) (R := R) (M := M + ε)
        (by positivity) hf_diffOn hf_mapsTo hRpos hz_ball hf0
    have hden_le : R - r ≤ R - ‖z‖ := by linarith [hz]
    have hfrac₁ : ‖z‖ / (R - ‖z‖) ≤ ‖z‖ / (R - r) :=
      div_le_div_of_nonneg_left (norm_nonneg z) hRrpos hden_le
    have hfrac₂ : ‖z‖ / (R - r) ≤ r / (R - r) :=
      div_le_div_of_nonneg_right hz (le_of_lt hRrpos)
    have hfrac : ‖z‖ / (R - ‖z‖) ≤ r / (R - r) := hfrac₁.trans hfrac₂
    have hmul :
        (2 * (M + ε)) * (‖z‖ / (R - ‖z‖)) ≤ (2 * (M + ε)) * (r / (R - r)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    have hz_bc' :
        2 * (M + ε) * ‖z‖ / (R - ‖z‖) ≤ 2 * (M + ε) * r / (R - r) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hz_bc.trans hz_bc'
  have hlim : ∀ ε : ℝ, 0 < ε → ‖f z‖ ≤ (2 * M * r / (R - r)) + ε := by
    intro ε hε
    set δ : ℝ := ε * (R - r) / (2 * r)
    have hδ : 0 < δ := by
      have h2rpos : 0 < (2 * r : ℝ) := by nlinarith [hr]
      exact div_pos (mul_pos hε hRrpos) h2rpos
    have hbc := hbc_eps δ hδ
    have hEq : 2 * (M + δ) * r / (R - r) = (2 * M * r / (R - r)) + ε := by
      have h2r : (2 * r : ℝ) ≠ 0 := by nlinarith [hr.ne']
      have hRr : (R - r) ≠ 0 := hRrpos.ne'
      dsimp [δ]
      field_simp [h2r, hRr]
    simpa [hEq] using hbc
  exact le_of_forall_pos_le_add (fun ε hε => hlim ε hε)

end BorelCaratheodory

end Complex
