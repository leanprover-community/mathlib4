/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compactly supported functions are dense in Schwartz space

This file shows that the compactly supported Schwartz functions are dense in `𝓢(E, F)`, by
multiplying a Schwartz function by a rescaled smooth cutoff.

## Main statements

* `SchwartzMap.tendsto_smulLeftCLM_comp_smul`: if `φ` is smooth, compactly supported, and equal
  to `1` near the origin, then `fun x ↦ φ (R⁻¹ • x)) • f → f` in the Schwartz topology as
  `R → ∞`.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported Schwartz functions are dense.

-/

public noncomputable section

open scoped Topology ContDiff
open Filter Metric ContinuousLinearMap Real Finset Function

namespace SchwartzMap

variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplying a Schwartz function `f` by the rescaled cutoff `fun x ↦ φ (R⁻¹ • x)` converges to
`f` in each Schwartz seminorm as `R → ∞`, when `φ` is smooth, compactly supported, and equal to
`1` on `ball 0 r`. -/
lemma tendsto_seminorm_smulLeftCLM_comp_smul_sub {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {r : ℝ} (hr : 0 < r) (hφr : ∀ y ∈ ball (0 : E) r, φ y = 1)
    (f : 𝓢(E, F)) (k n : ℕ) :
    Tendsto (fun R : ℝ ↦ (smulLeftCLM F (fun x ↦ φ (R⁻¹ • x)) f - f).seminorm ℝ k n) atTop
      (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := hφc.exists_bound_iteratedFDeriv hφ n
  set C := (A + 1) / r * ∑ i ∈ range (n + 1),
    (n.choose i : ℝ) * SchwartzMap.seminorm ℝ (k + 1) (n - i) f with hCdef
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := (C * ·⁻¹)) tendsto_const_nhds
  · simpa using tendsto_inv_atTop_zero.const_mul C
  · filter_upwards with _ using apply_nonneg _ _
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hR0 : 0 < R := by linarith
  have hcd : ContDiff ℝ ∞ (fun x : E ↦ φ (R⁻¹ • x)) := hφ.comp (contDiff_const_smul _)
  refine seminorm_le_bound ℝ k n _ (by positivity) fun x ↦ ?_
  rw [(by funext; simp [smulLeftCLM_apply_apply
    ((hφc.comp_smul (by positivity)).hasTemperateGrowth hcd), sub_smul] :
    ⇑(smulLeftCLM F (fun x ↦ φ (R⁻¹ • x)) f - f) = fun x ↦ (φ (R⁻¹ • x) - 1) • f x)]
  rcases lt_or_ge ‖x‖ (R * r) with hxR | hxR
  · suffices iteratedFDeriv ℝ n (fun y ↦ (φ (R⁻¹ • y) - 1) • f y) x = 0 by
      rw [this, norm_zero, mul_zero]; positivity
    suffices (fun y ↦ (φ (R⁻¹ • y) - 1) • f y) =ᶠ[𝓝 x] 0 by
      simp [(EventuallyEq.iteratedFDeriv ℝ this n).eq_of_nhds]
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxR] with y hy
    have : R⁻¹ • y ∈ ball 0 r := by
      rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_eq_abs, abs_of_pos hR0,
        inv_mul_lt_iff₀ hR0]
      grind
    simp [hφr _ this]
  · calc
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i) *
            ‖iteratedFDeriv ℝ i (fun y ↦ φ (R⁻¹ • y) - 1) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
          grw [norm_iteratedFDeriv_smul_le (hcd.sub contDiff_const) (f.smooth ⊤) x
            (mod_cast le_top)]
          grind [mul_sum]
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i) * (A + 1) *
            (f.seminorm ℝ (k + 1) (n - i) / (R * r)) := by
          refine sum_le_sum fun i hmem ↦ ?_
          have : ‖iteratedFDeriv ℝ i (fun y ↦ φ (R⁻¹ • y) - 1) x‖ ≤ A + 1 := by
            rcases i.eq_zero_or_pos with rfl | hi
            · have := hA 0 (by omega) (R⁻¹ • x)
              grind [norm_iteratedFDeriv_zero, norm_sub_le, norm_one]
            · have : iteratedFDeriv ℝ i (fun y ↦ φ (R⁻¹ • y) - 1) x
                  = iteratedFDeriv ℝ i (fun y ↦ φ (R⁻¹ • y)) x := by
                rw [(by rfl : (fun y ↦ φ (R⁻¹ • y) - 1) = (fun y ↦ φ (R⁻¹ • y)) - fun _ ↦ 1),
                  iteratedFDeriv_sub_apply (hcd.contDiffAt.of_le (mod_cast le_top))
                    contDiffAt_const,
                  iteratedFDeriv_const_of_ne (by omega)]
                simp
              rw [this, iteratedFDeriv_comp_const_smul _ (hφ.of_le (mod_cast le_top)), norm_smul,
                norm_pow, norm_eq_abs, abs_of_pos (by positivity)]
              have : R⁻¹ ≤ 1 := by rwa [inv_le_one₀ hR0]
              grw [hA i (Nat.lt_succ_iff.mp (mem_range.mp hmem)) (R⁻¹ • x),
                pow_le_one₀ (by positivity) this]
              linarith
          grw [this]
          gcongr
          grw [le_div_iff₀ (by positivity), hxR]
          grind [le_seminorm ℝ (k + 1) (n - i) f x]
      _ = _ := by rw [hCdef, mul_sum, sum_mul]; grind

/-- As `R → ∞`, multiplying `f` by the rescaled cutoff `fun x ↦ φ (R⁻¹ • x)` converges to `f` in
the Schwartz topology, for any smooth, compactly supported `φ` equal to `1` near the origin. -/
theorem tendsto_smulLeftCLM_comp_smul {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφ1 : φ =ᶠ[𝓝 0] 1) (f : 𝓢(E, F)) :
    Tendsto (fun R : ℝ ↦ smulLeftCLM F (fun x ↦ φ (R⁻¹ • x)) f) atTop (𝓝 f) := by
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff_ball.mp hφ1
  have hφr (y) (hy : y ∈ ball 0 r) : φ y = 1 := by simpa using hr' y hy
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  simpa using (tendsto_seminorm_smulLeftCLM_comp_smul_sub hφ hφc hr hφr f k n).eventually
    (isOpen_Iio.mem_nhds hε)

variable [FiniteDimensional ℝ E]

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport : Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  intro f
  set b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩ with hb
  have hφcd : ContDiff ℝ ∞ ⇑b := b.contDiff
  have hφcs : HasCompactSupport ⇑b := b.hasCompactSupport
  have hφ1 : ⇑b =ᶠ[𝓝 0] 1 := by
    filter_upwards [ball_mem_nhds 0 one_pos] with y hy
    exact b.one_of_mem_closedBall (ball_subset_closedBall hy)
  refine mem_closure_of_tendsto (tendsto_smulLeftCLM_comp_smul hφcd hφcs hφ1 f) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hcd : ContDiff ℝ ∞ (fun x : E ↦ b (R⁻¹ • x)) := hφcd.comp (contDiff_const_smul _)
  have hcs : HasCompactSupport (fun x : E ↦ b (R⁻¹ • x)) := hφcs.comp_smul (by positivity)
  suffices (smulLeftCLM F (fun x ↦ b (R⁻¹ • x)) f : E → F) = (fun x ↦ b (R⁻¹ • x)) • f by
    simpa [this] using hcs.smul_right
  funext x
  simp [smulLeftCLM_apply_apply (hcs.hasTemperateGrowth hcd)]

end SchwartzMap
