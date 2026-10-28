/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compactly supported functions are dense in Schwartz space

This file shows that the compactly supported Schwartz functions are dense in `𝓢(E, F)`, by
multiplying a Schwartz function by a rescaled smooth cutoff.

## Main statements

* `SchwartzMap.tendsto_smulLeftCLM_comp_smul`: if `φ` is smooth, compactly supported, and equal
  to `1` near the origin, then `(fun x ↦ φ (ε • x)) • f → f` in the Schwartz topology as `ε → 0`.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported Schwartz functions are dense.

-/

public noncomputable section

open scoped Topology ContDiff
open Filter Metric Real Finset Function

namespace SchwartzMap

variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ1 : φ =ᶠ[𝓝 0] 1)
  (f : 𝓢(E, F))

include hφ hφc hφ1 in
/-- Multiplying a Schwartz function `f` by the rescaled cutoff `fun x ↦ φ (ε • x)` converges to
`f` in each Schwartz seminorm as `ε → 0`, when `φ` is smooth, compactly supported, and equal to
`1` near the origin. -/
lemma tendsto_seminorm_smulLeftCLM_comp_smul_sub (k n : ℕ) :
    Tendsto
      (fun ε : ℝ ↦ (smulLeftCLM F (fun x ↦ φ (ε • x)) f - f).seminorm ℝ k n) (𝓝 0) (𝓝 0) := by
  obtain ⟨r, hr, hφr⟩ := eventually_nhds_iff_ball.mp hφ1
  obtain ⟨A, hA0, hA⟩ := hφc.exists_bound_iteratedFDeriv hφ n
  have hψ : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (fun z ↦ φ z - 1) y‖ ≤ A + 1 := by
    rintro (- | i) hi y
    · grind [norm_iteratedFDeriv_zero, norm_sub_le, norm_one, hA 0 hi y]
    · rw [fun_iteratedFDeriv_sub_apply (hφ.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
        iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
      linarith [hA _ hi y]
  refine squeeze_zero' (g := fun ε ↦
      ‖ε‖ * (∑ i ∈ range (n + 1), n.choose i * (A + 1) * f.seminorm ℝ (k + 1) (n - i)) / r)
    (.of_forall fun _ ↦ apply_nonneg _ _) ?_
    (by simpa only [zero_mul, zero_div] using (tendsto_norm_zero.mul_const _).div_const r)
  filter_upwards [closedBall_mem_nhds (0 : ℝ) one_pos] with ε hε
  have hg : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ ≤ A + 1 := by
    intro i hi x
    rw [iteratedFDeriv_comp_const_smul (f := fun z ↦ φ z - 1) _
      ((hφ.sub contDiff_const).of_le (mod_cast le_top)), norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hε))).trans (hψ i hi _)
  have hsmul : ⇑(smulLeftCLM F (fun x ↦ φ (ε • x)) f - f) = fun x ↦ (φ (ε • x) - 1) • f x := by
    ext x
    simp [show (fun x ↦ φ (ε • x)).HasTemperateGrowth by fun_prop, sub_smul]
  refine seminorm_le_bound ℝ k n _ (by positivity) fun x ↦ ?_
  rw [hsmul, le_div_iff₀ hr]
  rcases lt_or_ge ‖ε • x‖ r with hx | hx
  · have : (fun y ↦ (φ (ε • y) - 1) • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isOpen_ball.preimage (continuous_const_smul ε)).mem_nhds
        (mem_ball_zero_iff.mpr hx)] with y hy
      simp [hφr (ε • y) hy]
    calc
      _ = (0 : ℝ) := by simp [(this.iteratedFDeriv ℝ n).eq_of_nhds]
      _ ≤ _ := by positivity
  · rw [norm_smul] at hx
    calc
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖ * (‖ε‖ * ‖x‖) := by
          gcongr
      _ ≤ ‖ε‖ * ∑ i ∈ range (n + 1), n.choose i *
            ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ *
            (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
          grw [norm_iteratedFDeriv_smul_le (by fun_prop) (f.smooth ⊤) x (mod_cast le_top)]
          simp only [mul_sum, sum_mul]
          exact (sum_congr rfl fun _ _ ↦ by ring).le
      _ ≤ _ := by
          gcongr with i hi
          · exact hg i (by grind) x
          · exact le_seminorm ℝ _ _ f x

include hφ hφc hφ1 in
/-- As `ε → 0`, multiplying `f` by the rescaled cutoff `fun x ↦ φ (ε • x)` converges to `f` in
the Schwartz topology, for any smooth, compactly supported `φ` equal to `1` near the origin. -/
theorem tendsto_smulLeftCLM_comp_smul :
    Tendsto (fun ε : ℝ ↦ smulLeftCLM F (fun x ↦ φ (ε • x)) f) (𝓝 0) (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ δ hδ
  simpa using (tendsto_seminorm_smulLeftCLM_comp_smul_sub hφ hφc hφ1 f k n).eventually
    (isOpen_Iio.mem_nhds hδ)

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport [FiniteDimensional ℝ E] :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  intro f
  set b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩ with hb
  refine mem_closure_of_tendsto ((tendsto_smulLeftCLM_comp_smul b.contDiff b.hasCompactSupport
    b.eventuallyEq_one f).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hcs : HasCompactSupport (fun x ↦ b (ε • x)) := b.hasCompactSupport.comp_smul hε
  rw [smulLeftCLM_apply <| hcs.hasTemperateGrowth <| b.contDiff.comp <| contDiff_const_smul _]
  exact hcs.smul_right

end SchwartzMap
