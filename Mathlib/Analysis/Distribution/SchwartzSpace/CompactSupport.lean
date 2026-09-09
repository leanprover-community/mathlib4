/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compactly supported functions are dense in Schwartz space

This file establishes some basic properties of smooth cutoff functions, and uses this to
establish that the compactly supported Schwartz functions are dense in `𝓢(E, F)`.

## Key definitions

* `SchwartzMap.bumpR R`: a smooth cutoff function equal to `1` on the ball of radius `R` and
  supported in the ball of radius `2R`.
* `SchwartzMap.truncate f R`: smooth truncation of a Schwartz function `f` by `bumpR R`.

## Main statements

* `SchwartzMap.dense_hasCompactSupport`: compactly supported Schwartz functions are
  dense.
* `SchwartzMap.tendsto_truncate`: a more explicit version — `truncate f R → f` as `R → ∞`.

-/

public noncomputable section

open scoped Topology ContDiff
open Filter Metric ContinuousLinearMap Real Finset Function

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- Two bump functions centered at `0` with the same ratio `rOut / rIn` are dilations of each other:
`f` is `g` precomposed with scaling by `g.rIn / f.rIn`. -/
theorem toFun_eq_comp_smul {f g : ContDiffBump (0 : E)} (h : f.rOut / f.rIn = g.rOut / g.rIn) :
    (⇑f) = fun x ↦ g ((g.rIn / f.rIn) • x) := by
  ext x
  simp only [ContDiffBump.toFun, Function.comp_apply, sub_zero, h, smul_smul]
  congr 2
  have hf : f.rIn ≠ 0 := f.rIn_pos.ne'
  have hg : g.rIn ≠ 0 := g.rIn_pos.ne'
  field_simp

/-- The iterated derivatives of two bump functions centered at `0` with the same ratio `rOut / rIn`
scale by the dilation factor `g.rIn / f.rIn`. -/
theorem iteratedFDeriv_eq_smul {f g : ContDiffBump (0 : E)}
    (h : f.rOut / f.rIn = g.rOut / g.rIn) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n f x = (g.rIn / f.rIn) ^ n • iteratedFDeriv ℝ n g ((g.rIn / f.rIn) • x) := by
  rw [toFun_eq_comp_smul h, iteratedFDeriv_comp_const_smul _ (g.contDiff.of_le (mod_cast le_top))]

end ContDiffBump

namespace SchwartzMap

variable {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {R : ℝ} (f : 𝓢(E, F))

/-- The reference bump rescaled by `R`: equal to `1` on `ball 0 R`, supported in `ball 0 (2R)`,
built directly from the canonical smooth bump base. The unscaled bump `bumpR 1` plays the role of
a fixed reference bump. -/
def bumpR (R : ℝ) (x : E) : ℝ := (someContDiffBumpBase E).toFun 2 (R⁻¹ • x)

/-- For `R > 0`, `bumpR R` as the standard `ContDiffBump` from `R` to `2 * R`. -/
def bumpCDB (hR : 0 < R) : ContDiffBump (0 : E) := ⟨R, 2 * R, hR, by linarith⟩

/-- For `R > 0`, `bumpR R` agrees with the `ContDiffBump` from `R` to `2 * R`. -/
lemma bumpR_eq (hR : 0 < R) : bumpR R = ⇑(bumpCDB (E := E) hR) := by
  ext x
  simp only [bumpR, bumpCDB, ContDiffBump.toFun, Function.comp_apply, sub_zero]
  congr 2
  field_simp

@[simp]
lemma bumpR_eq_one (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : bumpR R x = 1 := by
  rw [bumpR_eq hR]
  exact (bumpCDB hR).one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff])

lemma bumpR_nonneg R (x : E) : 0 ≤ bumpR R x := ((someContDiffBumpBase E).mem_Icc 2 _).1

lemma bumpR_le_one R (x : E) : bumpR R x ≤ 1 := ((someContDiffBumpBase E).mem_Icc 2 _).2

@[fun_prop]
lemma contDiff_bumpR (hR : 0 < R) : ContDiff ℝ ∞ (bumpR R (E := E)) := by
  rw [bumpR_eq hR]; exact (bumpCDB hR).contDiff

lemma support_bumpR (hR : 0 < R) : support (bumpR R (E := E)) ⊆ closedBall (0 : E) (2 * R) := by
  rw [bumpR_eq hR, (bumpCDB hR).support_eq]; exact ball_subset_closedBall

lemma hasCompactSupport_bumpR (hR : 0 < R) : HasCompactSupport (bumpR R (E := E)) := by
  rw [bumpR_eq hR]; exact (bumpCDB hR).hasCompactSupport

lemma hasTemperateGrowth_bumpR (hR : 0 < R) : HasTemperateGrowth (bumpR R (E := E)) :=
  (hasCompactSupport_bumpR hR).hasTemperateGrowth (contDiff_bumpR hR)

/-- The derivatives of `bumpR R` vanish on the ball of radius `R` for `n ≥ 1`. -/
lemma iteratedFDeriv_bumpR_eq_zero (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (bumpR R) x = 0 := by
  suffices bumpR R =ᶠ[𝓝 x] fun _ ↦ 1 by
    rw [(EventuallyEq.iteratedFDeriv ℝ this n).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
    rfl
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  exact bumpR_eq_one hR hy.le

/-- Each derivative of `bumpR R` is a rescaling of that of `bumpR 1`, via the `ContDiffBump`
dilation lemma `ContDiffBump.iteratedFDeriv_eq_smul` (both bumps have ratio `2`). -/
lemma iteratedFDeriv_bumpR (hR : 0 < R) (n) (x : E) :
    iteratedFDeriv ℝ n (bumpR R) x = R⁻¹ ^ n • iteratedFDeriv ℝ n (bumpR 1) (R⁻¹ • x) := by
  rw [bumpR_eq hR, bumpR_eq one_pos, ContDiffBump.iteratedFDeriv_eq_smul (g := bumpCDB one_pos)]
  <;> grind [bumpCDB]

/-- Each derivative of `bumpR R` gains a factor `R⁻ⁿ`. -/
lemma norm_iteratedFDeriv_bumpR_le (hR : 0 < R) (n) (x : E) :
    ‖iteratedFDeriv ℝ n (bumpR R) x‖ ≤ R⁻¹ ^ n * ‖iteratedFDeriv ℝ n (bumpR 1) (R⁻¹ • x)‖ := by
  rw [iteratedFDeriv_bumpR hR, norm_smul, norm_pow, norm_eq_abs, abs_of_pos (by positivity)]

/-- The smooth truncation of a Schwartz function `f` by the rescaled bump `bumpR R`. -/
def truncate (R : ℝ) : 𝓢(E, F) := smulLeftCLM F (bumpR R) f

@[simp]
lemma truncate_apply (hR : 0 < R) (x : E) : truncate f R x = bumpR R x • f x :=
  smulLeftCLM_apply_apply (hasTemperateGrowth_bumpR hR) f x

lemma hasCompactSupport_truncate (hR : 0 < R) : HasCompactSupport (truncate f R : E → F) := by
  suffices (truncate f R : E → F) = (bumpR R) • f by
    simpa [this] using (hasCompactSupport_bumpR hR).smul_right
  funext; simp [hR]

private lemma tendsto_seminorm_truncate_sub k n :
    Tendsto (fun R ↦ (truncate f R - f).seminorm ℝ k n) atTop (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := (hasCompactSupport_bumpR (E := E) one_pos).exists_bound_iteratedFDeriv
    (contDiff_bumpR one_pos) n
  set C := (max 1 A) * ∑ i ∈ range (n + 1), (n.choose i) * SchwartzMap.seminorm ℝ (k + 1) (n - i) f
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := (C * ·⁻¹)) tendsto_const_nhds
  · simpa using tendsto_inv_atTop_zero.const_mul C
  · filter_upwards with _ using apply_nonneg _ _
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hR0 : 0 < R := by linarith
  refine seminorm_le_bound ℝ k n _ (by positivity) fun x ↦ ?_
  rw [(by funext; simp [hR0, sub_smul] : ⇑(truncate f R - f) = fun x ↦ (bumpR R x - 1) • f x)]
  rcases lt_or_ge ‖x‖ R with hxR | hxR
  · suffices iteratedFDeriv ℝ n (fun y ↦ (bumpR R y - 1) • f y) x = 0 by
      rw [this, norm_zero, mul_zero]; positivity
    suffices (fun y ↦ (bumpR R y - 1) • f y) =ᶠ[𝓝 x] 0 by
      simp [(EventuallyEq.iteratedFDeriv ℝ this n).eq_of_nhds]
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxR] with y hy
    simp [hR0, hy.le]
  · have : 0 < ‖x‖ := by linarith
    calc
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i) * ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
          grw [norm_iteratedFDeriv_smul_le ((contDiff_bumpR hR0).sub contDiff_const)
            (f.smooth ⊤) x (mod_cast le_top)]
          grind [mul_sum]
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i) * (max 1 A) * (f.seminorm ℝ (k + 1) (n - i) * R⁻¹) := by
          refine sum_le_sum fun i _ ↦ ?_
          suffices ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ ≤ max 1 A by
            grw [this, ← le_seminorm ℝ, pow_succ, hxR]
            field_simp; rfl
          rcases i.eq_zero_or_pos with rfl | _
          · grind [norm_iteratedFDeriv_zero, norm_eq_abs, bumpR_nonneg, bumpR_le_one]
          · suffices iteratedFDeriv ℝ i (bumpR R · - 1) x = iteratedFDeriv ℝ i (bumpR R) x by
              grw [this, norm_iteratedFDeriv_bumpR_le, pow_le_one₀]
                <;> grind [inv_le_one₀, inv_nonneg]
            rw [(by rfl : (bumpR R · - 1) = bumpR R - fun _ ↦ 1), iteratedFDeriv_sub_apply
              ((contDiff_bumpR hR0).contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
             iteratedFDeriv_const_of_ne (by omega)]
            simp
      _ = _ := by simpa [C, mul_sum, sum_mul] using by grind

/-- Smooth truncations converge to `f` in the Schwartz topology as `R → ∞`. -/
lemma tendsto_truncate : Tendsto (truncate f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  simpa using (tendsto_seminorm_truncate_sub f k n).eventually (isOpen_Iio.mem_nhds hε)

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport : Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} :=
  fun f ↦ mem_closure_of_tendsto (tendsto_truncate f)
    (by filter_upwards [eventually_gt_atTop 0] with R hR using hasCompactSupport_truncate f hR)

end SchwartzMap
