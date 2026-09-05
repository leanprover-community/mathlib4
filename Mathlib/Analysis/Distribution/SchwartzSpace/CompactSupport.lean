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

@[expose] public section

open scoped Topology ContDiff
open Filter Metric ContinuousLinearMap Real Finset Function

noncomputable section

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {R : ℝ} (f : 𝓢(E, F))

/-- A fixed reference bump on `E`: equal to `1` on the closed unit ball, supported in `ball 0 2`. -/
def bumpχ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The reference bump `bumpχ` as a plain function `E → ℝ`. -/
def χ₀ : E → ℝ := bumpχ (E := E)

/-- The reference bump rescaled by `R`: equal to `1` on `ball 0 R`, supported in `ball 0 (2R)`. -/
def bumpR (R : ℝ) (x : E) : ℝ := χ₀ (R⁻¹ • x)

@[simp]
lemma bumpR_eq_one (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : bumpR R x = 1 := by
  refine bumpχ.one_of_mem_closedBall ?_
  grw [mem_closedBall_zero_iff, norm_smul, hx]
  simp [inv_mul_cancel₀ hR.ne', bumpχ, abs_of_pos hR]

lemma bumpR_nonneg (R : ℝ) (x : E) : 0 ≤ bumpR R x := bumpχ.nonneg' _

lemma bumpR_le_one (R : ℝ) (x : E) : bumpR R x ≤ 1 := bumpχ.le_one

@[fun_prop]
lemma contDiff_bumpR (R : ℝ) : ContDiff ℝ ∞ (bumpR R (E := E)) :=
  bumpχ.contDiff.comp (contDiff_const_smul R⁻¹)

lemma support_χ₀ : support χ₀ = ball (0 : E) 2 := bumpχ.support_eq

lemma hasCompactSupport_χ₀ : HasCompactSupport (χ₀ : E → ℝ) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) (isClosed_tsupport _)
    (closure_minimal (support_χ₀.subset.trans ball_subset_closedBall) isClosed_closedBall)

/-- Each iterated derivative of the reference bump `χ₀` is bounded, uniformly over orders `≤ m`. -/
lemma exists_bound_iteratedFDeriv_χ₀ (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i ≤ m, ∀ y : E, ‖iteratedFDeriv ℝ i χ₀ y‖ ≤ A := by
  have key (i) : ∃ A : ℝ, ∀ y : E, ‖iteratedFDeriv ℝ i χ₀ y‖ ≤ A :=
    (bumpχ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_χ₀.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((range (m + 1)).sup' ⟨0, by simp⟩ A), by grind, fun i _ y ↦ ?_⟩
  exact (hA i y).trans (le_max_of_le_right (le_sup' A (by grind)))

lemma support_bumpR (hR : 0 < R) : support (bumpR R (E := E)) ⊆ closedBall (0 : E) (2 * R) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  change R⁻¹ • x ∈ support χ₀ at hx
  simp [support_χ₀, norm_smul, abs_of_pos, inv_mul_lt_iff₀, hR] at hx
  linarith

lemma hasCompactSupport_bumpR (hR : 0 < R) : HasCompactSupport (bumpR R (E := E)) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 (2 * R)) (isClosed_tsupport _)
    (closure_minimal (support_bumpR hR) isClosed_closedBall)

lemma hasTemperateGrowth_bumpR (hR : 0 < R) : HasTemperateGrowth (bumpR R (E := E)) :=
  (hasCompactSupport_bumpR hR).hasTemperateGrowth (contDiff_bumpR R)

/-- The derivatives of `bumpR R` vanish on the ball of radius `R` for `n ≥ 1`. -/
lemma iteratedFDeriv_bumpR_eq_zero (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n) {x : E} (hx : ‖x‖ < R) :
    iteratedFDeriv ℝ n (bumpR R) x = 0 := by
  suffices bumpR R =ᶠ[𝓝 x] fun _ ↦ 1 by
    rw [(EventuallyEq.iteratedFDeriv ℝ this n).eq_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
    rfl
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  exact bumpR_eq_one hR hy.le

/-- Each derivative of `bumpR R = χ₀ (R⁻¹ • ·)` gains a factor `R⁻ⁿ`. -/
lemma norm_iteratedFDeriv_bumpR_le (hR : 0 < R) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (bumpR R) x‖ ≤ R⁻¹ ^ n * ‖iteratedFDeriv ℝ n χ₀ (R⁻¹ • x)‖ := by
  grw [(by aesop : bumpR R = χ₀ ∘ (R⁻¹ • ContinuousLinearMap.id ℝ E)),
    iteratedFDeriv_comp_right _ (f := χ₀) bumpχ.contDiff x le_rfl,
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le, norm_smul, norm_id_le]
  simp [mul_comm, abs_of_pos hR]

/-- The smooth truncation of a Schwartz function `f` by the rescaled bump `bumpR R`. -/
def truncate (R : ℝ) : 𝓢(E, F) := smulLeftCLM F (bumpR R) f

@[simp]
lemma truncate_apply (hR : 0 < R) (x : E) : truncate f R x = bumpR R x • f x :=
  smulLeftCLM_apply_apply (hasTemperateGrowth_bumpR hR) f x

lemma hasCompactSupport_truncate (hR : 0 < R) : HasCompactSupport (truncate f R : E → F) := by
  suffices (truncate f R : E → F) = (bumpR R) • f by
    simpa [this] using (hasCompactSupport_bumpR hR).smul_right
  funext; simp [hR]

private lemma tendsto_seminorm_truncate_sub (k n) :
    Tendsto (fun R ↦ (truncate f R - f).seminorm ℝ k n) atTop (𝓝 0) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_iteratedFDeriv_χ₀ (E := E) n
  set C := (max 1 A) * ∑ i ∈ range (n + 1), (n.choose i) * SchwartzMap.seminorm ℝ (k + 1) (n - i) f
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := (C * ·⁻¹)) tendsto_const_nhds
  · simpa using tendsto_inv_atTop_zero.const_mul C
  · filter_upwards with R using apply_nonneg _ _
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hR0 : 0 < R := by linarith
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  have hRinv1 : R⁻¹ ≤ 1 := by simp [inv_le_one₀ hR0, hR]
  refine seminorm_le_bound ℝ k n _ (by positivity) fun x ↦ ?_
  have : ⇑(truncate f R - f) = fun x ↦ (bumpR R x - 1) • f x := by funext; simp [hR0, sub_smul]
  rw [this]
  rcases lt_or_ge ‖x‖ R with hxR | hxR
  · suffices iteratedFDeriv ℝ n (fun y ↦ (bumpR R y - 1) • f y) x = 0 by
      rw [this, norm_zero, mul_zero]; positivity
    suffices (fun y ↦ (bumpR R y - 1) • f y) =ᶠ[𝓝 x] 0 by
      simp [(EventuallyEq.iteratedFDeriv ℝ this n).eq_of_nhds]
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxR] with y hy
    simp [hR0, hy.le]
  · have : 0 < ‖x‖ := by linarith
    calc
      _ ≤ ‖x‖ ^ k * ∑ i ∈ range (n + 1), (n.choose i) *
            ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
          grw [norm_iteratedFDeriv_smul_le ((contDiff_bumpR R).sub contDiff_const)
            (f.smooth ⊤) x (mod_cast le_top)]
      _ = ∑ i ∈ range (n + 1), (n.choose i) * ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by grind [mul_sum]
      _ ≤ ∑ i ∈ range (n + 1), (n.choose i) * (max 1 A) * (f.seminorm ℝ (k + 1) (n - i) * R⁻¹) := by
          refine sum_le_sum fun i _ ↦ ?_
          suffices ‖iteratedFDeriv ℝ i (bumpR R · - 1) x‖ ≤ max 1 A by
            grw [this, ← le_seminorm ℝ _ _ f x, pow_succ, hxR]
            field_simp; rfl
          rcases i.eq_zero_or_pos with rfl | _
          · grind [norm_iteratedFDeriv_zero, norm_eq_abs, bumpR_nonneg, bumpR_le_one]
          · suffices iteratedFDeriv ℝ i (bumpR R · - 1) x = iteratedFDeriv ℝ i (bumpR R) x by
              grw [this, norm_iteratedFDeriv_bumpR_le hR0, pow_le_one₀ hRinv0 hRinv1,
                hA i (by grind) _]
              grind
            rw [(by rfl : (bumpR R · - 1) = bumpR R - fun _ ↦ 1), iteratedFDeriv_sub_apply
              ((contDiff_bumpR R).contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
              iteratedFDeriv_const_of_ne (by omega)]
            simp
      _ = _ := by simpa [C, mul_sum, sum_mul] using by grind

/-- Smooth truncations converge to `f` in the Schwartz topology as `R → ∞`. -/
lemma tendsto_truncate : Tendsto (truncate f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  simpa using (tendsto_seminorm_truncate_sub f k n).eventually (isOpen_Iio.mem_nhds hε)

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport : Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  refine fun f ↦ mem_closure_of_tendsto (tendsto_truncate f) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR using hasCompactSupport_truncate f hR

end SchwartzMap
