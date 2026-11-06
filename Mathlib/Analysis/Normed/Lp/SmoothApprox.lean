/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!

# Density of smooth compactly supported functions in `Lp`

In this file, we prove that `Lp` functions can be approximated by smooth compactly supported
functions for `p < ∞`.

This result is recorded in `MeasureTheory.MemLp.exist_eLpNorm_sub_le`.

## Implementation notes

The approximation of a continuous compactly supported function by a smooth one
(`HasCompactSupport.exists_contDiff_norm_sub_le`) is proved directly, by averaging values of `f`
with a smooth partition of unity subordinate to a finite cover of `tsupport f` by small balls
(built from `IsOpen.exists_contDiff_support_eq`), rather than via
`Continuous.exists_contDiff_approx` from `Mathlib.Geometry.Manifold.SmoothApprox`, so that this file
(and hence the Schwartz space and the Fourier transform) does not depend on the manifold library.
-/

public section

variable {α β E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]

open scoped Nat NNReal ContDiff
open MeasureTheory ENNReal Metric Set Function

namespace HasCompactSupport

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A continuous compactly supported function `f` on a finite-dimensional real normed space can be
approximated uniformly, to within `ε`, by a smooth function `g` supported in the `r`-thickening of
`tsupport f`. -/
theorem exists_contDiff_norm_sub_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) :
    ∃ g : E → F, support g ⊆ cthickening r (tsupport f) ∧ ContDiff ℝ ∞ g ∧
      ∀ x, ‖f x - g x‖ ≤ ε := by
  /- Finitely many balls `ball i (min r δ)`, `i ∈ t`, centred in `tsupport f` cover it, where `f`
  varies by at most `ε` on balls of radius `δ`. With `(tsupport f)ᶜ` they form a finite open
  cover `V j`, `j ∈ t'`, of `E`: `‖f - c j‖ ≤ ε` on `V j`, and `V j ⊆ cthickening r (tsupport f)`
  whenever `c j ≠ 0`. -/
  obtain ⟨δ, hδ, hfδ⟩ := uniformContinuous_iff.1 (h₁.uniformContinuous_of_continuous h₂) _ hε
  obtain ⟨t, htf⟩ := h₁.elim_nhds_subcover' (fun x _ ↦ ball x (min r δ)) fun x _ ↦
    ball_mem_nhds x (lt_min hr hδ)
  let V : Option (tsupport f) → Set E := fun j ↦ j.elim (tsupport f)ᶜ fun i ↦ ball i (min r δ)
  let c : Option (tsupport f) → F := fun j ↦ j.elim 0 fun i ↦ f i
  set t' := Finset.insertNone t
  have hV (j) : IsOpen (V j) := by
    rcases j with _ | i
    exacts [(isClosed_tsupport f).isOpen_compl, isOpen_ball]
  -- A smooth partition of unity `v j / ∑ k ∈ t', v k` subordinate to this cover.
  choose v hv_supp hv_smooth hv_range using fun j ↦ (hV j).exists_contDiff_support_eq (n := ⊤)
  have hv (j x) : 0 ≤ v j x := (hv_range j (mem_range_self x)).1
  have hpos (j x) (h : x ∈ V j) : 0 < v j x := (hv j x).lt_of_ne' (by rwa [← mem_support, hv_supp])
  have hc (j x) (hx : v j x ≠ 0) :
      dist (f x) (c j) ≤ ε ∧ (c j ≠ 0 → x ∈ cthickening r (tsupport f)) := by
    revert hx
    rcases j with _ | i <;> intro hx <;> rw [← mem_support, hv_supp] at hx
    · simp [c, image_eq_zero_of_notMem_tsupport hx, hε.le]
    · exact ⟨(hfδ ((mem_ball.1 hx).trans_le (min_le_right _ _))).le, fun _ ↦
        mem_cthickening_of_dist_le x i r _ i.2 ((mem_ball.1 hx).le.trans (min_le_left _ _))⟩
  have hS (x) : 0 < ∑ j ∈ t', v j x := Finset.sum_pos' (fun j _ ↦ hv j x) <| by
    by_cases hx : x ∈ tsupport f
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (htf hx)
      exact ⟨some i, Finset.some_mem_insertNone.2 hi, hpos _ x hxi⟩
    · exact ⟨none, Finset.none_mem_insertNone, hpos none x hx⟩
  -- The approximant is the weighted average `g := ∑ j ∈ t', (v j / ∑ k ∈ t', v k) • c j`.
  refine ⟨fun x ↦ ∑ j ∈ t', (v j x / ∑ k ∈ t', v k x) • c j, fun x hx ↦ ?_,
    by fun_prop (disch := exact fun x ↦ (hS x).ne'), fun x ↦ ?_⟩
  · obtain ⟨j, -, hjx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact (hc j x (div_ne_zero_iff.1 (left_ne_zero_of_smul hjx)).1).2 (right_ne_zero_of_smul hjx)
  · calc ‖f x - ∑ j ∈ t', (v j x / ∑ k ∈ t', v k x) • c j‖
        = ‖∑ j ∈ t', (v j x / ∑ k ∈ t', v k x) • (f x - c j)‖ := by
          simp [smul_sub, ← Finset.sum_smul, ← Finset.sum_div, (hS x).ne']
      _ ≤ ∑ j ∈ t', v j x / (∑ k ∈ t', v k x) * ε := norm_sum_le_of_le _ fun j _ ↦ by
          rw [norm_smul, Real.norm_of_nonneg (div_nonneg (hv j x) (hS x).le), ← dist_eq_norm]
          exact (eq_or_ne (v j x) 0).elim (fun h ↦ by simp [h]) fun h ↦
            mul_le_mul_of_nonneg_left (hc j x h).1 (div_nonneg (hv j x) (hS x).le)
      _ = ε := by rw [← Finset.sum_mul, ← Finset.sum_div, div_self (hS x).ne', one_mul]

/-- For every continuous compactly supported function `f` there exists a smooth compactly supported
function `g` such that `f - g` is arbitrarily small in the `Lp`-norm for `p < ∞`. -/
theorem exist_eLpNorm_sub_le_of_continuous (μ : Measure E := by volume_tac)
    [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  -- It suffices to find a smooth `g` supported in the compact set `s` with `‖f - g‖ ≤ ε'`
  -- everywhere, where `m * ε' ≤ ε` and `μ s ^ p.toReal⁻¹ = ofReal m`.
  set s := cthickening 1 (tsupport f)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ μ s ^ p.toReal⁻¹ = ENNReal.ofReal m :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal <| ENNReal.rpow_ne_top_of_nonneg
      (by positivity) h₁.cthickening.measure_lt_top.ne).symm⟩
  obtain ⟨ε', hε', hε'm⟩ : ∃ ε', 0 < ε' ∧ m * ε' ≤ ε :=
    ⟨ε / (m + 1), by positivity, by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith⟩
  obtain ⟨g, hg_supp, hg_smooth, hg_dist⟩ := h₁.exists_contDiff_norm_sub_le one_pos hε' h₂
  refine ⟨g, .of_support_subset_isCompact h₁.cthickening hg_supp, hg_smooth, ?_⟩
  have hfg := (h₂.sub hg_smooth.continuous).aestronglyMeasurable (μ := μ)
  calc eLpNorm (f - g) p μ = eLpNorm (f - g) p (μ.restrict s) :=
        (eLpNorm_restrict_eq_of_support_subset hfg <| (support_sub f g).trans <| union_subset
          ((subset_tsupport f).trans (self_subset_cthickening _)) hg_supp).symm
    _ ≤ μ s ^ p.toReal⁻¹ * ENNReal.ofReal ε' := by
        simpa using eLpNorm_le_of_ae_bound (p := p) (μ := μ.restrict s) hfg.restrict
          (.of_forall hg_dist)
    _ ≤ ENNReal.ofReal ε := by rw [hm, ← ENNReal.ofReal_mul hm0]; gcongr

end HasCompactSupport

namespace MeasureTheory.MemLp

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- Every `Lp` function can be approximated by a smooth compactly supported function provided that
`p < ∞`. -/
theorem exist_eLpNorm_sub_le {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  -- We use a standard ε / 2 argument to deduce the result from the approximation for
  -- continuous compactly supported functions.
  have hε₂ : 0 < ε / 2 := by positivity
  have hε₂' : 0 < ENNReal.ofReal (ε / 2) := by positivity
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε₂'.ne'
  obtain ⟨g', hg'₁, hg'₂, hg'₃⟩ :=
    hg₁.exist_eLpNorm_sub_le_of_continuous (p := p) μ hε₂ hg₃
  refine ⟨g', hg'₁, hg'₂, ?_⟩
  have : f - g' = (f - g) - (g' - g) := by simp
  grw [this, eLpNorm_sub_le hp₂, hg₂, eLpNorm_sub_comm (f := g') (g := g) (p := p) (μ := μ),
    hg'₃, ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

theorem _root_.MeasureTheory.Lp.dense_hasCompactSupport_contDiff {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp₂ : Fact (1 ≤ p)] :
    Dense {f : Lp F p μ | ∃ (g : E → F), f =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := exist_eLpNorm_sub_le hp hp₂.out (Lp.memLp f) hε
  have hg₄ : MemLp g p μ := hg₂.continuous.memLp_of_hasCompactSupport hg₁
  use hg₄.toLp
  use ⟨g, hg₄.coeFn_toLp, hg₁, hg₂⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp hg₄.toLp)).eLpNorm_ne_top hε.le]
  convert hg₃ using 1
  apply eLpNorm_congr_ae
  gcongr
  exact hg₄.coeFn_toLp

end MeasureTheory.MemLp
