/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao, Moritz Doll
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

* `SchwartzMap.tendsto_smulLeftCLM_comp_smul`: if `g` is Schwartz function and equal to `1` at `0`,
  then `(fun x ↦ g (ε • x)) • f → f` in the Schwartz topology as `ε → 0`.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported Schwartz functions are dense.

-/

public noncomputable section

open scoped Topology ContDiff
open Filter Metric Real Finset Function

namespace SchwartzMap

variable {ι 𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable (f : 𝓢(E, F)) {g : 𝓢(E, 𝕜)}

/-- The main estimate for the density argument. -/
private lemma seminorm_smulLeft_sub_le (hg : g 0 = 1) (k n : ℕ) (ε : ℝ) (hr : |ε| ≤ 1) :
    ((smulLeftCLM F (fun x ↦ g (ε • x))) f - f).seminorm 𝕜 k n ≤
      |ε| * (g.seminorm 𝕜 0 1 * f.seminorm 𝕜 (k + 1) n +
        ∑ i ∈ Finset.range n,
          n.choose (i + 1) * g.seminorm 𝕜 0 (i + 1) * f.seminorm 𝕜 k (n - (i + 1))) := by
  refine seminorm_le_bound _ _ _ _ (by positivity) ?_
  intro x
  calc
    _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => (g (ε • x) - 1) • f x) x‖ := by
      congr
      ext y
      rw [sub_apply, smulLeftCLM_apply_apply (by fun_prop)]
      module
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), n.choose i *
        ‖iteratedFDeriv ℝ i (fun x ↦ g (ε • x) - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
      gcongr
      apply norm_iteratedFDeriv_smul_le (f := fun x ↦ g (ε • x) - 1) (g := f) (N := n)
      · have : ContDiff ℝ n g := g.smooth _
        fun_prop
      · apply f.smooth
      · simp
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * n.choose i *
        ‖iteratedFDeriv ℝ i (fun x ↦ g (ε • x) - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
      grind [Finset.mul_sum]
    _ = ‖x‖ ^ k * ‖g (ε • x) - 1‖ * ‖iteratedFDeriv ℝ n f x‖ +
        ∑ i ∈ Finset.range n, ‖x‖ ^ k * (n.choose (i + 1)) *
        ‖iteratedFDeriv ℝ (i + 1) (fun x ↦ g (ε • x) - 1) x‖ *
        ‖iteratedFDeriv ℝ (n - (i + 1)) f x‖ := by
      nth_rw 1 [Finset.sum_range_succ', add_comm]
      simp
    _ ≤ |ε| * g.seminorm 𝕜 0 1 * f.seminorm 𝕜 (k + 1) n +
        ∑ i ∈ Finset.range n, |ε| * n.choose (i + 1) *
        g.seminorm 𝕜 0 (i + 1) * f.seminorm 𝕜 k (n - (i + 1)) := by
      gcongr 1
      · grw [← hg, norm_sub_le_seminorm_mul_norm 𝕜, ← f.le_seminorm 𝕜 _ _ x]
        simp only [sub_zero, norm_smul, Real.norm_eq_abs]
        apply le_of_eq; ring
      · gcongr 1 with i hi
        grw [iteratedFDeriv_sub_const_apply (by simp)]
        rw [iteratedFDeriv_comp_const_smul _ (g.smooth _), norm_smul, norm_pow, Real.norm_eq_abs]
        have : |ε| ^ (i + 1) ≤ |ε| := by
          grw [pow_succ, pow_le_one₀ (by simp) hr]
          simp
        grw [this, ← f.le_seminorm 𝕜 _ _ x, ← g.le_seminorm 𝕜 _ _ (ε • x)]
        apply le_of_eq; ring
    _ = _ := by
      grind [Finset.mul_sum]

theorem tendsto_smulLeftCLM_comp_smul_sub (hg : g 0 = 1) :
    Tendsto (fun ε : ℝ ↦ smulLeftCLM F (g <| ε • · ) f - f) (𝓝 0) (𝓝 0) := by
  rw [(schwartz_withSeminorms 𝕜 E F).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  set C := (g.seminorm 𝕜 0 1) * (f.seminorm 𝕜 (k + 1) n) +
    ∑ i ∈ Finset.range n,
      (n.choose (i + 1)) * (g.seminorm 𝕜 0 (i + 1)) * (f.seminorm 𝕜 k (n - (i + 1)))
  rw [Metric.eventually_nhds_iff_ball]
  use min 1 (ε / (C + 1)), by positivity
  intro δ hδ
  obtain ⟨hδ₁, hδ₂⟩ : |δ| < 1 ∧ |δ| < ε / (C + 1) := by simpa using hδ
  calc
    _ ≤ |δ| * C := by
      simp only [schwartzSeminormFamily_apply, sub_zero]
      exact seminorm_smulLeft_sub_le f hg k n δ hδ₁.le
    _ < ε := by
      rw [lt_div_iff₀ (by positivity)] at hδ₂
      grw [← hδ₂]
      gcongr
      simp

/-- Multiplying a Schwartz function `f` by the rescaled cutoff `fun x ↦ φ (ε • x)` converges to
`f` in each Schwartz seminorm as `ε → 0`, when `φ` is smooth, compactly supported, and equal to
`1` near the origin. -/
@[deprecated "use tendsto_smulLeftCLM_comp_smul_sub" (since := "2026-11-05")]
theorem tendsto_seminorm_smulLeftCLM_comp_smul_sub (hg : g 0 = 1) (k n : ℕ) :
    Tendsto (fun ε : ℝ ↦ (smulLeftCLM F (g <| ε • · ) f - f).seminorm 𝕜 k n) (𝓝 0) (𝓝 0) := by
  have : Continuous (SchwartzMap.seminorm 𝕜 k n : 𝓢(E, F) → ℝ) :=
    (schwartz_withSeminorms 𝕜 E F).continuous_seminorm (k, n)
  convert (this.tendsto _).comp (tendsto_smulLeftCLM_comp_smul_sub f hg)
  · simp
  · simp

/-- As `ε → 0`, multiplying `f` by the rescaled cutoff `fun x ↦ g (ε • x)` converges to `f` in
the Schwartz topology, for any Schwartz function `g` with `g 0 = 1`. -/
theorem tendsto_smulLeftCLM_comp_smul (hg : g 0 = 1) :
    Tendsto (fun ε : ℝ ↦ smulLeftCLM F (g <| ε • · ) f) (𝓝 0) (𝓝 f) := by
  suffices Tendsto (fun ε : ℝ ↦ (smulLeftCLM F (g <| ε • · ) f - f) + f) (𝓝 0) (𝓝 (0 + f)) by
    simpa
  exact (tendsto_smulLeftCLM_comp_smul_sub f hg).add tendsto_const_nhds

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport [FiniteDimensional ℝ E] :
    Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  intro f
  set b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩ with hb
  set b' := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hb' : b' 0 = 1 := b.eventuallyEq_one.eq_of_nhds
  refine mem_closure_of_tendsto ((tendsto_smulLeftCLM_comp_smul f hb').mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hcs : HasCompactSupport (fun x ↦ b (ε • x)) := b.hasCompactSupport.comp_smul hε
  simp only [HasCompactSupport.toSchwartzMap_toFun, b']
  rw [smulLeftCLM_apply <| hcs.hasTemperateGrowth (by fun_prop)]
  exact hcs.smul_right

end SchwartzMap
