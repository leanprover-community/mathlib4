/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.BumpFunctionFindim

/-!
# Functions which vanish as distributions vanish as functions

In a finite dimensional normed real vector space endowed with a Borel measure, consider a locally
integrable function whose integral against compactly supported smooth functions vanishes. Then
the function is almost everywhere zero.
This is proved in `ae_eq_zero_of_integral_smul_contDiff_eq_zero`.

A version for two functions having the same integral when multiplied by smooth compactly supported
functions is also given in `ae_eq_of_integral_smul_contDiff_eq`.
-/

open MeasureTheory Filter Metric Function Set

open scoped Topology

variable {E F : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {f f' : E → F}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- If a locally integrable function `f` has zero integral when multiplied by any smooth compactly
supported function, then `f` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_smul_contDiff_eq_zero (hf : LocallyIntegrable f μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ⊤ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 := by
  -- it suffices to show that the integral of the function vanishes on any compact set `s`
  apply ae_eq_zero_of_forall_set_integral_isCompact_eq_zero' hf (fun s hs ↦ Eq.symm ?_)
  -- choose a sequence of smooth functions `g n` equal to `1` on `s` and vanishing outside of the
  -- `u n`-neighborhood of `s`, where `u n` tends to zero. Then each integral `∫ gₙ f` vanishes,
  -- and by dominated convergence these integrals converge to `∫ x in s, f`.
  obtain ⟨u, u_anti, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : ℝ)
  let v : ℕ → Set E := fun n ↦ thickening (u n) s
  obtain ⟨K, K_compact, vK⟩ : ∃ K, IsCompact K ∧ ∀ n, v n ⊆ K := by
    refine' ⟨closure (v 0), _, fun n ↦ _⟩
    · rw [closure_thickening (u_pos 0)]
      apply isCompact_of_isClosed_bounded isClosed_cthickening hs.bounded.cthickening
    · apply Set.Subset.trans ?_ (subset_closure)
      exact thickening_mono (u_anti.antitone (zero_le n)) _
  have : ∀ n, ∃ (g : E → ℝ), support g = v n ∧ ContDiff ℝ ⊤ g ∧ Set.range g ⊆ Set.Icc 0 1
          ∧ ∀ x ∈ s, g x = 1 := fun n ↦ isOpen_thickening.exists_smooth_support_eq_eq_one
    hs.isClosed (self_subset_thickening (u_pos n) s)
  choose g g_supp g_diff g_range hg using this
  -- main fact: the integral of `∫ gₙ f` tends to `∫ x in s, f`.
  have L : Tendsto (fun n ↦ ∫ x, g n x • f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    rw [← integral_indicator hs.measurableSet]
    let bound : E → ℝ := K.indicator (fun x ↦ ‖f x‖)
    have A : ∀ n, AEStronglyMeasurable (fun x ↦ g n x • f x) μ :=
      fun n ↦ (g_diff n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable
    have B : Integrable bound μ := by
      rw [integrable_indicator_iff K_compact.measurableSet]
      exact (hf.integrableOn_isCompact K_compact).norm
    have C : ∀ n, ∀ᵐ x ∂μ, ‖g n x • f x‖ ≤ bound x := by
      intro n
      apply eventually_of_forall (fun x ↦ ?_)
      rw [norm_smul]
      refine le_indicator_apply (fun _ ↦ ?_) (fun hxK ↦ ?_)
      · have : ‖g n x‖ ≤ 1 := by
          have := g_range n (mem_range_self (f := g n) x)
          rw [Real.norm_of_nonneg this.1]
          exact this.2
        exact mul_le_of_le_one_left (norm_nonneg _) this
      · have : g n x = 0 := by rw [← nmem_support, g_supp]; contrapose! hxK; exact vK n hxK
        simp [this]
    have D : ∀ᵐ x ∂μ, Tendsto (fun n => g n x • f x) atTop (𝓝 (s.indicator f x)) := by
      apply eventually_of_forall (fun x ↦ ?_)
      by_cases hxs : x ∈ s
      · have : ∀ n, g n x = 1 := fun n ↦ hg n x hxs
        simp [this, indicator_of_mem hxs f]
      · simp_rw [indicator_of_not_mem hxs f]
        apply tendsto_const_nhds.congr'
        suffices H : ∀ᶠ n in atTop, g n x = 0
        · filter_upwards [H] with n hn using by simp [hn]
        obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ x ∉ thickening δ s := by
          rw [← hs.isClosed.closure_eq, closure_eq_iInter_thickening s] at hxs
          simpa using hxs
        filter_upwards [(tendsto_order.1 u_lim).2 _ δpos] with n hn
        rw [← nmem_support, g_supp]
        contrapose! hδ
        exact thickening_mono hn.le s hδ
    exact tendsto_integral_of_dominated_convergence bound A B C D
  -- deduce that `∫ x in s, f = 0` as each integral `∫ gₙ f` vanishes by assumption
  have : ∀ n, ∫ x, g n x • f x ∂μ = 0 := by
    refine' fun n ↦ h _ (g_diff n) _
    apply HasCompactSupport.of_support_subset_isCompact K_compact
    simpa [g_supp] using vK n
  simpa [this] using L

/-- If two locally integrable functions have the same integral when multiplied by any
smooth compactly supported function, then they coincide almost everywhere. -/
theorem ae_eq_of_integral_smul_contDiff_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : ∀ (g : E → ℝ),
      ContDiff ℝ ⊤ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x := by
  have : ∀ᵐ x ∂μ, (f - f') x = 0 := by
    apply ae_eq_zero_of_integral_smul_contDiff_eq_zero (hf.sub hf')
    intro g g_diff g_supp
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub, sub_eq_zero]
    · exact h g g_diff g_supp
    · exact hf.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
    · exact hf'.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx
