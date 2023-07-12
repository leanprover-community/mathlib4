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
-/

open MeasureTheory Filter Metric Function

open scoped Topology

variable {E F : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {f : E → F}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem glou (hf : LocallyIntegrable f μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ⊤ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 := by
  apply ae_eq_zero_of_forall_set_integral_isCompact_eq_zero' hf (fun s hs ↦ Eq.symm ?_)
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
  have L : Tendsto (fun n ↦ ∫ x, g n x • f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := sorry
  have B : ∀ n, ∫ x, g n x • f x ∂μ = 0 := by
    intro n
    apply h _ (g_diff n)
  simpa [B] using L


#exit

IsOpen.exists_smooth_support_eq_eq_one
