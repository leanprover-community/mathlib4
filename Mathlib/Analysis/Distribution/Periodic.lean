/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Temperate growth
-/

open scoped ContDiff Real

variable {𝕜 α β E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace Function

section PeriodicUtil

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- If a function is is periodic, then its derivative is periodic. -/
theorem Periodic.fderiv {f : E → F} {c : E} (hf : Periodic f c) : Periodic (fderiv 𝕜 f) c := by
  intro x
  rw [← fderiv_comp_add_right, hf.funext]

variable (𝕜) in
/-- If a function is is periodic, then all of its derivatives are periodic. -/
theorem Periodic.iteratedFDeriv (n : ℕ) {f : E → F} {c : E} (hf : Periodic f c) :
    Periodic (iteratedFDeriv 𝕜 n f) c := by
  intro x
  rw [← iteratedFDeriv_comp_add_right, hf.funext]

variable [LinearOrderedAddCommGroup α] [Archimedean α] [TopologicalSpace α] [CompactIccSpace α]
  [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]

theorem Periodic.bddAbove_range_of_continuous [Nonempty β] {f : α → β} {c : α}
    (hf : Periodic f c) (hc : c ≠ 0) (hf_cont : Continuous f) :
    BddAbove (Set.range f) := by
  rw [← hf.image_uIcc hc 0]
  exact IsCompact.bddAbove_image isCompact_uIcc hf_cont.continuousOn

/-- Continuous periodic functions on an infinite, ordered set are bounded. -/
theorem Periodic.exists_bound_of_continuous {f : α → F} {c : α}
    (hf : Periodic f c) (hc : c ≠ 0) (hf_cont : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  have h := (hf.comp fun y ↦ ‖y‖).bddAbove_range_of_continuous hc hf_cont.norm
  rcases h.exists_ge 0 with ⟨C, _, hC⟩
  exact ⟨C, fun x ↦ by simpa using hC ‖f x‖⟩

end PeriodicUtil

section HasTemperateGrowth

variable [NormedSpace ℝ F]

-- TODO: Could generalize beyond `ℝ`? Not necessary at this stage.
theorem Periodic.hasTemperateGrowth {f : ℝ → F} {c : ℝ} (hf : Periodic f c) (hc : c ≠ 0)
    (hf_smooth : ContDiff ℝ ∞ f) : f.HasTemperateGrowth := by
  refine ⟨hf_smooth, fun n ↦ ⟨0, ?_⟩⟩
  simpa using (hf.iteratedFDeriv ℝ n).exists_bound_of_continuous hc
    (hf_smooth.continuous_iteratedFDeriv (by norm_cast; simp))

end HasTemperateGrowth

end Function

theorem Complex.exp_ofReal_mul_I_periodic : Function.Periodic (fun x : ℝ ↦ exp (x * I)) (2 * π) :=
  fun x ↦ by simp [add_mul, exp_add]

theorem Real.cos_hasTemperateGrowth : cos.HasTemperateGrowth :=
  cos_periodic.hasTemperateGrowth two_pi_pos.ne' contDiff_cos

theorem Real.sin_hasTemperateGrowth : sin.HasTemperateGrowth :=
  sin_periodic.hasTemperateGrowth two_pi_pos.ne' contDiff_sin

theorem Complex.exp_ofReal_mul_I_hasTemperateGrowth :
    (fun x : ℝ ↦ exp (x * I)).HasTemperateGrowth :=
  exp_ofReal_mul_I_periodic.hasTemperateGrowth Real.two_pi_pos.ne'
    (ofRealCLM.contDiff.mul contDiff_const).cexp
