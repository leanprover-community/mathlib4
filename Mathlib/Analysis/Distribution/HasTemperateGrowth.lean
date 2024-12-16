/-
Copyright (c) 2024 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Temperate growth
-/

open ContDiff

namespace Function

section PeriodicUtil

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

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

variable {α β : Type*}
  [LinearOrderedAddCommGroup α] [Archimedean α] [TopologicalSpace α] [CompactIccSpace α]
  [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]

theorem Periodic.bddAbove_range_of_continuous [Nonempty β] {f : α → β} {c : α}
    (hf : Periodic f c) (hc : 0 < c) (hf_cont : Continuous f) :
    BddAbove (Set.range f) := by
  -- TODO: Can we change the proof to reduce the assumptions on `β`?
  rw [← hf.image_Icc hc 0]
  exact IsCompact.bddAbove_image isCompact_Icc hf_cont.continuousOn

-- TODO: Generalize to finite-dimensional vector space?
/-- Continuous periodic functions on are bounded. -/
theorem Periodic.exists_bound_of_continuous {f : α → F} {c : α}
    (hf : Periodic f c) (hc : 0 < c) (hf_cont : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  have h := (hf.comp fun y ↦ ‖y‖).bddAbove_range_of_continuous hc hf_cont.norm
  rcases h.exists_ge 0 with ⟨C, _, hC⟩
  exact ⟨C, fun x ↦ by simpa using hC ‖f x‖⟩

end PeriodicUtil

section HasTemperateGrowth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- TODO: Could generalize beyond `ℝ`? Not necessary at this stage.
theorem Periodic.hasTemperateGrowth {f : ℝ → F} {c : ℝ}
    (hf : Periodic f c) (hc : 0 < c) (hf_smooth : ContDiff ℝ ∞ f) : f.HasTemperateGrowth := by
  refine ⟨hf_smooth, ?_⟩
  intro n
  use 0
  have := (hf.iteratedFDeriv ℝ n).exists_bound_of_continuous hc
    (hf_smooth.continuous_iteratedFDeriv (by norm_cast; simp))
  simpa

end HasTemperateGrowth

end Function

namespace Real

theorem hasTemperateGrowth_cos : cos.HasTemperateGrowth :=
  cos_periodic.hasTemperateGrowth two_pi_pos contDiff_cos

theorem hasTemperateGrowth_sin : sin.HasTemperateGrowth :=
  sin_periodic.hasTemperateGrowth two_pi_pos contDiff_sin

end Real

namespace Complex

open scoped Real

theorem exp_ofReal_mul_I_periodic : Function.Periodic (fun x : ℝ ↦ exp (x * I)) (2 * π) :=
  fun x ↦ by simp [add_mul, exp_add]

theorem exp_ofReal_mul_I_hasTemperateGrowth : Function.HasTemperateGrowth fun x : ℝ ↦ exp (x * I) :=
  exp_ofReal_mul_I_periodic.hasTemperateGrowth Real.two_pi_pos
    (ofRealCLM.contDiff.mul contDiff_const).cexp

end Complex
