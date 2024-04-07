import Mathlib

set_option trace.profiler true in
noncomputable example : FiniteDimensional ℝ (ℂ × ℂ →L[ℂ] ℂ) := by
  infer_instance
