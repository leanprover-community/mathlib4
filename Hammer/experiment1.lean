import Mathlib.MeasureTheory.Function.Floor
import Hammer

open scoped NNReal

example (n : ℤ) : Measurable (fun (x : ℝ≥0) ↦ ⌊ x * (2^n : ℝ)⌋) := by
  hammer
