import Mathlib.Tactic.Finiteness
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Typeclasses

open MeasureTheory
open scoped ENNReal

example : (1 : ℝ≥0∞) < ∞ := by finiteness
example : (3 : ℝ≥0∞) ≠ ∞ := by finiteness

example (a : ℝ) (b : ℕ) : ENNReal.ofReal a + b < ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a + 3 < ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a < ∞) : a + 3 < ∞ := by finiteness
/-- 
Test that `finiteness_nonterminal` makes progress but does not fail on not 
closing the goal. 
-/
example {a : ℝ≥0∞} (ha : a = 0) : a + 3 < ∞ := by finiteness_nonterminal; simp [ha]

example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness

example {α : Type*} (f : α → ℕ) : ∀ i, (f i : ℝ≥0∞) ≠ ∞ := by finiteness

example {_ : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ := by
  finiteness
