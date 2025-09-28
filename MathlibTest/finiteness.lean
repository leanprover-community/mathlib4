import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Finiteness

open MeasureTheory Set
open scoped ENNReal NNReal

example : (1 : ℝ≥0∞) < ∞ := by finiteness
example : (3 : ℝ≥0∞) ≠ ∞ := by finiteness

example (a : ℝ) (b : ℕ) : ENNReal.ofReal a + b < ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a + 3 < ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a < ∞) : a + 3 < ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a ^ 10 ≠ ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a ≠ ∞) : a / 10 + 5 ≠ ∞ := by finiteness
example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ 0) : a / b ≠ ∞ := by finiteness
example {a : ℝ≥0∞} {b : ℝ≥0} (ha : a ≠ ∞) (hb : b ≠ 0) : a / b ≠ ∞ := by finiteness
example {a b : ℝ≥0∞} (ha : a ≠ ∞) : a / (b + 5) ≠ ∞ := by finiteness

example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a * b ≠ ∞ := by finiteness
example {a : ℝ≥0∞} (ha : 0 < a) : a⁻¹ ≠ ∞ := by finiteness
-- not supported yet
-- example {t a : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (this : a ≠ 0) : t * a ≠ ∞ := by finiteness
-- example {t a : ℝ≥0∞} (ht : t ∈ Ioo 0 1) (this : a ≠ 0) : a * t ≠ ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a ^ 10 ≠ ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a ≠ ∞) (ha' : a ≠ 0) : a ^ (10 : ℤ) ≠ ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a ≠ ∞) : a ^ (10 : ℝ) ≠ ∞ := by finiteness
example : (0 : ℝ≥0∞) ^ (10 : ℝ) ≠ ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ∞) : a ^ (-10 : ℝ) ≠ ∞ := by finiteness
example {a : ℝ} : (10 : ℝ≥0∞) ^ a ≠ ∞ := by finiteness
example {a : ℝ≥0∞} {t : ℝ} (ha : a ≠ 0) (ha : a ≠ ∞) : a ^ t ≠ ∞ := by finiteness

example {a : ℝ≥0∞} : a * a⁻¹ ≠ ∞ := by finiteness
example {a : ℝ≥0∞} : a⁻¹ * a ≠ ∞ := by finiteness
example {a : ℝ≥0∞} : 2 * (a⁻¹ * a) ≠ ∞ := by finiteness
example {a : ℝ≥0∞} : 2 * a⁻¹ * a ≠ ∞ := by rw [mul_assoc]; finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : max a 37 ≠ ∞ := by finiteness
example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : max a b < ∞ := by finiteness

/--
Test that `finiteness_nonterminal` makes progress but does not fail on not
closing the goal.
-/
example {a : ℝ≥0∞} (ha : a = 0) : a + 3 < ∞ := by finiteness_nonterminal; simp [ha]

example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness

example {α : Type*} (f : α → ℕ) : ∀ i, (f i : ℝ≥0∞) ≠ ∞ := by finiteness

example {α} {_ : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ := by
  finiteness
