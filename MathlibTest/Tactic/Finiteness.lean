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

-- Basic tests for `finiteness?`
/--
info: Try this:

  [apply]     apply max_ne_top
    · exact ha
    · apply ENNReal.ofNat_ne_top
-/
#guard_msgs in
example {a : ℝ≥0∞} (ha : a ≠ ∞) : max a 37 ≠ ∞ := by finiteness?

-- Also test supplying additional expressions.
/--
info: Try this:

  [apply]     rename_i this
    apply Ne.lt_top
    exact this
-/
#guard_msgs in
example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : max a b < ∞ := by finiteness? [max_ne_top ha hb]

section

attribute [-aesop] max_ne_top
-- now finiteness fails to close the goal
axiom silentSorry {α} : α
example {a b : ℝ≥0∞} (_ha : a ≠ ∞) (_hb : b ≠ ∞) : max a b < ∞ := by
  fail_if_success finiteness
  exact silentSorry

-- but adding it as an expression works
example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : max a b < ∞ := by finiteness [max_ne_top ha hb]

-- as does adding max_ne_top again via an aesop clause
example {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : max a b < ∞ := by finiteness (add safe max_ne_top)

end

-- The attribute removal was confined to the previous section: this test confirms it.
example {a b : ℝ≥0∞} (_ha : a ≠ ∞) (_hb : b ≠ ∞) : max a b < ∞ := by finiteness

-- finiteness can split on a condition by proving each branch individually.
example {p : Prop} [Decidable p] {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    (if c ≠ 37 ∨ ¬p then c + a else b + 1) < ∞ := by
  finiteness

-- finiteness can use the condition to help prove the goal. Test dite and ite versions:
example {a b c : ℝ≥0∞} (hb : b ≠ ∞) (hc : c ≠ ∞) :
    (if _ : a ≠ ∞ then c + a else b + 1) < ∞ := by
  finiteness

example {a b c : ℝ≥0∞} (hb : b ≠ ∞) (hc : c ≠ ∞) :
    (if a ≠ ∞ then c + a else b + 1) < ∞ := by
  finiteness

/--
Test that `finiteness_nonterminal` makes progress but does not fail on not
closing the goal.
-/
example {a : ℝ≥0∞} (ha : a = 0) : a + 3 < ∞ := by finiteness_nonterminal; simp [ha]

example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness

-- `finiteness_nonterminal` is allowed to close goals.
-- (In practice, this is a code smell; `finiteness` should be used directly.)
example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness_nonterminal

example {α : Type*} (f : α → ℕ) : ∀ i, (f i : ℝ≥0∞) ≠ ∞ := by finiteness

example {α} {_ : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ := by
  finiteness
