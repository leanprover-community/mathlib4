import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Util.Time

axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.linearOrderedField : LinearOrderedField ℝ


#time
-- set_option trace.Meta.synthInstance true in
-- set_option trace.profiler true in
-- set_option profiler.threshold 5 in
theorem foo {a b : ℝ} (h : a + 1 ≤ b) : True := by
  -- 10
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  -- 10
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  -- 10
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  -- 10
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  -- 10
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  have : 0 ≤ b - a := by linear_combination h
  exact trivial

#time
example {a b : ℝ} (h : a + 1 ≤ b) : True := by
  -- 10
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  -- 10
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  -- 10
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  -- 10
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  -- 10
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  have : 0 ≤ b - a := by linarith only [h]
  sorry
