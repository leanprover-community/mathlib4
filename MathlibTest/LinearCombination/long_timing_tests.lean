import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

axiom Real : Type
notation "ℝ" => Real
@[instance] axiom Real.linearOrderedField : LinearOrderedField ℝ


#time
-- set_option trace.Meta.synthInstance true in
-- set_option trace.profiler true in
-- set_option profiler.threshold 5 in
theorem foo {a b : ℝ} (h : a + 1 ≤ b) : True := by
  iterate 50
    have : 0 ≤ b - a := by linear_combination h
    clear this
  trivial

#time
example {a b : ℝ} (h : a + 1 ≤ b) : True := by
  iterate 50
    have : 0 ≤ b - a := by linarith only [h]
    clear this
  trivial
