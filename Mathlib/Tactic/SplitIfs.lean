import Mathlib.Tactic.Basic
import Mathlib.Tactic.Block

example (P : Prop) [Decidable P] (w : if P then False else False) : False := by
  (by_cases P)
  - rw [if_pos h] at w
    assumption
  - rw [if_neg h] at w
    assumption
