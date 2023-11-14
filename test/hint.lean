import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

example (h : 1 < 0) : False := by hint

example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

example {P Q R: Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

example : 37^2 - 35^2 = 72 * 2 := by hint

example : Nat.Prime 37 := by hint

example {P : Nat → Prop} (h : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by hint
