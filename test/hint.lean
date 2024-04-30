import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

/--
info: Try these:
• linarith
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

/--
info: Try these:
• exact f p
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
• simp_all only [and_self]
-/
#guard_msgs in
example {P Q R: Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

/--
info: Try these:
• linarith
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
• omega
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by hint

/--
info: Try these:
• decide
-/
#guard_msgs in
example : Nat.Prime 37 := by hint

/--
info: Try these:
• aesop
• simp_all only [zero_le, and_true]
-/
#guard_msgs in
example {P : Nat → Prop} (h : { x // P x }) : ∃ x, P x ∧ 0 ≤ x := by hint
