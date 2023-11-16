import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

/--
info: Try these:
• simp_all only
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

/--
info: Try these:
• linarith
• simp_all only [gt_iff_lt, ge_iff_le]
• aesop
-/
#guard_msgs in
example {x y z : Rat} (_ : x + y > z) (_ : x < z / 2) (_ : y < z / 4) (_ : z ≥ 0) : False := by
  hint

/--
info: Try these:
• simp_all only [forall_true_left, p]
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
• exact lt_asymm h
• intro
• simp_all only [not_lt]
-/
#guard_msgs in
example {a b : ℚ} (h : a < b) : ¬ b < a := by hint

/--
info: Try these:
• decide
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
