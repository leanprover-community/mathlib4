import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime

/--
info: Try these:
• simp_all only [not_lt_zero']
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

-- This message is non-deterministic due to parallelism.
/-
info: Try these:
• simp_all only [forall_true_left, p]
-/
#guard_msgs (drop info) in
example {P Q : Prop} (p : P) (f : P → Q) : Q := by hint

/--
info: Try these:
• simp_all only [and_self]
-/
#guard_msgs in
example {P Q R: Prop} (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by hint

-- This message is non-deterministic due to parallelism.
/-
info: Try these:
• exact lt_asymm h
• intro
• simp_all only [not_lt]
-/
#guard_msgs (drop info) in
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


/-!
We now register a hint tactic that simulates a long running tactic,
in order to test that the `hint` tactic cancels long running tactics if another tactic successfully
closes the goal.

Note that while the tactic framework internally calls `IO.checkCanceled`,
calculations in the kernel do not, and so it is posssible that the cancellation request will fail.

I don't see a good way to verify this in the test file,
but you can check that in the final example below CPU usage drops to zero after `hint` returns.
Disabling the `cancel` step in the implementation of the `hint` tactic results in a processs
that continues using a CPU for 10 seconds after `hint` returns.
-/

def busy_wait (millis : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  while !(← IO.checkCanceled) && (← IO.monoMsNow) < start + millis do pure ()
  IO.checkCanceled

register_hint run_tac busy_wait 10000

/--
info: Try these:
• decide
-/
#guard_msgs in
example : True := by hint
