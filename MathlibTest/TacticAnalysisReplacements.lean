module

public import Mathlib.Tactic.TacticAnalysis.Replacements

/-! Tests for the always-on tactic replacement analysis passes. -/

/--
info: `simp_all` can replace `aesop`

Try this:
  [apply] simp_all

Note: This linter can be disabled with `set_option linter.tacticAnalysis.aesopToSimpAll false`
-/
#guard_msgs in
example : True := by
  aesop

/--
info: `simp` can replace `simp_all`

Try this:
  [apply] simp

Note: This linter can be disabled with `set_option linter.tacticAnalysis.simpAllToSimp false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  simp_all

/--
info: `lia` can replace `grind`

Try this:
  [apply] lia

Note: This linter can be disabled with `set_option linter.tacticAnalysis.grindToLia false`
-/
#guard_msgs in
example (x y : Int) (h : x ≤ y) : x ≤ y := by
  grind

-- A failed replacement must not try to extract a counterexample when failure reporting is off.
-- In particular, the target may depend on the auxiliary declaration for a recursive definition,
-- which cannot be cleared while extracting a standalone theorem.
#guard_msgs in
private def recursiveAux : (n : Nat) → { p : Prop // p }
  | 0 => ⟨True, by trivial⟩
  | n + 1 => ⟨(recursiveAux n).1, by grind [(recursiveAux n).2]⟩

section

variable {α : Type*} {a b : α} (h : a = b)

/--
info: `rw` can replace `simp_rw [h]` using `rw [h]`

Try this:
  [apply] rw [h]

Note: This linter can be disabled with `set_option linter.tacticAnalysis.simpRwToRw false`
-/
#guard_msgs in
example : a = b := by
  simp_rw [h]

/--
info: `rw` can replace `rw! [h] at ha` using `rw [h] at ha`

Try this:
  [apply] rw [h] at ha

Note: This linter can be disabled with `set_option linter.tacticAnalysis.depRwToRw false`
-/
#guard_msgs in
example (P : α → Prop) (ha : P a) : P b := by
  rw! [h] at ha
  exact ha

/--
info: `rw` can replace `grw [h]` using `rw [h]`

Try this:
  [apply] rw [h]

Note: This linter can be disabled with `set_option linter.tacticAnalysis.grwToRw false`
-/
#guard_msgs in
example : a = b := by
  grw [h]

end
