module

public import Mathlib.Tactic.TacticAnalysis.Replacements

/-! Tests for the always-on tactic replacement analysis passes. -/

/--
warning: `simp_all` can replace `aesop`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.aesopToSimpAll false`
-/
#guard_msgs in
example : True := by
  aesop

/--
warning: `simp` can replace `simp_all`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.simpAllToSimp false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  simp_all

/--
warning: `lia` can replace `grind`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.grindToLia false`
-/
#guard_msgs in
example (x y : Int) (h : x ≤ y) : x ≤ y := by
  grind

section

variable {α : Type*} {a b : α} (h : a = b)

/--
warning: `rw` can replace `simp_rw [h]` using `rw [h]`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.simpRwToRw false`
-/
#guard_msgs in
example : a = b := by
  simp_rw [h]

/--
warning: `rw` can replace `rw! [h] at ha` using `rw [h] at ha`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.depRwToRw false`
-/
#guard_msgs in
example (P : α → Prop) (ha : P a) : P b := by
  rw! [h] at ha
  exact ha

/--
warning: `rw` can replace `grw [h]` using `rw [h]`

Note: This linter can be disabled with `set_option linter.tacticAnalysis.grwToRw false`
-/
#guard_msgs in
example : a = b := by
  grw [h]

end
