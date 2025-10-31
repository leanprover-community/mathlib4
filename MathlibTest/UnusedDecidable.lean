import Mathlib.Tactic.Linter.UnusedDecidable

set_option linter.unusedDecidable true

/--
warning: `foo` has the hypothesis `[DecidableEq α]` which is not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead.

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
theorem foo [DecidableEq α] : True := True.intro

def Foo (α) [DecidableEq α] := Unit

#guard_msgs in
theorem bar [DecidableEq α] (s : Foo α) : s = s := rfl

/--
warning: unused variable `x`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: `foo₂` has the hypothesis `[(m : Nat) → Decidable (m ≠ 0)]` which is not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead.

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ m : Nat, Decidable (m ≠ 0)] (x : Unit) [Nonempty a] : True := trivial

-- TODO: why the newline + indentation?
/--
warning: `foo₃` has the hypotheses `[(m : Nat) →
  Decidable (m ≠ 0)]` and `[DecidableEq β]` which are not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead.

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
def foo₃ {β} [∀ m : Nat, Decidable (m ≠ 0)] [DecidableEq β] : True := trivial
