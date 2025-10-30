import Mathlib.Tactic.Linter.UnusedInstancesInType

set_option linter.unusedDecidable true

/--
warning: `foo` has the hypothesis `[DecidableEq α]` (#2) which is not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open Scoped classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
theorem foo {α} [DecidableEq α] : True := True.intro

def Foo (α) [DecidableEq α] := Unit

#guard_msgs in
theorem bar {α} [DecidableEq α] (s : Foo α) : s = s := rfl

/--
warning: unused variable `x`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: `foo₂` has the hypothesis `[(m : Nat) → Decidable (m ≠ 0)]` (#2) which is not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open Scoped classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
theorem foo₂ (a : Type) [∀ m : Nat, Decidable (m ≠ 0)] (x : Unit) [Nonempty a] : True := trivial

-- TODO: why the newline + indentation in the pretty-printing of the forall?
/--
warning: `foo₃` has the hypotheses `[(m : Nat) →
  Decidable (m ≠ 0)]` (#2) and `[DecidableEq β]` (#3) which are not used in the remainder of the type.
Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open Scoped classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.unusedDecidable false`
-/
#guard_msgs in
theorem foo₃ {β} [∀ m : Nat, Decidable (m ≠ 0)] [DecidableEq β] : True := trivial

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem fooSorry {β} [∀ m : Nat, Decidable (m ≠ 0)] [DecidableEq β] (b : sorry) : True := trivial
