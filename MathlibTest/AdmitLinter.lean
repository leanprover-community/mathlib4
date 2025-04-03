import Mathlib.Tactic.Linter.AdmitLinter

set_option linter.admit true

/--
warning: declaration uses 'sorry'
---
warning: The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead.
note: this linter can be disabled with `set_option linter.admit false`
-/
#guard_msgs in
example : True := by admit

/--
warning: declaration uses 'sorry'
---
warning: The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead.
note: this linter can be disabled with `set_option linter.admit false`
---
warning: The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead.
note: this linter can be disabled with `set_option linter.admit false`
---
warning: The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead.
note: this linter can be disabled with `set_option linter.admit false`
---
warning: The `admit` tactic is discouraged: please consider using the synonymous `sorry` instead.
note: this linter can be disabled with `set_option linter.admit false`
-/
#guard_msgs in
example : True ∧ True := by
  have : True := by
    · admit
  let foo : Nat := by admit
  refine ⟨?_, ?_⟩
  · admit
  · admit
