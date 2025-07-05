import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter

set_option linter.style.refine true
/--
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.

Note: This linter can be disabled with `set_option linter.style.refine false`
---
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.

Note: This linter can be disabled with `set_option linter.style.refine false`
-/
#guard_msgs in
example : True := by
  refine' (by refine' .intro)

set_option linter.style.refine false
-- This is quiet because `linter.style.refine` is now false
example : True := by
  refine' (by refine' .intro)

set_option linter.style.refine false in
-- This is quiet because `linter.style.refine` is now false, even using `in`.
example : True := by
  refine' (by refine' .intro)

set_option linter.style.cases true
/--
warning: The `cases'` tactic is discouraged: please strongly consider using `obtain`, `rcases` or `cases` instead.

Note: This linter can be disabled with `set_option linter.style.cases false`
---
warning: The `cases'` tactic is discouraged: please strongly consider using `obtain`, `rcases` or `cases` instead.

Note: This linter can be disabled with `set_option linter.style.cases false`
-/
#guard_msgs in
example (a : (True ∨ True) ∨ (True ∨ True)): True := by
  cases' a with b b <;> cases' b <;> trivial

set_option linter.style.cases false
-- This is quiet because `linter.style.cases` is now false
example (a : (True ∨ True) ∨ (True ∨ True)): True := by
  cases' a with b b <;> cases' b <;> trivial

set_option linter.style.admit true
/--
warning: declaration uses 'sorry'
---
warning: The `admit` tactic is discouraged: please strongly consider using the synonymous `sorry` instead.

Note: This linter can be disabled with `set_option linter.style.admit false`
-/
#guard_msgs in
example : False := by admit

/--
warning: declaration uses 'sorry'
---
warning: The `admit` tactic is discouraged: please strongly consider using the synonymous `sorry` instead.

Note: This linter can be disabled with `set_option linter.style.admit false`
---
warning: The `admit` tactic is discouraged: please strongly consider using the synonymous `sorry` instead.

Note: This linter can be disabled with `set_option linter.style.admit false`
---
warning: The `admit` tactic is discouraged: please strongly consider using the synonymous `sorry` instead.

Note: This linter can be disabled with `set_option linter.style.admit false`
---
warning: The `admit` tactic is discouraged: please strongly consider using the synonymous `sorry` instead.

Note: This linter can be disabled with `set_option linter.style.admit false`
-/
#guard_msgs in
example : True ∧ True := by
  have : True := by
    · admit
  let foo : Nat := by admit
  refine ⟨?_, ?_⟩
  · admit
  · admit

set_option linter.style.admit false
/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : False := by admit

set_option linter.style.nativeDecide true

/--
warning: Using `native_decide` is not allowed in mathlib: because it trusts the entire Lean compiler
(not just the Lean kernel), it could quite possibly be used to prove false.

Note: This linter can be disabled with `set_option linter.style.nativeDecide false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by native_decide

/--
warning: Using `decide +native` is not allowed in mathlib:
because it trusts the entire Lean compiler (not just the Lean kernel),
it could quite possibly be used to prove false.

Note: This linter can be disabled with `set_option linter.style.nativeDecide false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by decide +native
#guard_msgs in
example : 1 + 1 = 2 := by decide -native

/--
warning: Using `decide +native` is not allowed in mathlib:
because it trusts the entire Lean compiler (not just the Lean kernel),
it could quite possibly be used to prove false.

Note: This linter can be disabled with `set_option linter.style.nativeDecide false`
-/
#guard_msgs in
theorem foo : 1 + 1 = 2 := by decide -native +native
#guard_msgs in
example : 1 + 1 = 2 := by decide +native -native

/--
warning: Using `decide +native` is not allowed in mathlib:
because it trusts the entire Lean compiler (not just the Lean kernel),
it could quite possibly be used to prove false.

Note: This linter can be disabled with `set_option linter.style.nativeDecide false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by decide +native -native +native +native
#guard_msgs in
example : 1 + 1 = 2 := by decide +native -native +kernel +native -kernel +native -native

/--
warning: Using `decide +native` is not allowed in mathlib:
because it trusts the entire Lean compiler (not just the Lean kernel),
it could quite possibly be used to prove false.

Note: This linter can be disabled with `set_option linter.style.nativeDecide false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by decide (config := { native := true })
example : 1 + 1 = 2 := by decide (config := { native := false })
-- Not handled yet: since mathlib hardly uses the old config syntax and this linter is purely
-- for user information (and not hard guarantees), we deem this acceptable.
example : 1 + 1 = 2 := by decide (config := { native := true, kernel := false })

set_option linter.style.nativeDecide false

set_option linter.style.maxHeartbeats true
/--
warning: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
set_option maxHeartbeats 10 in
-- reason for change
...

Note: This linter can be disabled with `set_option linter.style.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 10 in
section

/--
warning: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
set_option maxHeartbeats 10 in
-- reason for change
...

Note: This linter can be disabled with `set_option linter.style.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 10 in
set_option maxHeartbeats 10 in
section

/--
warning: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
set_option synthInstance.maxHeartbeats 10 in
-- reason for change
...

Note: This linter can be disabled with `set_option linter.style.maxHeartbeats false`
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 10 in
section

/--
warning: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
set_option maxHeartbeats 10 in
-- reason for change
...

Note: This linter can be disabled with `set_option linter.style.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 10 in
set_option synthInstance.maxHeartbeats 10 in
/- The comment here is not enough to silence the linter:
the *first* `maxHeartbeats` option should have a comment. -/
section

#guard_msgs in
set_option maxHeartbeats 10 in
/- The comment here is enough to silence the linter:
the *first* `maxHeartbeats` has a comment, to remaining ones are free to be commentless. -/
set_option synthInstance.maxHeartbeats 10 in
section

#guard_msgs in
set_option maxHeartbeats 10 in
-- no reason, but has a comment
section

/--
warning: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in
set_option maxHeartbeats 10 in
-- reason for change
...

Note: This linter can be disabled with `set_option linter.style.maxHeartbeats false`
-/
#guard_msgs in
set_option maxHeartbeats 10 in
/-- Doc-strings for the following command do not silence the linter. -/
example : True := trivial
