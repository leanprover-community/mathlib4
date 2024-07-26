import Mathlib.Tactic.Linter.CheckAsSorry

set_option linter.checkAsSorry false

namespace X

/--
error: ⏎
---
warning: 'X.heq0' is not defeq to its 'asSorry'ed version
actual type:      '∀ {a b : Nat}, a = b → a = b'
'asSorry'ed type: '∀ {α : Sort u_1} {a b : α}, a = b'
note: this linter can be disabled with `set_option linter.checkAsSorry false`
-/
#guard_msgs in
set_option linter.checkAsSorry true in
variable {a b : Nat} (h : a = b) in
lemma heq0 : a = b := by exact h

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option linter.checkAsSorry true in
/-- doc-string -/
nonrec
theorem heq1 {a b : Nat} (h : a = b) : a = b := sorry --by exact h

#guard_msgs in
set_option linter.checkAsSorry true in
lemma heq2 {a b : Nat} (h : a = b) : a = b := by exact h

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option linter.checkAsSorry true in
lemma heq3 {a b : Nat} (h : a = b) : a = b := sorry
