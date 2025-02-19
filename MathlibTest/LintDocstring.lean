import Mathlib.Tactic.Linter.DocString

/-! Tests for the `docstring` linter -/

set_option linter.style.docString true

/--
warning: error: doc-string "Missing space " should start with a space or newline
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--Missing space -/
example : Nat := 1

/--
warning: error: doc-string "Missing ending space" should end with a space or newline
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Missing ending space-/
example : Nat := 1

/--
warning: error: doc-string "Trailing newline " should start with a single space
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--  Trailing newline -/
example : Nat := 1

/--
warning: error: doc-string "Trailing newline  " should end with at most a single space
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--
Trailing newline  -/
example : Nat := 1

/--
warning: error: subsequent lines in the doc-string "Bad indentation
  on the second line " should not be indented
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Bad indentation
  on the second line -/
example : Nat := 1

/--
warning: error: subsequent lines in the doc-string "Bad indentation
not on the second, but
   the second line " should not be indented
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Bad indentation
not on the second, but
   the second line -/
example : Nat := 1

/--
warning: error: docstring "ends with a comma, " ends with a comma
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- ends with a comma, -/
example : Nat := 1

/--
warning: error: docstring "With a trailing quote" " ends with a single quote
note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- With a trailing quote" -/
example : Nat := 1

/--
warning: error: subsequent lines in the doc-string "With a trailing
  quote" " should not be indented note: this linter can be disabled with `set_option linter.style.docString false`
---
warning: error: docstring "With a trailing
  quote" " ends with a single quote note: this linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- With a trailing
  quote" -/
example : Nat := 1
