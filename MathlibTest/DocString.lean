import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Linter.DocString

/-! Tests for the `docstring` linter -/

set_option linter.style.docString true

#adaptation_note /--This comment is not inspected by the `docString` linter.-/

example : True := by
  #adaptation_note /--   This comment is not inspected by the `docString` linter.
  -/
  trivial

/--
warning: error: this doc-string is empty

Note: This linter can be disabled with `set_option linter.style.docString.empty false`
-/
#guard_msgs in
/---/
example : Nat := 0

/--
warning: error: this doc-string is empty

Note: This linter can be disabled with `set_option linter.style.docString.empty false`
-/
#guard_msgs in
/--
-/
example : Nat := 0

set_option linter.style.docString.empty false
/---/
example : Nat := 0

set_option linter.style.docString.empty true
set_option linter.style.docString false

#guard_msgs in
/--Missing space -/
example : Nat := 1

set_option linter.style.docString true

#guard_msgs in
/-- A doc-string
with fine indentation -/
example : Nat := 0

/--
warning: error: line 'with odd indentation ' is indented by 1 space, which is an odd number

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string
 with odd indentation -/
example : Nat := 0

/--
warning: error: line 'with odd indentation' is indented by 3 spaces, which is an odd number

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: error: line 'and even odder. ' is indented by 5 spaces, which is an odd number

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string
   with odd indentation

     and even odder. -/
example : Nat := 0


/--
warning: error: doc-strings should start with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--Missing space -/
example : Nat := 1

/--
warning: error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Missing ending space-/
example : Nat := 1

/--
warning: error: doc-strings should start with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--  Two starting spaces -/
example : Nat := 1

/--
warning: error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--
Two ending spaces  -/
example : Nat := 1

/--
warning: error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Let's give an example.
```lean4
def foo : Bool := by
  sorry
```

-/
example : Nat := 1

/--
warning: error: doc-strings should not end with a comma

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- Let's give an example ending in a comma, -/
example : Nat := 1

/--
warning: error: doc-strings should start with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: error: doc-strings should start with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- The structure `X`. -/
structure X where
  /--  A field of `X`.
  -/
  x : Unit
  z : Unit
  /--
   A field of `X`
  spanning multiple lines.
  -/
  y : Unit
