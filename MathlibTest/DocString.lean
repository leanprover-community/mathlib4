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


#guard_msgs in
/-- Odd indentation,
```
 but in a code block
-/
example : Nat := 1

#guard_msgs in
/-- Currently, odd indentation before any code block
 is also allowed
```
1 + 2 = 2
```
-/
example : Nat := 1

/--
warning: error: line '* oddly indented' is indented by 1 space, which is an odd number

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--
A list
* first item
 * oddly indented
-/
example : Nat := 1

#guard_msgs in
/--
A list
* first item
  - second item
-/
example : Nat := 1

/--
warning: unexpected indentation: line '- over-indented second item' is indented by 4 spaces,
but should have been indented by at most 2.
The the previous line was indented by 0 spaces.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--
A list
* first item
    - over-indented second item
-/
example : Nat := 1

/--
warning: error: line '- an odd item' is indented by 3 spaces, which is an odd number

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: unexpected indentation: line '- another' is indented by 6 spaces,
but should have been indented by at most 5.
The the previous line was indented by 3 spaces.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/--
A list
* first item
  - over-indented second item
    - third
   - an odd item
      - another
    - fine again
  * less indentation
- even less
-/
example : Nat := 1

#guard_msgs in
/--
A list
* first item
  - over-indented second item
    - third
* abrupt de-indentation
-/
example : Nat := 1

/--
warning: bad indentation: line '- second item' follows an enumeration item, expected additional indentation.
To start a new paragraph, insert a blank line instead.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string with an enumeration
* first item
spanning multiple lines
- second item
  is fine
-/
example : Nat := 1

#guard_msgs in
/-- A doc-string with an enumeration
* first item
  spanning multiple lines
- second item

Now, a new paragraph begins.
-/
example : Nat := 1

/--
warning: bad indentation: line '' follows an enumeration item, expected additional indentation.
To start a new paragraph, insert a blank line instead.

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: bad indentation: line '' follows an enumeration item, expected additional indentation.
To start a new paragraph, insert a blank line instead.

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: error: doc-strings should end with a single space or newline

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- First doc-string line.

* `{x | p x}` is elaborated as `Set.setOf fun x ↦ p x`
* `{x : α | p x}` is elaborated as `Set.setOf fun x : α ↦ p x`
* `{binder x | p x}`, where `x` is bound by the `binder` binder, is elaborated as
  `{x | binder x ∧ p x}`. The typical example is `{x ∈ s | p x}`, which is elaborated as
  `{x | x ∈ s ∧ p x}`. The possible binders are
  * `· ∈ s`, `· ∉ s`
  * `· ⊆ s`, `· ⊂ s`, `· ⊇ s`, `· ⊃ s`
  * `· ≤ a`, `· ≥ a`, `· < a`, `· > a`, `· ≠ a`

-/
example : Nat := 1

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
