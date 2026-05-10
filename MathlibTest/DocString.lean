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
warning: warning: this doc-string is empty

Note: This linter can be disabled with `set_option linter.style.docString.empty false`
-/
#guard_msgs in
/---/
example : Nat := 0

/--
warning: warning: this doc-string is empty

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


/-! # Tests for Verso-compatible docstrings -/

set_option linter.style.docStringVerso true

-- Errors on mismatched brackets, but not on references:
/--
warning: expected ']'

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
-/
#guard_msgs in
/-- See [bourbaki1989) -/
example : Nat := 0

/-- See [bourbaki1989] -/
example : Nat := 0

-- Errors on underscores, but not when they appear in a URL:
/--
warning: expected '_' without preceding space

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
-/
#guard_msgs in
/-- See wikipedia page 0_(disambiguation) -/
example : Nat := 0

/-- See https://en.wikipedia.org/wiki/0_(disambiguation) -/
example : Nat := 0

-- Error on underscores or backslashes, but not inside a LaTeX block.
/--
warning: expected identifier

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
---
warning: unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
-/
#guard_msgs in
/-- 0^0 + 0 = 0_0 - \frac{0}{1} -/
example : Nat := 0

/-- $$0^0 + 0 = 0_0 - \frac{0}{1}$$ -/
example : Nat := 0

-- TODO (difficult because it requires nontrivial parsing): support inline LaTeX too.
/--
warning: expected identifier

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
---
warning: unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'

Note: This linter can be disabled with `set_option linter.style.docStringVerso false`
-/
#guard_msgs in
/-- Inline $0^0 + 0 = 0_0 - \frac{0}{1}$ LaTeX text -/
example : Nat := 0

/-- The simple solution of skipping everything between `$`s does not work because it
will result in this current docstring breaking from mismatched quotes around
```
$
```
signs.
-/
example : Nat := 0
