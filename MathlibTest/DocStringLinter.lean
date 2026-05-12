import Mathlib.Tactic.Linter.DocString

/-! # Tests for the docString linter -/

set_option linter.style.docString true

/-- A doc-string across multiple lines
spanning
even more lines
just to cover this. -/
def foo := 2

/-- A doc-string across multiple lines
- now some indented list
- and another

The blank line is not linted. -/
def bar := 2

/-- A doc-string across multiple lines
* now some indented list
  with a multi-line item
  and follow-up lines being indented correctly
* and another item, with asterisks

The blank line is not linted. -/
def baz := 0


/--
warning: bad indentation: line 'with a second continuation line, with too much indentation. TODO: why not linted?' is indented by 6 spaces, but expected 2.
This line is considered inside an enumeration item.
To start a new paragraph, insert a blank line instead.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string across multiple lines
* now some indented list
      with a second continuation line, with too much indentation. TODO: why not linted?
* and another item, with asterisks

The blank line is not linted. -/
def hoge := 0

-- test for a regression
#guard_msgs in
/-- A doc-string with a numbered item:
  1. one item
  2. another one
-/
def sdf := 2

#guard_msgs in
/-- A doc-string with a numbered item:
  1. one item
    across multiple lines
  2. another one
-/
def sdf' := 2

-- This used to have false positives.
#guard_msgs in
/-- A doc-string with a numbered item:
  1. after the item,
    continuing with two space indentation is fine
  2. but so is
     indenting by three spaces!
-/
def sdf'' := 2

-- Yet, we still check for an even number of spaces inside an unnumbered item.
/--
warning: bad indentation: line 'indenting by three spaces is linted!' is indented by 3 spaces, but expected 2.
This line is considered inside an enumeration item.
To start a new paragraph, insert a blank line instead.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string with a numbered item:
1. un-numbered item,
  continuing with two space indentation is fine
* numbered item,
   indenting by three spaces is linted!
-/
def sdf''' := 2


/--
warning: bad indentation: line 'but extra indentation is bad' is indented by 6 spaces, but expected 4

Note: This linter can be disabled with `set_option linter.style.docString false`
---
warning: unexpected indentation: line 'also!' is indented by 7 spaces,
but should have been indented by at least 4 and at most 6.

Note: This linter can be disabled with `set_option linter.style.docString false`
-/
#guard_msgs in
/-- A doc-string with a numbered item:
  1. after the item,
    continuing with two space indentation is fine,
      but extra indentation is bad
  2. and more than two spaces
       also!
-/
def hogehoge := 2

#guard_msgs in
/-- A doc-string with un-numbered items:
* first line,
  second line,
  third line
-/
def hogehoge' := 2

-- two more former false positives
#guard_msgs in
/--
Foo
1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend
   `IsManifold I n G`. This way we save users from adding both
   `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many API
-/
def more := 0

#guard_msgs in
/--
Foo
1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend
   `IsManifold I n G`. This way we save users from adding both
   `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many API
-/
def more' := 0
