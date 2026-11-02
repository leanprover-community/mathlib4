module

import Mathlib.Tactic.Linter.LongUncommentedProof
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.Lemma

set_option linter.unusedTactic false
set_option linter.style.longUncommentedProof true
set_option linter.style.longUncommentedProof.minLines 4
set_option linter.style.longUncommentedProof.minComments 2

-- The line `lemma long : True := by` belongs to the statement.
-- A trailing comment on the last line of the body counts.
/--
warning: This declaration body has 4 lines of code, but too few comments (commented lines: 1, expected at least 2). Consider explaining the argument in comments or splitting off auxiliary lemmas.

Note: This linter can be disabled with `set_option linter.style.longUncommentedProof false`
-/
#guard_msgs in
lemma long : True := by
  skip
  skip
  skip
  exact trivial -- A trailing comment counts as a comment, and its line as code.
-- A comment after the declaration does not belong to its body.

-- Lines consisting only of comments and blank lines are not code.
set_option linter.style.longUncommentedProof.minComments 10 in
#guard_msgs in
example : True := by
  -- first comment
  skip
  /- a block comment
  spanning lines -/

  exact trivial

-- Two commented lines suffice.
#guard_msgs in
example : True := by
  -- first comment
  skip
  skip -- second comment
  exact trivial

-- Only the body is counted, not the statement.
#guard_msgs in
theorem longStatement
    (_ : True)
    (_ : True)
    (_ : True) : True :=
  trivial

-- Comment markers in string literals are code, not comments.
/--
warning: This declaration body has 4 lines of code, but too few comments (commented lines: 0, expected at least 2). Consider explaining the argument in comments or splitting off auxiliary lemmas.

Note: This linter can be disabled with `set_option linter.style.longUncommentedProof false`
-/
#guard_msgs in
def str : String :=
  "first line
-- not a comment
/- not a comment -/
last line"

-- Doc-comments count as comments, as do the comments following them.
#guard_msgs in
def withWhere : Nat :=
  aux₁ +
  aux₂
where
  /-- A doc-comment. -/
  -- A comment.
  aux₁ : Nat := 0
  aux₂ : Nat := 1

-- Bodies of all declarations in a `mutual` block are checked.
/--
warning: This declaration body has 4 lines of code, but too few comments (commented lines: 0, expected at least 2). Consider explaining the argument in comments or splitting off auxiliary lemmas.

Note: This linter can be disabled with `set_option linter.style.longUncommentedProof false`
---
warning: This declaration body has 4 lines of code, but too few comments (commented lines: 0, expected at least 2). Consider explaining the argument in comments or splitting off auxiliary lemmas.

Note: This linter can be disabled with `set_option linter.style.longUncommentedProof false`
-/
#guard_msgs in
mutual
def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | n + 1 => isEven n
end

-- Custom declaration commands are checked.
/--
warning: This declaration body has 4 lines of code, but too few comments (commented lines: 0, expected at least 2). Consider explaining the argument in comments or splitting off auxiliary lemmas.

Note: This linter can be disabled with `set_option linter.style.longUncommentedProof false`
-/
#guard_msgs in
irreducible_def irreducible : Nat :=
  1 +
  2 +
  3 +
  4

-- Declarations in quotations are not checked.
#guard_msgs in
macro "quotedDecl" : command => `(def quoted : Nat :=
  1 +
  2 +
  3 +
  4)

set_option linter.style.longUncommentedProof false in
#guard_msgs in
example : True := by
  skip
  skip
  skip
  exact trivial
