/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import Mathlib.Tactic.Linter.LongDeclaration
import Lean.Elab.GuardMsgs
import Mathlib.Tactic.Lemma

/-! # Regression tests for the long-declaration linter -/

set_option linter.longDeclaration true

-- Use a small bound to keep the boundary tests readable.
set_option linter.longDeclaration.maxLines 3

-- Exactly the limit is permitted.
example : True := by
  skip
  exact True.intro

/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
theorem longDeclarationTest : True := by
  skip
  skip
  exact True.intro

-- Explicit hypotheses contribute to the declaration length.
/--
warning: This command contains 6 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
theorem shortProofWithLongHeader
    (α : Type)
    (_x : α)
    (h : True) :
    True := by
  exact h

-- Term proofs are checked too.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example (_α : Type) : True :=
  id (
    id (
      id (
        True.intro)))

-- Anonymous declarations include their headers too.
/--
warning: This command contains 6 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example
    (α : Type)
    (_x : α)
    (h : True) :
    True := by
  exact h

-- Hypotheses declared separately do not contribute to the declaration length.
section
variable (α : Type)
    (_x : α)
    (h : True)

include h

theorem shortProofWithSectionVariables : True := by
  exact h

-- but the `variable` command itself may trigger the linter.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
variable (α : Type)
    (_x : α)
    (_y : α)
    (_z : α)
    (h : True)

end

-- A declaration's documentation does not count toward its length.
/-- A documented theorem.
Its documentation spans several lines.
These lines do not count as code.
-/
theorem documentedShortProof : True := by
  skip
  exact True.intro

-- Data-returning declaration bodies are checked too.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : Nat := by
  skip
  skip
  exact 1

-- Only the enclosing declaration body is reported, even when it contains a long subproof.
/--
warning: This command contains 6 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  have h : True := by
    skip
    skip
    exact True.intro
  exact h

-- Blank lines and comment-only lines do not count.
example : True := by
  -- This comment is free.
  /- Outer comment

      /- Nested comment -/
      -- These are still block-comment contents.
    -/
  skip

  exact True.intro

-- Code before or after a block comment still counts, as do lines with trailing comments.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by -- A trailing comment.
  skip /- A block comment starting after code.
    This line does not count.
-/skip
  exact True.intro

-- Command-local overrides must be respected.
set_option linter.longDeclaration false in
example : True := by
  skip
  skip
  exact True.intro

-- Lines of a multiline string remain code, even when they look like comments.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  let _ := "first line
-- This is string content.
/- This is also string content. -/"
  exact True.intro

-- Non-declaration commands are checked too, including any quoted syntax they contain.
/--
warning: This command contains 6 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
run_elab do
  let _ ← `(command| def quotedLongDeclaration : Nat := by
    skip
    skip
    exact 0)
  pure ()
