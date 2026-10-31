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

-- A named declaration whose entire range is exactly the limit can take the fast path.
theorem shortProofAtLimit : True := by
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

/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
private theorem longPrivateProofTest : True := by
  skip
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

/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
lemma longLemmaTest : True := by
  skip
  skip
  exact True.intro

-- Term proofs are checked too; UTF-8 before the proof must not affect the positions.
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

-- Proofs with local proposition parameters are checked without type information.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example (P : Prop) (h : P) : P := by
  skip
  skip
  exact h

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

-- An embedded proof contributes to the enclosing definition body.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longEmbeddedProofTest : {n : Nat // n = 0} := ⟨0, by
  skip
  skip
  rfl⟩

-- Blank lines and comment-only lines do not count.
example : True := by
  -- This comment is free.

  skip

  exact True.intro

-- Nested block comments, including blank lines inside them, do not count.
example : True := by
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

-- A blank line between separate comments does not count.
example : True := by
  -- First comment.

  -- Second comment.
  skip
  exact True.intro

-- Comment markers in strings and quoted identifiers are code.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  let «/- identifier -/» := "-- /- string -/"
  skip
  exact True.intro

example : True := by
  exact True.intro
-- Trailing comments do not count.
-- Nor do blank lines after the last token.

-- Command-local overrides must be respected.
set_option linter.longDeclaration false in
example : True := by
  skip
  skip
  exact True.intro

set_option linter.longDeclaration.maxLines 4 in
example : True := by
  skip
  skip
  exact True.intro

/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  skip
  skip
  exact True.intro

-- Documentation comments in term proofs are excluded too.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True :=
  let rec
    /-- A local definition.
        Its documentation is not proof code.
    -/
    x : Nat := 0
  True.intro

-- A line-comment marker cannot start a block comment.
example : True := by
  -- /- This does not open a block comment.

  exact True.intro

-- A closing block-comment marker can overlap a pair of hyphens.
example : True := by
  /- A block comment ending with an extra hyphen. --/

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

-- Blank lines inside multiline tokens still count.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  let _ := "first line

last line"
  exact True.intro

-- Term-style definitions returning data are checked.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longDataTermTest : Nat :=
  id (
    id (
      id (
        0)))

-- Abbreviations are checked.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
abbrev longAbbrevTest : Nat := by
  skip
  skip
  exact 0

-- Opaque declarations with bodies are checked.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
opaque longOpaqueTest : Nat := by
  skip
  skip
  exact 0

-- Structure-style instances are checked.
/--
warning: This command contains 4 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
instance longInstanceTest : Inhabited Nat where
  default :=
    id (
      id 0)

-- Equation-style definitions include the signature and patterns.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longEquationTest : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => n

-- Attached helper declarations count toward the enclosing declaration.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longWhereTest : Nat :=
  helper
where
  helper : Nat :=
    0

-- Termination hints are part of the declaration body.
/--
warning: This command contains 5 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longTerminationTest (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => longTerminationTest n
termination_by n

-- Equation-style declarations include their signatures and patterns.
/--
warning: This command contains 7 lines of code, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def shortEquationTest
    (_α : Type)
    (_x : _α) :
    Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => n

-- Short opaque declarations without values and axioms are permitted.
opaque bodylessOpaqueTest : Nat

axiom bodylessAxiomTest : True

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
