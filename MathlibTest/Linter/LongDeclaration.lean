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
#guard_msgs in
example : True := by
  skip
  exact True.intro

-- A named declaration whose entire range is exactly the limit can take the fast path.
#guard_msgs in
theorem shortProofAtLimit : True := by
  skip
  exact True.intro

-- A long declaration range is only an upper bound: its header is still excluded from the count.
#guard_msgs in
theorem shortProofWithLongHeader
    (α : Type)
    (_x : α)
    (h : True) :
    True := by
  exact h

/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
private theorem longPrivateProofTest : True := by
  skip
  skip
  exact True.intro

/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
theorem longDeclarationTest : True := by
  skip
  skip
  exact True.intro

/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
lemma longLemmaTest : True := by
  skip
  skip
  exact True.intro

-- Term proofs are checked too; UTF-8 before the proof must not affect the positions.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example (_α : Type) : True :=
  id (
    id (
      id (
        True.intro)))

-- The declaration header does not contribute to the proof length.
#guard_msgs in
example
    (α : Type)
    (_x : α)
    (h : True) :
    True := by
  exact h

-- Data-returning declaration bodies are checked too.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : Nat := by
  skip
  skip
  exact 1

-- Proofs with local proposition parameters are checked without type information.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example (P : Prop) (h : P) : P := by
  skip
  skip
  exact h

-- Only the enclosing declaration body is reported, even when it contains a long subproof.
/--
warning: This declaration body contains 6 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

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
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longEmbeddedProofTest : {n : Nat // n = 0} := ⟨0, by
  skip
  skip
  rfl⟩

-- Comment-only lines do not count, but blank lines outside comments still count.
#guard_msgs in
example : True := by
  -- This comment is free.

  exact True.intro

-- Nested block comments, including blank lines inside them, do not count.
#guard_msgs in
example : True := by
  /- Outer comment

     /- Nested comment -/
     -- These are still block-comment contents.
  -/
  skip
  exact True.intro

-- Code before or after a block comment still counts, as do lines with trailing comments.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by -- A trailing comment.
  skip /- A block comment starting after code.
    This line does not count.
-/skip
  exact True.intro

-- A blank line between separate comments still counts.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  -- First comment.

  -- Second comment.
  skip
  exact True.intro

-- Comment markers in strings and quoted identifiers are code.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  let «/- identifier -/» := "-- /- string -/"
  skip
  exact True.intro

#guard_msgs in
example : True := by
  exact True.intro
-- Trailing comments do not count.
-- Nor do blank lines after the last token.

-- Command-local overrides must be respected.
#guard_msgs in
set_option linter.longDeclaration false in
example : True := by
  skip
  skip
  exact True.intro

#guard_msgs in
set_option linter.longDeclaration.maxLines 4 in
example : True := by
  skip
  skip
  exact True.intro

/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  skip
  skip
  exact True.intro

-- Documentation comments in term proofs are excluded too.
#guard_msgs in
example : True :=
  let rec
    /-- A local definition.
        Its documentation is not proof code.
    -/
    x : Nat := 0
  True.intro

-- A line-comment marker cannot start a block comment.
#guard_msgs in
example : True := by
  -- /- This does not open a block comment.

  exact True.intro

-- A closing block-comment marker can overlap a pair of hyphens.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  /- A block comment ending with an extra hyphen. --/

  skip
  exact True.intro

-- Lines of a multiline string remain code, even when they look like comments.
/--
warning: This declaration body contains 5 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
example : True := by
  let _ := "first line
-- This is string content.
/- This is also string content. -/"
  exact True.intro

-- Term-style definitions returning data are checked.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

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
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
abbrev longAbbrevTest : Nat := by
  skip
  skip
  exact 0

-- Opaque declarations with bodies are checked.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
opaque longOpaqueTest : Nat := by
  skip
  skip
  exact 0

-- Structure-style instance bodies start at `where`.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
instance longInstanceTest : Inhabited Nat where
  default :=
    id (
      id 0)

-- Equation-style bodies include the patterns, but exclude the declaration signature.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longEquationTest : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => n

-- Attached helper declarations count toward the enclosing body.
/--
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

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
warning: This declaration body contains 4 non-comment lines, exceeding the limit of 3. Consider extracting helper definitions or lemmas.

Note: This linter can be disabled with `set_option linter.longDeclaration false`
-/
#guard_msgs in
def longTerminationTest (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => longTerminationTest n
termination_by n

-- A body at the boundary remains short, even when its signature occupies many lines.
#guard_msgs in
def shortEquationTest
    (_α : Type)
    (_x : _α) :
    Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => n

-- Opaque declarations without values and axioms have no body to check.
#guard_msgs in
opaque bodylessOpaqueTest : Nat

#guard_msgs in
axiom bodylessAxiomTest : True

-- Declarations quoted inside a term are data, not independently linted declarations.
#guard_msgs in
run_elab do
  let _ ← `(command| def quotedLongDeclaration : Nat := by
    skip
    skip
    exact 0)
  pure ()
